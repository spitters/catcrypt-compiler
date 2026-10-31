/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
public import CatCrypt.Crypto.SecureCompilation.Haxc.ExportContract

/-!
# Ascent of given bytes to a region program by recompilation and validation

Given bytes, an untrusted proposer supplies a candidate: a region program `p` over the
Jasmin dialect, a printed body `body` and an allocation certificate `cert`. The check
`decompileB` accepts the candidate when `p` is region-exportable and has no `call`, the
export `exportR` of `p` passes the gate `regionCoB` and the constant-time check `regionCtB`
against `body` at `cert`, and `body` encodes to the given bytes. These are the checks
`compileRegion` applies to the body its allocator prints; here the body is read off the
bytes, not produced by the compiler.

## Main results

* `decompileB_spec`: the conjuncts of an accepted candidate.
* `decompile_correct`: the bytes of an accepted candidate decode to a program that halts on
  the machine with the source value of `p` read back, the stack register restored and
  memory unchanged outside the frame and the pointer regions.
* `decompile_ct`: the decodings of the bytes of an accepted candidate are constant time
  between entry states related by `RegionBytePub`, when `p` is constant time at the source
  events.
* `decompileB_of_compileRegion`: the result of `compileRegion` on a program without `call`
  is accepted at that program after the region legalisation `legalizeRegion` (the identity
  on a program without `rorImm` and without and-not), with the printed body and certificate
  of the compiler.
* `regionPre_bytes_ct_of_decompileB`, `calleeSpec_of_decompileB`: the decoded block of the
  bytes of an accepted candidate is constant time at `regionPre σ c.p`, and it meets
  `regionSig σ c.p` when it passes the keep check at a store policy.
* `inWin_wordsLocs`, `ofRegion_footOut`: an out window within the words of the result
  region, and the footprint of a policy whose windows lie in the out result, among the frame
  and the result locations outside the return word.
* `ofRegion_meets_of_calleeSpec`: the contract of a region linked function from the
  specification of its code, at a store policy whose footprint lies there.
* `read_entryRegs_of_sub`: the read-back of the result from the entry registers, when the
  registers it reads at entry are among `abiRegs σ`.
* `linkedFn_meets_of_decompile`: the linked function `LinkedFn.ofRegion` at `c.p` and the
  bytes of an accepted candidate meets its contract.
* `regionPre_eq_of_denote`, `regionPost_eq_of_denote`: programs with the same values at
  every valuation have the same precondition and postcondition.
* `meets_of_decompile_equiv`: the linked function at a program `p'` with the values of
  `c.p` and the bytes of an accepted candidate meets its contract.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
  (encodeLfundefBytes encodeLfundefBytesChecked encodeLfundefBytesChecked_eq)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (entryA)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (RunSafe)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (runA)
open CatCrypt.Crypto.SecureCompilation.SepLogic.Addr (AccessIn)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck

/-- A candidate for the ascent of given bytes: a region program with one result, a printed
    body and an allocation certificate. -/
structure DecompCand (Γ : Ctxt jasminDialect) (t : JasminTy) where
  /-- The region program. -/
  p : NFProg jasminDialect Γ [t]
  /-- The printed body the bytes are read as. -/
  body : Lcmd
  /-- The allocation certificate of the gate. -/
  cert : List (String × String)

/-- **The check of a candidate against bytes** at the layout `σ` and the function name
    `fn`: `p` is region-exportable and has no `call`, its export passes `regionCoB` and
    `regionCtB` against `body` at `cert`, and `body` encodes to `bytes`. -/
def decompileB (σ : AbiLayout) (fn : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : DecompCand Γ t) (bytes : List (BitVec 8)) : Bool :=
  regionExportableB c.p && c.p.callFree
    && (match exportR Γ.length fn c.p Γ.length 0 with
      | some r => regionCoB σ exportReg c.body t r.code r.res c.cert
          && regionCtB σ exportReg c.body t r.code r.res c.cert
      | none => false)
    && decide (encodeLfundefBytesChecked c.body = some bytes)

variable {σ : AbiLayout} {fn : String} {Γ : Ctxt jasminDialect} {t : JasminTy}

/-- The conjuncts of an accepted candidate. -/
theorem decompileB_spec {c : DecompCand Γ t} {bytes : List (BitVec 8)}
    (h : decompileB σ fn c bytes = true) :
    regionExportableB c.p = true ∧ c.p.callFree = true
      ∧ ∃ r, exportR Γ.length fn c.p Γ.length 0 = some r
        ∧ regionCoB σ exportReg c.body t r.code r.res c.cert = true
        ∧ regionCtB σ exportReg c.body t r.code r.res c.cert = true
        ∧ encodeLfundefBytesChecked c.body = some bytes := by
  unfold decompileB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hB, hcf⟩, hm⟩, hbs⟩ := h
  split at hm
  · rename_i r hr
    rw [Bool.and_eq_true] at hm
    exact ⟨hB, hcf, r, hr, hm.1, hm.2, hbs⟩
  · cases hm

/-- **Correctness of the bytes of an accepted candidate.** From every entry state `sa`
    satisfying `σ.Regions`, at every valuation `V` that `σ` reads off `sa` at which `c.p`
    denotes `v` at some fuel, the bytes decode to a program that halts on the machine from
    `sa` in a state `sa'` from which `σ` reads back the source value of the result. The
    stack register of `sa'` holds its value in `sa`, and the memory of `sa'` agrees with that
    of `sa` outside the stack words of the frame and the words of each pointer region of
    `σ`; some run of the address machine on `c.body` from `entryA σ sa` halts and accesses
    `layoutMem σ sa` only. -/
theorem decompile_correct {c : DecompCand Γ t} {bytes : List (BitVec 8)}
    (h : decompileB σ fn c bytes = true)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : c.p.denote fuel V = some v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ ∃ frame fuel s zf, runA frame c.body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame c.body (AccessIn (layoutMem σ sa) frame c.body) fuel (entryA σ sa)
          false := by
  obtain ⟨hB, -, r, hr, hco, -, hbs⟩ := decompileB_spec h
  rw [encodeLfundefBytesChecked_eq hbs]
  exact regionCo_bytes (regionExportableB_sound hB) hr hco sa V hV hreg fuel hv

/-- **Constant time of the bytes of an accepted candidate.** If `c.p` is constant time at
    the source events for the labels `L` at the fuel `fuel`, on the valuations the layout
    reads off machine states that satisfy `σ.Regions` and `Pre`, then every decoding of the
    bytes is constant time under DOITM between entry states related by `RegionBytePub`. -/
theorem decompile_ct (Pj : JLeakParams) {c : DecompCand Γ t} {bytes : List (BitVec 8)}
    (h : decompileB σ fn c bytes = true) (fuel : Nat) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel c.p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel c.p V₂).map Prod.snd)
    (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog bytes = some prog) :
    ConstantTimeRel (RegionBytePub σ fuel c.p L Pre)
      (fun sa u => ∃ sa', RunL .doitm ok prog 0 sa u sa') := by
  obtain ⟨hB, hcf, r, hr, hco, hck, hbs⟩ := decompileB_spec h
  obtain ⟨hlk, hprW, hgW⟩ := regionCtB_spec hck
  rw [encodeLfundefBytesChecked_eq hbs] at hdec
  exact regionWide_bytes_ct Pj fn fuel (regionExportableB_sound hB) hcf hct hr hco hlk hprW
    hgW ok hdec

/-- **The compiler's output is accepted.** For a result `(P, bytes)` of `compileRegion σ a p`
    on a program without `call`, the candidate of `p` with the printed body and certificate
    of the compiler passes `decompileB` at the function name of `a`. -/
theorem decompileB_of_compileRegion {a : AbiNames} {p : NFProg jasminDialect Γ [t]}
    (hcf : p.callFree = true) {P : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion σ a p = some (P, bytes)) :
    ∃ body cert, decompileB σ a.fname ⟨legalizeRegion p, body, cert⟩ bytes = true := by
  obtain ⟨hB, r, b, cert, hr, hbs, hco, hck, -⟩ := compileRegion_spec h
  refine ⟨b, cert, ?_⟩
  simp only [decompileB, hB, legalizeRegion_callFree hcf, hr, hco, hck, hbs, Bool.and_self,
    decide_true]

/-! ## The bytes of an accepted candidate as a linked callee -/

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernel
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
  (meets_of_calleeSpec holds_entryAt entryAt_of_pre sem_isSome_of_pre entryRegs
    not_ret_of_resRegion)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (abiRegs Loc resLocs wordLocs)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (InRange8)

/-- **A window within the words of a region.** An address in the window of the
    displacements `lo, …, hi - 1` from `b`, with `0 ≤ lo` and `hi ≤ 8 n ≤ 2 ^ 64`, is a byte of
    one of the `n` words from `b`. -/
theorem inWin_wordsLocs {b x : BitVec 64} {lo hi : Int} {n : Nat} (h0 : 0 ≤ lo)
    (hhi : hi ≤ 8 * n) (hn : 8 * n ≤ 2 ^ 64) (h : InWin b lo hi x) :
    Loc.mem x ∈ wordsLocs (regionWords b n) := by
  obtain ⟨L, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  unfold InWin at h
  obtain ⟨t, ht⟩ : ∃ t, t = (x - (b + BitVec.ofInt 64 (L : Int))).toNat := ⟨_, rfl⟩
  rw [← ht] at h
  have hd : L + t < 8 * n := by omega
  refine Set.mem_iUnion₂.2 ⟨b + BitVec.ofNat 64 (8 * ((L + t) / 8)),
    ⟨(L + t) / 8, by omega, rfl⟩, x, ?_, rfl⟩
  change (x - (b + BitVec.ofNat 64 (8 * ((L + t) / 8)))).toNat < 8
  have hx : x = b + BitVec.ofNat 64 (L + t) := by
    have hL : BitVec.ofInt 64 (L : Int) = BitVec.ofNat 64 L := by simp
    rw [hL] at ht
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    bv_omega
  rw [hx]
  have hs : b + BitVec.ofNat 64 (L + t) - (b + BitVec.ofNat 64 (8 * ((L + t) / 8)))
      = BitVec.ofNat 64 ((L + t) % 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hs, BitVec.toNat_ofNat]
  omega

/-- **Constant time of the bytes of an accepted candidate at the region precondition.** Let
    `c` pass `decompileB` at the bytes `bytes`, decoding to the block `q`, with `c.p`
    constant time at the source events for labels `L` that agree with the public data of
    `σ`, at every fuel. Then the leaky runs of `q` under `ctRegime` from entry states that
    agree on the public data of `σ` and satisfy `regionPre σ c.p` have equal traces. -/
theorem regionPre_bytes_ct_of_decompileB {c : DecompCand Γ t} {bytes : List (BitVec 8)}
    (h : decompileB σ fn c bytes = true) (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel c.p) (hL : PubLabelsOK σ L)
    {q : List RInstr} (hq : decodeLprog bytes = some q) :
    ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ regionPre σ c.p s₁ ∧ regionPre σ c.p s₂)
      (fun s tr => ∃ s', RunL ctRegime (fun _ _ => True) q 0 s tr s') := by
  obtain ⟨hB, hcf, r, hr, hco, hck, hb⟩ := decompileB_spec h
  obtain ⟨hlk, hprW, hgW⟩ := regionCtB_spec hck
  rw [encodeLfundefBytesChecked_eq hb] at hq
  rintro sa₁ sa₂ u₁ u₂ ⟨hag, ⟨h₁, V₁, fuel, v₁, hV₁, hv₁⟩, ⟨h₂, V₂, -, -, hV₂, -⟩⟩ hb₁ hb₂
  exact regionWide_bytes_ct JLeakParams.owned fn fuel (regionExportableB_sound hB) hcf
    (nfCT_restrict _ σ (fun _ => True) (hsrc fuel)) hr hco hlk hprW hgW (fun _ _ => True) hq
    sa₁ sa₂ u₁ u₂
    ⟨V₁, V₂, pubEqV_of_pubAgree hL hag hV₁ hV₂, hV₁, hV₂, h₁, h₂, trivial, trivial, hag.1,
      fun x hx n hn => hag.2 x hx (by simp [AbiLayout.argPub, hn]),
      show (c.p.denote fuel V₁).isSome = true by rw [hv₁]; rfl⟩
    hb₁ hb₂

/-- **The specification of the bytes of an accepted candidate.** Let `c` pass `decompileB`
    at the bytes `bytes`, decoding to the block `q` that passes `keepCheckWB` at the clobber
    set `clob`, the frame of `F` bytes and the store policy `K`, with `c.p` constant time at
    the source events for labels `L` that agree with the public data of `σ`, at every fuel.
    Then the leaky run of `q` under `ctRegime` meets `regionSig σ c.p args res clob F K`. -/
theorem calleeSpec_of_decompileB {c : DecompCand Γ t} {bytes : List (BitVec 8)}
    (h : decompileB σ fn c bytes = true) {q : List RInstr}
    (hq : decodeLprog bytes = some q) {args : List String} {res : Option String}
    {clob : String → Bool} {F : Nat} {K : StorePol} (hk : keepCheckWB q clob F K = true)
    (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel c.p) (hL : PubLabelsOK σ L) :
    CalleeSpec (runOf ctRegime q) (regionSig σ c.p args res clob F K) :=
  calleeSpec_of_keepCheckW (c := regionSig σ c.p args res clob F K) (P := K) hk
    (fun _ _ hx => hx)
    (fun s ⟨hreg, V, fuel, v, hV, hv⟩ => by
      obtain ⟨prog, s', hd, hh, hR, -⟩ := decompile_correct h s V hV hreg fuel hv
      rw [hq, Option.some.injEq] at hd
      subst hd
      exact ⟨s', hh, V, fuel, v, hV, hv, hR⟩)
    (regionPre_bytes_ct_of_decompileB h L hsrc hL hq)

/-- **The contract of a region linked function from the specification of its code.** Let the
    bytes `bytes` of `LinkedFn.ofRegion` at the program `p` decode to the block `q`, whose
    leaky run under `ctRegime` meets `regionSig σ p` at the clobbered registers, the frame
    size and the store policy `K` of the record. Let the footprint `KeepFoot K F` at an entry
    state satisfying the precondition of the contract lie in the `F + K.red` bytes below the
    entry stack register (the frame and the red zone, among the `l.frame` bytes of the
    record) or in the result locations outside the return word (`hK`; at
    `K := .frame` by `keepFoot_frame`, for out windows by `ofRegion_footOut`). Let the
    read-back of the result of `σ` depend on the entry state only at the registers of
    `abiRegs σ`, and let `regionPre σ p` hold wherever the precondition of the contract does.
    Then the record meets its contract. -/
theorem ofRegion_meets_of_calleeSpec {name : String}
    {params : List (String × NFDialect.NfTy)} {res : NFDialect.NfTy}
    {sem : List _root_.Hax.Value → Option _root_.Hax.Value}
    {sem_res : ∀ vals v, sem vals = some v →
      (CatCrypt.Crypto.Hax.ImpToNF.dec res v).isSome = true}
    {p : NFProg jasminDialect Γ [t]} {clob : List String} {F : Nat}
    {bytes : List (BitVec 8)}
    {hsem : ∀ sa sa' v, regionPre σ p sa → regionPost σ p sa sa' →
      sem (σ.args.map (·.read sa)) = some v → σ.ResultOf sa sa' v} {h0 : σ.pubWords = []}
    {K : StorePol} {q : List RInstr} (hq : decodeLprog bytes = some q) {args : List String}
    {cres : Option String}
    (hX : CalleeSpec (runOf ctRegime q)
      (regionSig σ p args cres (fun x => clob.contains x) F K))
    (hres : ∀ (s s' : AState) (rv : String → BitVec 64), (∀ r ∈ abiRegs σ, s.regs r = rv r) →
      σ.result.read s s' = σ.result.read (entryRegs rv) s')
    (hpre : ∀ a s, ((CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ p
      clob F bytes hsem h0 K).contractPre a).holds s → regionPre σ p s)
    (hK : ∀ a s x, ((CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ p
      clob F bytes hsem h0 K).contractPre a).holds s → KeepFoot K F s.regs x →
        InFrame (s.regs "%rsp") (F + K.red) x ∨
          (Loc.mem x ∈ resLocs (entryRegs a.rv) σ.result ∧ ¬ InRange8 a.sp x)
      := by exact fun _ _ _ _ hx => Or.inl (keepFoot_frame.1 hx)) :
    (CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ p clob F bytes
      hsem h0 K).Meets := by
  refine meets_of_calleeSpec hq hX hpre (fun r hr => show r ∈ clob by simpa [regionSig] using hr)
    (fun a s x hs hx => (hK a s x hs hx).imp_left (inFrame_of_le (le_max_left _ _)))
    (fun a s s' hs hp => ?_) (fun _ _ hp => AbiLayout.PubAgree.of_pubWords_nil h0 hp.1 hp.2)
  obtain ⟨hregs, -, hvals, -, -⟩ := holds_entryAt (entryAt_of_pre hs)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (sem_isSome_of_pre hs)
  have hR := hsem s s' v (hpre a s hs) hp
    (by rw [show σ.args.map (·.read s) = a.vals from hvals]; exact hv)
  refine ⟨v, hv, ?_⟩
  unfold AbiLayout.ResultOf at hR ⊢
  rw [hR, hres s s' a.rv hregs]
  rfl

/-- **The read-back of the result from the entry registers.** If the registers the read-back
    of the result of `σ` reads at entry are among `abiRegs σ`, then at an entry state whose
    registers of `abiRegs σ` hold their values under `rv` the read-back equals the read-back
    from `entryRegs rv` (`read_entry_congr`). -/
theorem read_entryRegs_of_sub (hsub : ∀ r ∈ resultRegs σ.result, r ∈ abiRegs σ)
    (s s' : AState) (rv : String → BitVec 64) (h : ∀ r ∈ abiRegs σ, s.regs r = rv r) :
    σ.result.read s s' = σ.result.read (entryRegs rv) s' :=
  read_entry_congr σ.result fun r hr => h r (hsub r hr)

/-- **The footprint of an out-window policy.** Let the result of `σ` be the `n` words at the
    register `r`, a pointer region of `σ`, with `8 n ≤ 2 ^ 64`, and let the store policy `K`
    have only windows from `r` within the bytes `0, …, 8 n - 1`. Then at an entry state
    satisfying the precondition of the contract of `LinkedFn.ofRegion`, the footprint
    `KeepFoot K F` lies in the `F + K.red` bytes below the stack register or in
    the result locations outside the return word: the hypothesis `hK` of
    `ofRegion_meets_of_calleeSpec`. -/
theorem ofRegion_footOut {name : String}
    {params : List (String × NFDialect.NfTy)} {res : NFDialect.NfTy}
    {sem : List _root_.Hax.Value → Option _root_.Hax.Value}
    {sem_res : ∀ vals v, sem vals = some v →
      (CatCrypt.Crypto.Hax.ImpToNF.dec res v).isSome = true}
    {p : NFProg jasminDialect Γ [t]} {clob : List String} {F : Nat}
    {bytes : List (BitVec 8)}
    {hsem : ∀ sa sa' v, regionPre σ p sa → regionPost σ p sa sa' →
      sem (σ.args.map (·.read sa)) = some v → σ.ResultOf sa sa' v} {h0 : σ.pubWords = []}
    {K : StorePol} {r : String} {n : Nat} (hres : σ.result = .words r n)
    (hreg : (r, n) ∈ σ.regions) (hn : 8 * n ≤ 2 ^ 64)
    (hwin : ∀ w ∈ K.wins, w.1 = r ∧ 0 ≤ w.2.1 ∧ w.2.2 ≤ 8 * n) :
    ∀ a s x, ((CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ p
      clob F bytes hsem h0 K).contractPre a).holds s → KeepFoot K F s.regs x →
        InFrame (s.regs "%rsp") (F + K.red) x ∨
          (Loc.mem x ∈ resLocs (entryRegs a.rv) σ.result ∧ ¬ InRange8 a.sp x) := by
  intro a s x hs hx
  obtain ⟨hregs, -, -, -, -⟩ := holds_entryAt (entryAt_of_pre hs)
  rcases hx with hf | ⟨w, hw, hin⟩
  · exact Or.inl hf
  · right
    obtain ⟨hw1, hlo, hhi⟩ := hwin w hw
    have hrA : r ∈ abiRegs σ := by
      obtain ⟨a', ha', hr'⟩ := List.mem_filterMap.1 hreg
      unfold AbiArg.region at hr'
      split at hr' <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hr'
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (hr'.1 ▸ List.mem_map_of_mem ha'))
    have hmem : Loc.mem x ∈ resLocs (entryRegs a.rv) σ.result := by
      rw [hres]
      change Loc.mem x ∈ wordsLocs (regionWords (a.rv r) n)
      rw [← hregs r hrA, ← hw1]
      exact inWin_wordsLocs hlo hhi hn hin
    exact ⟨hmem, not_ret_of_resRegion (entryAt_of_pre hs) hres hreg hmem⟩

/-- **The linked function of the bytes of an accepted candidate meets its contract.** Let
    `c` pass `decompileB` at the bytes `bytes` of `LinkedFn.ofRegion` at `c.p`, decoding to
    the block `q` that passes `keepCheckWB` at the clobbered registers, the frame size and
    the store policy `K` of the record, with `c.p` constant time at the source events for
    labels `L` that agree with the public data of `σ`, at every fuel, and let the footprint
    of `K` satisfy `hK` of `ofRegion_meets_of_calleeSpec`. Let the registers the read-back of
    the result of `σ` reads at entry be among `abiRegs σ`, and let `regionPre σ c.p` hold
    wherever the precondition of the contract does. Then the record meets its contract. -/
theorem linkedFn_meets_of_decompile {name : String}
    {params : List (String × NFDialect.NfTy)} {res : NFDialect.NfTy}
    {sem : List _root_.Hax.Value → Option _root_.Hax.Value}
    {sem_res : ∀ vals v, sem vals = some v →
      (CatCrypt.Crypto.Hax.ImpToNF.dec res v).isSome = true}
    {c : DecompCand Γ t} {clob : List String} {F : Nat} {bytes : List (BitVec 8)}
    {hsem : ∀ sa sa' v, regionPre σ c.p sa → regionPost σ c.p sa sa' →
      sem (σ.args.map (·.read sa)) = some v → σ.ResultOf sa sa' v} {h0 : σ.pubWords = []}
    {K : StorePol} (h : decompileB σ fn c bytes = true) {q : List RInstr}
    (hq : decodeLprog bytes = some q)
    (hk : keepCheckWB q (fun x => clob.contains x) F K = true) (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel c.p) (hL : PubLabelsOK σ L)
    (hsub : ∀ r ∈ resultRegs σ.result, r ∈ abiRegs σ)
    (hpre : ∀ a s, ((CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ c.p
      clob F bytes hsem h0 K).contractPre a).holds s → regionPre σ c.p s)
    (hK : ∀ a s x, ((CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ c.p
      clob F bytes hsem h0 K).contractPre a).holds s → KeepFoot K F s.regs x →
        InFrame (s.regs "%rsp") (F + K.red) x ∨
          (Loc.mem x ∈ resLocs (entryRegs a.rv) σ.result ∧ ¬ InRange8 a.sp x)
      := by exact fun _ _ _ _ hx => Or.inl (keepFoot_frame.1 hx)) :
    (CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ c.p clob F bytes
      hsem h0 K).Meets :=
  ofRegion_meets_of_calleeSpec hq
    (calleeSpec_of_decompileB (args := []) (res := none) h hq hk L hsrc hL)
    (read_entryRegs_of_sub hsub) hpre hK

/-- **The region precondition depends on the values of the program only.** Two programs
    with the same values at every valuation, at some fuel, have the same precondition. -/
theorem regionPre_eq_of_denote {p p' : NFProg jasminDialect Γ [t]}
    (hd : ∀ (V : Ctxt.Valuation Γ) (v : Ctxt.Valuation (d := jasminDialect) [t]),
      (∃ fuel, p.denote fuel V = some v) ↔ (∃ fuel, p'.denote fuel V = some v)) :
    regionPre σ p = regionPre σ p' := by
  funext s
  apply propext
  constructor
  · rintro ⟨hr, V, fuel, v, hV, hv⟩
    obtain ⟨fuel', hv'⟩ := (hd V v).1 ⟨fuel, hv⟩
    exact ⟨hr, V, fuel', v, hV, hv'⟩
  · rintro ⟨hr, V, fuel, v, hV, hv⟩
    obtain ⟨fuel', hv'⟩ := (hd V v).2 ⟨fuel, hv⟩
    exact ⟨hr, V, fuel', v, hV, hv'⟩

/-- **The region postcondition depends on the values of the program only.** Two programs
    with the same values at every valuation, at some fuel, have the same postcondition. -/
theorem regionPost_eq_of_denote {p p' : NFProg jasminDialect Γ [t]}
    (hd : ∀ (V : Ctxt.Valuation Γ) (v : Ctxt.Valuation (d := jasminDialect) [t]),
      (∃ fuel, p.denote fuel V = some v) ↔ (∃ fuel, p'.denote fuel V = some v)) :
    regionPost σ p = regionPost σ p' := by
  funext s s'
  apply propext
  constructor
  · rintro ⟨V, fuel, v, hV, hv, hR⟩
    obtain ⟨fuel', hv'⟩ := (hd V v).1 ⟨fuel, hv⟩
    exact ⟨V, fuel', v, hV, hv', hR⟩
  · rintro ⟨V, fuel, v, hV, hv, hR⟩
    obtain ⟨fuel', hv'⟩ := (hd V v).2 ⟨fuel, hv⟩
    exact ⟨V, fuel', v, hV, hv', hR⟩

/-- **The linked function at a program with the values of an accepted candidate meets its
    contract.** Let `c` pass `decompileB` at the bytes `bytes`, decoding to the block `q`
    that passes `keepCheckWB` at the clobbered registers, the frame size and the store
    policy `K`, whose footprint satisfies `hK` of `ofRegion_meets_of_calleeSpec`, with `c.p`
    constant time at the source events for labels `L` that agree with the public data of
    `σ`, at every fuel, and let the program `p'` have the values of `c.p` at every valuation.
    Let the registers the read-back of the result of `σ` reads at entry be among
    `abiRegs σ`, and let `regionPre σ p'` hold wherever the precondition of the contract
    does. Then `LinkedFn.ofRegion` at `p'` and `bytes` meets its contract. -/
theorem meets_of_decompile_equiv {name : String}
    {params : List (String × NFDialect.NfTy)} {res : NFDialect.NfTy}
    {sem : List _root_.Hax.Value → Option _root_.Hax.Value}
    {sem_res : ∀ vals v, sem vals = some v →
      (CatCrypt.Crypto.Hax.ImpToNF.dec res v).isSome = true}
    {c : DecompCand Γ t} {p' : NFProg jasminDialect Γ [t]} {clob : List String} {F : Nat}
    {bytes : List (BitVec 8)}
    {hsem : ∀ sa sa' v, regionPre σ p' sa → regionPost σ p' sa sa' →
      sem (σ.args.map (·.read sa)) = some v → σ.ResultOf sa sa' v} {h0 : σ.pubWords = []}
    (h : decompileB σ fn c bytes = true)
    (hd : ∀ (V : Ctxt.Valuation Γ) (v : Ctxt.Valuation (d := jasminDialect) [t]),
      (∃ fuel, c.p.denote fuel V = some v) ↔ (∃ fuel, p'.denote fuel V = some v))
    {K : StorePol} {q : List RInstr} (hq : decodeLprog bytes = some q)
    (hk : keepCheckWB q (fun x => clob.contains x) F K = true) (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel c.p) (hL : PubLabelsOK σ L)
    (hsub : ∀ r ∈ resultRegs σ.result, r ∈ abiRegs σ)
    (hpre : ∀ a s, ((CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ p'
      clob F bytes hsem h0 K).contractPre a).holds s → regionPre σ p' s)
    (hK : ∀ a s x, ((CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ p'
      clob F bytes hsem h0 K).contractPre a).holds s → KeepFoot K F s.regs x →
        InFrame (s.regs "%rsp") (F + K.red) x ∨
          (Loc.mem x ∈ resLocs (entryRegs a.rv) σ.result ∧ ¬ InRange8 a.sp x)
      := by exact fun _ _ _ _ hx => Or.inl (keepFoot_frame.1 hx)) :
    (CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ p' clob F bytes
      hsem h0 K).Meets := by
  have hX := calleeSpec_of_decompileB (args := []) (res := none) h hq hk L hsrc hL
  have hS : regionSig σ c.p [] none (fun x => clob.contains x) F K
      = regionSig σ p' [] none (fun x => clob.contains x) F K := by
    unfold regionSig
    rw [regionPre_eq_of_denote hd, regionPost_eq_of_denote hd]
  rw [hS] at hX
  exact ofRegion_meets_of_calleeSpec hq hX (read_entryRegs_of_sub hsub) hpre hK

end CatCrypt.Crypto.SecureCompilation.Haxc
