/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCopyCoalesce
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCmovTestElim
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.CombSelectBytes

/-!
# Ed25519 comb select through the front in conditional-move form

The `N`-entry comb select of `CombSelectFront`, stated with the `LowCT`
conditional-select constructor `RSelect` in place of the arithmetic equality
mask: per entry `e` the source binds `q := d ⊕ e`, which is zero exactly when
`d = e`, and for each limb `k` loads table cell `4·e + k` into `l` and writes
`s_k := if q = 0 then l else s_k`.

The `RSelect` arm of `TranslateDialectDirectArms.translateDialectFull` on
64-bit words emits the comparison select `selectCmpCont` (`z := 0`,
`b := (q == z)`, `s_k := b ? l : s_k`), and `DialectToJasminCom.toJExprD` maps
its `bvEq` to `JasminOp.cmp .eq 64` and its `ite` to `JasminOp.select 64`. The
exported body holds one `SETE:64` and one `CMOV:64` per select;
`LprogCmovTestElim.cmpFuseBody` replaces each such pair by `CMP:64` and a
two-address conditional move, and `LprogCmovTestElim.cmovTestElimBody` rewrites
any remaining `CMOV:64` into the printer's `test`/`cmovcc` forms.

## Main results

* `combSelectCmovSrc N`: the `N`-entry scan in `RSelect` form as `LowCT`.
* `combSelectCmovFront`, `combSelectCmovLowered`, `combSelectCmovLprog`: the
  front output, its `Com jasminDialect` lowering and the exported `Lprog`, by
  the composition of `CombSelectFront`.
* `cmovFuseLprog`: `cmpFuseFundef` on the result registers followed by
  `cmovTestElimFundef`, on every function of an `Lprog`.
* `combSelectCmovAsmN`: the owned AT&T rendering after
  `ConstIndexFold.constIndexFold`, the basic-block pipeline, two rounds of
  `LprogCopyCoalesce.coalesceRounds` and `cmovFuseLprog`.
* `selScanVal_eq`, `selScanVal_eq_scanVal`: after `n` entries running limb `k`
  holds `T[4·D + k]` when `D < n` and `0` otherwise, the state of the mask-form
  scan `CombSelectFront.scanVal` at the same entry boundary.
* `combSelectCmovSrc_run`, `combSelectCmovSrc_refines`: the source runs to
  `out[k] = T[4·D + k]` for `D < N` and `0` otherwise, the buffer
  `CombSelectFront.combSelectSrc` leaves.
* `combSelectCmovFront_denote`, `combSelectCmovFront_denote_eq`: the front
  output lowers to `Com jasminDialect` and denotes that buffer, the denotation
  of `CombSelectFront.combSelectFront`.
* `combSelectCmovLines`, `combSelectCmovClean`, `combSelectCmovHasCmov`: the
  line count of the rendering, the absence of an `UNHANDLED` sentinel, and the
  presence of a `cmov` mnemonic.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectCmovFront

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront
  (seqL accName setE selInit storeAll selCtx selVM)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr Located TowerType)

/-! ## 1. The source -/

/-- The selector of entry `e`: `q := d ⊕ e`, zero exactly when `d = e`. -/
def testCmd (e : Nat) : LowCT :=
  setE "q" (.SXor (.SVar "d") (.SLit e))

/-- Load table cell `4·e + k` from `tbl` (a `tw`-byte buffer) into `l` and
    select it into running limb `k` when `q = 0`. -/
def cellSelCmds (tw e : Nat) (k : Fin 4) : List LowCT :=
  [ setE "i" (.SLit (4 * e + k.val))
  , .RArrLoad ⟨"l", .TU64⟩ ⟨"tbl", .TBytes tw⟩ "i"
  , .RSelect ⟨accName k, .TU64⟩ "q" ⟨"l", .TU64⟩ ⟨accName k, .TU64⟩ ]

/-- One entry of the scan: its selector and the four conditional selects. -/
def entrySelCmds (tw e : Nat) : List LowCT :=
  testCmd e :: (cellSelCmds tw e 0 ++ (cellSelCmds tw e 1 ++ (cellSelCmds tw e 2 ++
    cellSelCmds tw e 3)))

/-- The scan over entries `0 … N−1`. -/
def scanSelCmds (tw : Nat) : Nat → List LowCT
  | 0 => []
  | N + 1 => scanSelCmds tw N ++ entrySelCmds tw N

/-- The constant-time `N`-entry comb select in conditional-select form, over the
    arguments `tbl` (`4N` little-endian words), `d` (the secret index) and `out`
    (four words): every entry is read on every call and selected into the
    running limbs under `d ⊕ e = 0`. -/
def combSelectCmovSrc (N : Nat) : LowCT :=
  seqL (selInit ++ (scanSelCmds (32 * N) N ++ storeAll))

/-! ## 2. The front, the lowering and the rendering -/

/-- The front output: `translateDialectControl` on the source, closed by
    returning `out`. -/
def combSelectCmovFront (N : Nat) : Option (Com catCryptDialect (selCtx N) (.memref 4)) :=
  match translateDialectControl (selVM N) (combSelectCmovSrc N) with
  | some r =>
      match r.vm.lookup "out" with
      | some ⟨.memref 4, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front output lowered to `Com jasminDialect`. -/
def combSelectCmovLowered (N : Nat) :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match combSelectCmovFront N with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

/-- The exported `Lprog` under `f(tbl = RDI, d = RSI, out = RDX)`, with the
    export arguments of `CombSelectFront.combSelectLprog`. -/
def combSelectCmovLprog (name : String) (N : Nat) : Option JasminLprogExport.Lprog :=
  (combSelectCmovLowered N).map (fun s =>
    JasminLprogExport.Com.toLprogPhysAbi s.2.2 name
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The exported `Lprog` after `ConstIndexFold.constIndexFold`,
    `ConstIndexFold.spellLprog`, the basic-block pipeline and two rounds of
    `LprogCopyCoalesce.coalesceRounds`, composed as in
    `LprogCopyCoalesce.combSelectCoalescedLprog`. -/
def combSelectCmovCoalescedLprog (name : String) (N : Nat) :
    Option JasminLprogExport.Lprog :=
  (combSelectCmovLprog name N).map (fun lp =>
    LprogCopyCoalesce.coalesceRounds 2 (LprogOptPipeline.optimizeLprogBasicBlocks
      (ConstIndexFold.spellLprog (ConstIndexFold.constIndexFold lp))))

/-- The comparison fusion followed by the shared-test rewrite on every function
    of an `Lprog`. The registers read after a body are its result registers
    `lfd_res`, the `liveOut` argument of `LprogCmovTestElim.cmpFuseFundef`. -/
def cmovFuseLprog (p : JasminLprogExport.Lprog) : JasminLprogExport.Lprog :=
  { p with lp_funcs := p.lp_funcs.map fun (n, f) =>
      (n, LprogCmovTestElim.cmovTestElimFundef
        (LprogCmovTestElim.cmpFuseFundef f.lfd_res f)) }

/-- `combSelectCmovCoalescedLprog` after `cmovFuseLprog`: the body the printer
    receives. -/
def combSelectCmovFusedLprog (name : String) (N : Nat) :
    Option JasminLprogExport.Lprog :=
  (combSelectCmovCoalescedLprog name N).map cmovFuseLprog

/-- The owned AT&T rendering of `combSelectCmovFusedLprog`. -/
def combSelectCmovAsmN (name : String) (N : Nat) : Option String :=
  (combSelectCmovFusedLprog name N).map (fun p => LprogAsmPrinter.renderLprogAtt p)

/-! ## 3. Evaluation predicates -/

/-- The line count of the rendered `N`-entry select. -/
def combSelectCmovLines (N : Nat) : Option Nat :=
  (combSelectCmovAsmN "ed25519_comb_select_cmov_x86_from_lean" N).map
    LprogCopyCoalesce.lineCount

/-- The rendered `N`-entry select exists and has no `UNHANDLED` sentinel. -/
def combSelectCmovClean (N : Nat) : Bool :=
  match combSelectCmovAsmN "ed25519_comb_select_cmov_x86_from_lean" N with
  | some t => !LprogCopyCoalesce.hasUnhandled t
  | none => false

/-- The rendered `N`-entry select contains a `cmov` mnemonic. -/
def combSelectCmovHasCmov (N : Nat) : Bool :=
  match combSelectCmovAsmN "ed25519_comb_select_cmov_x86_from_lean" N with
  | some t => (t.splitOn "cmov").length != 1
  | none => false

/-! ## 4. Waist semantics of the source

The scan invariant is `CombSelectFront.SelInv`. After the first `n` entries
running limb `k` holds `T[4·D + k]` when `D < n` and `0` otherwise
(`selScanVal_eq`), the state `CombSelectFront.scanVal_eq` gives for the
mask-form source at the same entry boundary. -/

open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront

/-- The selector block binds `q` to `D ⊕ e`. -/
theorem testCmd_run {N : Nat} {T : Fin (4 * N) → BitVec 64} {D : BitVec 64}
    {O a : Fin 4 → BitVec 64} {env : SEnvScalar}
    (h : SelInv N T D O a env) (e : Nat) (he : e < 2 ^ 64) :
    ∃ env', semScalar (testCmd e) env = some env' ∧ SelInv N T D O a env'
      ∧ env' "q" = some ⟨.sword 64, D ^^^ BitVec.ofNat 64 e⟩ := by
  have nd : ¬ isTmpName "d" := notTmp_of_head (by decide)
  obtain ⟨e1, s1, v1, f1⟩ := setE_run (x := "q") (e := .SXor (.SVar "d") (.SLit e))
    (env := env) ⟨nd, he⟩ (by simp [sexprVars, readU64_of h.d])
  refine ⟨e1, s1, h.frame f1 rfl, ?_⟩
  rw [v1]
  simp only [SExpr.evalBV, reader_of h.d]

theorem accName_ne_q (k : Fin 4) : accName k ≠ "q" := by
  match k with
  | 0 | 1 | 2 | 3 => decide

/-- One cell block selects table cell `4·e + k` into running limb `k` when the
    selector is zero, and keeps the selector. -/
theorem cellSelCmds_run {N : Nat} {T : Fin (4 * N) → BitVec 64} {D : BitVec 64}
    {O a : Fin 4 → BitVec 64} {env : SEnvScalar} {Q : BitVec 64}
    (h : SelInv N T D O a env) (hq : env "q" = some ⟨.sword 64, Q⟩)
    (tw e : Nat) (k : Fin 4) (hi : 4 * e + k.val < 2 ^ 64) :
    ∃ env', semScalar (seqL (cellSelCmds tw e k)) env = some env'
      ∧ SelInv N T D O (setLimb a k (selectWord Q (memGetDyn T (4 * e + k.val)) (a k))) env'
      ∧ env' "q" = some ⟨.sword 64, Q⟩ := by
  have nq : ¬ isTmpName "q" := notTmp_of_head (by decide)
  obtain ⟨e1, s1, v1, f1⟩ := setE_run (x := "i") (e := .SLit (4 * e + k.val))
    (env := env) (litClean hi) (by simp [sexprVars])
  have h1 := h.frame f1 rfl
  have q1 := (f1 "q" nq (by decide)).trans hq
  have s2 := arrLoad_eq (dstN := "l") (tw := .TBytes tw) h1.tbl v1
  set e2 := e1.upd "l" (t := .sword 64) (memGetDyn T (SExpr.evalBV (envReader env)
    (.SLit (4 * e + k.val))).toNat) with he2
  have f2 : ∀ s, ¬ isTmpName s → s ≠ "l" → e2 s = e1 s := fun s _ hs => upd_ne' hs
  have v2 : e2 "l" = some ⟨.sword 64, memGetDyn T (4 * e + k.val)⟩ := by
    rw [he2, SEnvScalar.upd, ite_eq_left rfl]
    simp only [SExpr.evalBV, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
  have h2 := h1.frame f2 rfl
  have q2 : e2 "q" = some ⟨.sword 64, Q⟩ := (f2 "q" nq (by decide)).trans q1
  have s3 := semScalar_rSelect_word ⟨accName k, .TU64⟩ "q" ⟨"l", .TU64⟩ ⟨accName k, .TU64⟩
    e2 Q (memGetDyn T (4 * e + k.val)) (a k) rfl q2 v2 (h2.acc k)
  refine ⟨e2.upd (accName k) (t := .sword 64)
    (selectWord Q (memGetDyn T (4 * e + k.val)) (a k)), ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [cellSelCmds, semScalar_seqL_cons s1, semScalar_seqL_cons s2, semScalar_seqL_cons s3,
      semScalar_seqL_nil]
  · rw [upd_ne' (Ne.symm (accName_ne_tbl k))]; exact h2.tbl
  · rw [upd_ne' (Ne.symm (accName_ne_d k))]; exact h2.d
  · rw [upd_ne' (Ne.symm (accName_ne_out k))]; exact h2.out
  · intro j
    by_cases hj : j = k
    · subst hj
      simp [SEnvScalar.upd, setLimb]
    · rw [upd_ne' (accName_ne hj)]
      simp only [setLimb, ite_eq_right hj]
      exact h2.acc j
  · rw [upd_ne' (Ne.symm (accName_ne_q k))]; exact q2

/-- The limbs after one entry: table entry `e` when `D = e`, unchanged
    otherwise. -/
def entrySelVal {N : Nat} (T : Fin (4 * N) → BitVec 64) (D : BitVec 64) (e : Nat)
    (a : Fin 4 → BitVec 64) : Fin 4 → BitVec 64 :=
  fun k => selectWord (D ^^^ BitVec.ofNat 64 e) (memGetDyn T (4 * e + k.val)) (a k)

/-- One entry of the scan selects the entry into the running limbs. -/
theorem entrySelCmds_run {N : Nat} {T : Fin (4 * N) → BitVec 64} {D : BitVec 64}
    {O a : Fin 4 → BitVec 64} {env : SEnvScalar}
    (h : SelInv N T D O a env) (tw e : Nat) (he : 4 * e + 4 ≤ 2 ^ 64) :
    ∃ env', semScalar (seqL (entrySelCmds tw e)) env = some env'
      ∧ SelInv N T D O (entrySelVal T D e a) env' := by
  obtain ⟨e0, s0, h0, q0⟩ := testCmd_run h e (by omega)
  obtain ⟨e1, s1, h1, q1⟩ := cellSelCmds_run h0 q0 tw e 0 (by simp; omega)
  obtain ⟨e2, s2, h2, q2⟩ := cellSelCmds_run h1 q1 tw e 1 (by simp; omega)
  obtain ⟨e3, s3, h3, q3⟩ := cellSelCmds_run h2 q2 tw e 2 (by simp; omega)
  obtain ⟨e4, s4, h4, -⟩ := cellSelCmds_run h3 q3 tw e 3 (by simp; omega)
  refine ⟨e4, ?_, ?_⟩
  · rw [entrySelCmds, semScalar_seqL_cons s0, semScalar_seqL_append, s1, Option.bind_some,
      semScalar_seqL_append, s2, Option.bind_some, semScalar_seqL_append, s3,
      Option.bind_some, s4]
  · convert h4 using 2
    funext j
    match j with
    | 0 | 1 | 2 | 3 => simp [setLimb, entrySelVal]

/-- Running limb `k` after the first `n` entries of the scan. -/
def selScanVal {N : Nat} (T : Fin (4 * N) → BitVec 64) (D : BitVec 64) (k : Fin 4) :
    Nat → BitVec 64
  | 0 => 0
  | n + 1 => selectWord (D ^^^ BitVec.ofNat 64 n) (memGetDyn T (4 * n + k.val))
      (selScanVal T D k n)

/-- The scan over `n` entries leaves `selScanVal` in the running limbs. -/
theorem scanSelCmds_run {N : Nat} {T : Fin (4 * N) → BitVec 64} {D : BitVec 64}
    {O : Fin 4 → BitVec 64} (tw : Nat) :
    ∀ (n : Nat) (env : SEnvScalar), 4 * n ≤ 2 ^ 64 →
      SelInv N T D O (fun _ => 0) env →
      ∃ env', semScalar (seqL (scanSelCmds tw n)) env = some env'
        ∧ SelInv N T D O (fun k => selScanVal T D k n) env'
  | 0, env, _, h => ⟨env, semScalar_seqL_nil env, h⟩
  | n + 1, env, hn, h => by
      obtain ⟨e1, s1, h1⟩ := scanSelCmds_run tw n env (by omega) h
      obtain ⟨e2, s2, h2⟩ := entrySelCmds_run h1 tw n (by omega)
      exact ⟨e2, by rw [scanSelCmds, semScalar_seqL_append, s1, Option.bind_some, s2], h2⟩

/-- **The entry-boundary invariant.** After `n` entries the conditional-select
    scan holds the entry at the index when the index is below `n`, and `0`
    otherwise. -/
theorem selScanVal_eq {N : Nat} (T : Fin (4 * N) → BitVec 64) (D : BitVec 64) (k : Fin 4) :
    ∀ n, n ≤ 2 ^ 64 →
      selScanVal T D k n = if D.toNat < n then memGetDyn T (4 * D.toNat + k.val) else 0
  | 0, _ => by simp [selScanVal]
  | n + 1, hn => by
      have ih := selScanVal_eq T D k n (by omega)
      have h64 : n < 2 ^ 64 := by omega
      have hiff : D ^^^ BitVec.ofNat 64 n = 0#64 ↔ D.toNat = n := by
        rw [BitVec.xor_eq_zero_iff]
        constructor
        · rintro rfl; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h64
        · intro h
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]; exact h
      rw [selScanVal, ih, selectWord]
      by_cases heq : D.toNat = n
      · rw [ite_eq_left (hiff.mpr heq), ite_eq_left (by omega)]
        subst heq; rfl
      · rw [ite_eq_right (fun h => heq (hiff.mp h))]
        by_cases hlt : D.toNat < n
        · rw [ite_eq_left hlt, ite_eq_left (by omega)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]

/-- **The two scans agree at every entry boundary.** After `n` entries the
    running limbs of the conditional-select scan equal those of the mask-form
    scan of `CombSelectFront`. -/
theorem selScanVal_eq_scanVal {N : Nat} (T : Fin (4 * N) → BitVec 64) (D : BitVec 64)
    (k : Fin 4) (n : Nat) (hn : n ≤ 2 ^ 64) : selScanVal T D k n = scanVal T D k n := by
  rw [selScanVal_eq T D k n hn, scanVal_eq T D k n hn]

/-- **Waist semantics of the source.** From an environment binding the table
    `T`, the index `D` and the output buffer, the source runs to completion and
    leaves `out[k] = T[4·D + k]` when `D < N`, and `out[k] = 0` otherwise. -/
theorem combSelectCmovSrc_run (N : Nat) (hN : 4 * N ≤ 2 ^ 64) {T : Fin (4 * N) → BitVec 64}
    {D : BitVec 64} {O : Fin 4 → BitVec 64} {env : SEnvScalar}
    (ht : env "tbl" = some ⟨.memref (4 * N), T⟩) (hd : env "d" = some ⟨.sword 64, D⟩)
    (ho : env "out" = some ⟨.memref 4, O⟩) :
    ∃ env', semScalar (combSelectCmovSrc N) env = some env'
      ∧ env' "out" = some ⟨.memref 4, fun k =>
          if D.toNat < N then memGetDyn T (4 * D.toNat + k.val) else 0⟩ := by
  obtain ⟨e1, s1, h1⟩ := selInit_run ht hd ho
  obtain ⟨e2, s2, h2⟩ := scanSelCmds_run (32 * N) N e1 hN h1
  obtain ⟨e3, s3, h3⟩ := storeAll_run h2
  refine ⟨e3, ?_, ?_⟩
  · rw [combSelectCmovSrc, semScalar_seqL_append, s1, Option.bind_some, semScalar_seqL_append,
      s2, Option.bind_some, s3]
  · rw [h3.out]
    congr
    funext k
    exact selScanVal_eq T D k N (by omega)

/-- **The conditional-select source refines the mask-form source.** From an
    environment binding the table, the index and the output buffer, both
    sources run to completion and leave the same buffer in `out`. -/
theorem combSelectCmovSrc_refines (N : Nat) (hN : 4 * N ≤ 2 ^ 64)
    {T : Fin (4 * N) → BitVec 64} {D : BitVec 64} {O : Fin 4 → BitVec 64} {env : SEnvScalar}
    (ht : env "tbl" = some ⟨.memref (4 * N), T⟩) (hd : env "d" = some ⟨.sword 64, D⟩)
    (ho : env "out" = some ⟨.memref 4, O⟩) :
    ∃ envS envC, semScalar (combSelectSrc N) env = some envS
      ∧ semScalar (combSelectCmovSrc N) env = some envC
      ∧ envC "out" = envS "out" := by
  obtain ⟨envS, hS, oS⟩ := combSelectSrc_run N hN ht hd ho
  obtain ⟨envC, hC, oC⟩ := combSelectCmovSrc_run N hN ht hd ho
  exact ⟨envS, envC, hS, hC, oC.trans oS.symm⟩

/-! ## 5. The reads-bound judgment and the front output -/

theorem testCmd_tt {N : Nat} {σ : NameTys} (h : TyInv N σ) (e : Nat) (he : e < 2 ^ 64) :
    ∃ σ', TransTotal σ (testCmd e) σ' ∧ TyInv N σ' ∧ σ' "q" = some (.sword 64) := by
  have nq : ¬ isTmpName "q" := notTmp_of_head (by decide)
  have nd : ¬ isTmpName "d" := notTmp_of_head (by decide)
  refine ⟨_, .rScalarSetExpr "q" _ nq ⟨nd, he⟩ ?_, h.upd (x := "q") (.sword 64) rfl,
    nameTys_upd_self _ _ _⟩
  simp [sexprVars, h.d]

theorem cellSelCmds_tt {N : Nat} {σ : NameTys} (h : TyInv N σ) (hq : σ "q" = some (.sword 64))
    (tw e : Nat) (k : Fin 4) (hi : 4 * e + k.val < 2 ^ 64) :
    ∃ σ', TransTotal σ (seqL (cellSelCmds tw e k)) σ' ∧ TyInv N σ'
      ∧ σ' "q" = some (.sword 64) := by
  have ni : ¬ isTmpName "i" := notTmp_of_head (by decide)
  have nl : ¬ isTmpName "l" := notTmp_of_head (by decide)
  have h1 := h.upd (x := "i") (.sword 64) rfl
  have h2 := h1.upd (x := "l") (encodeTy .TU64) rfl
  have q2 : (σ.upd "i" (.sword 64)).upd "l" (encodeTy .TU64) "q" = some (.sword 64) := by
    rw [nameTys_upd_ne (by decide), nameTys_upd_ne (by decide)]; exact hq
  refine ⟨_, .rSeq (.rScalarSetExpr "i" _ ni (litClean hi) (by simp [sexprVars]))
    (.rSeq (.rArrLoad ⟨"l", .TU64⟩ ⟨"tbl", .TBytes tw⟩ "i" nl
      (by simp [nameTys_upd_ne, h.tbl]) (by simp [nameTys_upd_self]))
    (.rSeq (.rSelect ⟨accName k, .TU64⟩ "q" ⟨"l", .TU64⟩ ⟨accName k, .TU64⟩
      (accName_notTmp k) rfl q2 (nameTys_upd_self _ _ _) (h2.acc k)) .rSkip)),
    h2.updAcc k, ?_⟩
  rw [nameTys_upd_ne (Ne.symm (accName_ne_q k))]; exact q2

theorem entrySelCmds_tt {N : Nat} {σ : NameTys} (h : TyInv N σ) (tw e : Nat)
    (he : 4 * e + 4 ≤ 2 ^ 64) :
    ∃ σ', TransTotal σ (seqL (entrySelCmds tw e)) σ' ∧ TyInv N σ' := by
  obtain ⟨σ0, t0, h0, q0⟩ := testCmd_tt h e (by omega)
  obtain ⟨σ1, t1, h1, q1⟩ := cellSelCmds_tt h0 q0 tw e 0 (by simp; omega)
  obtain ⟨σ2, t2, h2, q2⟩ := cellSelCmds_tt h1 q1 tw e 1 (by simp; omega)
  obtain ⟨σ3, t3, h3, q3⟩ := cellSelCmds_tt h2 q2 tw e 2 (by simp; omega)
  obtain ⟨σ4, t4, h4, -⟩ := cellSelCmds_tt h3 q3 tw e 3 (by simp; omega)
  exact ⟨σ4, .rSeq t0 (transTotal_seqL_append t1 (transTotal_seqL_append t2
    (transTotal_seqL_append t3 t4))), h4⟩

theorem scanSelCmds_tt {N : Nat} (tw : Nat) :
    ∀ (n : Nat) {σ : NameTys}, 4 * n ≤ 2 ^ 64 → TyInv N σ →
      ∃ σ', TransTotal σ (seqL (scanSelCmds tw n)) σ' ∧ TyInv N σ'
  | 0, σ, _, h => ⟨σ, .rSkip, h⟩
  | n + 1, σ, hn, h => by
      obtain ⟨σ1, t1, h1⟩ := scanSelCmds_tt tw n (by omega) h
      obtain ⟨σ2, t2, h2⟩ := entrySelCmds_tt h1 tw n (by omega)
      exact ⟨σ2, by rw [scanSelCmds]; exact transTotal_seqL_append t1 t2, h2⟩

/-- **The source is in the reads-bound covered fragment.** -/
theorem combSelectCmovSrc_transTotal (N : Nat) (hN : 4 * N ≤ 2 ^ 64) :
    ∃ σ', TransTotal (selTys N) (combSelectCmovSrc N) σ' ∧ TyInv N σ' := by
  obtain ⟨σ1, t1, h1⟩ := selInit_tt N
  obtain ⟨σ2, t2, h2⟩ := scanSelCmds_tt (N := N) (32 * N) N hN h1
  obtain ⟨σ3, t3, h3⟩ := storeCmds_tt h2 0
  obtain ⟨σ4, t4, h4⟩ := storeCmds_tt h3 1
  obtain ⟨σ5, t5, h5⟩ := storeCmds_tt h4 2
  obtain ⟨σ6, t6, h6⟩ := storeCmds_tt h5 3
  exact ⟨σ6, transTotal_seqL_append t1 (transTotal_seqL_append t2
    (transTotal_seqL_append t3 (transTotal_seqL_append t4 (transTotal_seqL_append t5 t6)))),
    h6⟩

/-- The front translates the source and the result lowers to `Com jasminDialect`. -/
theorem combSelectCmovFront_spec (N : Nat) (hN : 4 * N ≤ 2 ^ 64) :
    ∃ (o : DTransOut (selCtx N)) (v : CVar o.Γ' (.memref 4))
      (com : Com catCryptDialect (selCtx N) (.memref 4)),
      translateDialectControl (selVM N) (combSelectCmovSrc N) = some o
      ∧ o.vm.lookup "out" = some ⟨.memref 4, v⟩
      ∧ o.cont (Com.ret (toVIRVar v)) = some com
      ∧ combSelectCmovFront N = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome := by
  obtain ⟨σ', htt, hinv⟩ := combSelectCmovSrc_transTotal N hN
  obtain ⟨o, htr, happ, hcont⟩ :=
    translateDialectControl_total htt (selVM N) (selTys_srcTys N) (selTys_vmApprox N)
  obtain ⟨v, hv⟩ := happ "out" (.memref 4) hinv.out
  obtain ⟨com, hcom, hlow⟩ := hcont (Com.ret (toVIRVar v)) (by rfl)
  refine ⟨o, v, com, htr, hv, hcom, ?_, hlow⟩
  simp only [combSelectCmovFront, htr, hv]
  exact hcom

/-- **Value correctness of the front output.** For every table `T`, index `D`
    and initial output buffer, the program the front produces from
    `combSelectCmovSrc N` lowers to `Com jasminDialect` and returns the buffer
    `out` with `out[k] = T[4·D + k]` when `D < N`, and `out[k] = 0` otherwise:
    the denotation `CombSelectFront.combSelectFront_denote` gives for the
    mask-form source. -/
theorem combSelectCmovFront_denote (N : Nat) (hN : 4 * N ≤ 2 ^ 64)
    (O : Fin 4 → BitVec 64) (D : BitVec 64) (T : Fin (4 * N) → BitVec 64) :
    ∃ com, combSelectCmovFront N = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome
      ∧ com.denote (selVal N O D T) = fun k =>
          if D.toNat < N then memGetDyn T (4 * D.toNat + k.val) else 0 := by
  obtain ⟨σ', htt, -⟩ := combSelectCmovSrc_transTotal N hN
  obtain ⟨o, v, com, htr, hv, hcom, hfront, hlow⟩ := combSelectCmovFront_spec N hN
  have hc : ConsistentS (selVM N) (selVal N O D T) (selEnv N (selVal N O D T)) :=
    fun _ => rfl
  have ht : selEnv N (selVal N O D T) "tbl" = some ⟨.memref (4 * N), T⟩ := by
    simp [selEnv, selVM, VarMap.bind, VarMap.empty, selVal]; rfl
  have hd : selEnv N (selVal N O D T) "d" = some ⟨.sword 64, D⟩ := by
    simp [selEnv, selVM, VarMap.bind, selVal]; rfl
  have ho : selEnv N (selVal N O D T) "out" = some ⟨.memref 4, O⟩ := by
    simp [selEnv, selVM, VarMap.bind, selVal]; rfl
  obtain ⟨env', hsem, hout⟩ := combSelectCmovSrc_run N hN ht hd ho
  obtain ⟨V', hc', htail⟩ := translateDialectControl_denote htt.toIsCoveredS (selVM N)
    (selVal N O D T) _ env' o hc htr hsem
  obtain ⟨com', hcom', hden⟩ := htail (Com.ret (toVIRVar v))
  rw [hcom] at hcom'
  cases hcom'
  refine ⟨com, hfront, hlow, ?_⟩
  rw [hden]
  exact ConsistentS.lookup_eq hc' hv hout

/-- The two front outputs denote the same function of the table, the index and
    the output buffer. -/
theorem combSelectCmovFront_denote_eq (N : Nat) (hN : 4 * N ≤ 2 ^ 64)
    (O : Fin 4 → BitVec 64) (D : BitVec 64) (T : Fin (4 * N) → BitVec 64) :
    ∃ comC comS, combSelectCmovFront N = some comC ∧ combSelectFront N = some comS
      ∧ comC.denote (selVal N O D T) = comS.denote (selVal N O D T) := by
  obtain ⟨comC, hC, -, dC⟩ := combSelectCmovFront_denote N hN O D T
  obtain ⟨comS, hS, -, dS⟩ := combSelectFront_denote N hN O D T
  exact ⟨comC, comS, hC, hS, dC.trans dS.symm⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectCmovFront
