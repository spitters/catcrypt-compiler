/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public import CatCrypt.Crypto.Optimizer.Lattice.LayeredNtt

/-!
# BabyBear NTT butterflies generated through the front, on all inputs

`Plonky3NttLayerEmit` generates the last layer of the 8-point BabyBear NTT
(`p = 2013265921`) through the front: `butterflyStmts` is the Barrett/csub
butterfly as `LowCT`, `translateDialectControl` turns the layer body into
`Com catCryptDialect`, `cryptoDialectToJasminCom` into `Com jasminDialect`. This
module proves what those programs compute for every input, and uses the same
butterfly generator for the whole `2^k`-point transform of `ntt.rs`.

The proof reads the front programs through the front-general preservation theorem
`TranslateDialectScalar.translateDialectControl_denote`: a body in the reads-bound
fragment (`TranslateDialectTotality.TransTotal`) is translated, and the emitted
program denotes the source semantics `semScalar`. The source semantics of one
butterfly is computed symbolically, and its words are identified with field
elements through the Barrett law `Plonky3BarrettLaw.barrettMul_correct`.

## Main results

* `butterfly_run` — one emitted butterfly leaves `fixW (a + wbW w b − p)` and
  `fixW (a − wbW w b)` in its two value slots; `enc_lo`, `enc_hi` read these as
  `a + w·b` and `a − w·b` in `ZMod p`.
* `finv_steps`, `copies_run`, `butterflies_tt`, `copies_tt` — a list of butterflies
  followed by output copies runs as the fold of `LayeredNtt.bupd`, and is in the
  front's reads-bound fragment.
* `layer_frontComAt_denote`, `layer_frontComAt_ctLayer` — the deployed layer
  (`plonky3_ntt_layer8_rc`) computes `LayeredNtt.ctLayer 4 ω` on all canonical
  inputs; `layer_frontComAt_dft` — applied to the output of the first two layers
  it yields the 8-point DFT; `layerLowered_denote`, `layerCom_denote` — the same
  for the lowered `Com jasminDialect`.
* `kFrontAt_denote` — any admissible butterfly network generated through the
  front computes its fold of `bupd`.
* `nttKernelAt_dft` — the generated `2^(e+1)`-point kernel computes
  `dft (2^(e+1)) ω` on the bit-reversed input for every `ω` with `ω^(2^e) = −1`;
  `nttKernelAt_dft_bbRoot` instantiates `ω` with `bb_root_of_unity(e+1)` for
  `e + 1 ≤ 27` (`bbRoot_pow_half`).

## Conventions

Values and twiddles are canonical residues in 64-bit words (`Enc`). The kernel's
inputs are the `2^(e+1)` values in bit-reversed order (`bitrevWords`), the `2^e`
twiddle words `ω^0, …, ω^(2^e − 1)`, then `MU` and `p`; output `q k` holds
`Σ_i x_i ω^{ik}`, the evaluation at `ω^k` of the polynomial with coefficients `x`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerDenote

open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit (bbP bbCsub bbCsub_correct bbP_toNat)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3BarrettLaw

/-! ## 1. Word arithmetic of one butterfly -/

/-- The branch-free correction the emitted code applies to a word `d`:
`d + ((0 − (d >> 63)) & p)`, adding `p` exactly when the top bit of `d` is set. -/
def fixW (d : BitVec 64) : BitVec 64 := d + (((0 : BitVec 64) - (d >>> 63)) &&& bbP)

theorem mask_eq (d : BitVec 64) :
    ((0 : BitVec 64) - (d >>> 63)) &&& bbP = if d.toNat < 2 ^ 63 then 0 else bbP := by
  have hlt := d.isLt
  split_ifs with h
  · have : d >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [Nat.div_eq_of_lt h]; rfl
    rw [this]; exact BitVec.eq_of_toNat_eq rfl
  · have : d >>> 63 = 1 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have h1 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
      rw [h1]
      omega
    rw [this]; exact BitVec.eq_of_toNat_eq rfl

theorem fixW_sub (x y : BitVec 64) (hx : x.toNat < 2013265921) (hy : y.toNat < 2013265921) :
    (fixW (x - y)).toNat = (x.toNat + 2013265921 - y.toNat) % 2013265921 := by
  unfold fixW
  rw [mask_eq]
  by_cases hxy : y.toNat ≤ x.toNat
  · have hs : (x - y).toNat = x.toNat - y.toNat := BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]; exact hxy)
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [ite_eq_left (by omega), BitVec.toNat_add, hs, h0, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    rw [show x.toNat + 2013265921 - y.toNat = (x.toNat - y.toNat) + 2013265921 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · have hs : (x - y).toNat = 2 ^ 64 - (y.toNat - x.toNat) := by
      rw [BitVec.toNat_sub]; omega
    rw [ite_eq_right (by omega), BitVec.toNat_add, hs, bbP_toNat]
    rw [Nat.mod_eq_of_lt (show x.toNat + 2013265921 - y.toNat < 2013265921 by omega)]
    omega

theorem fixW_add (x y : BitVec 64) (hx : x.toNat < 2013265921) (hy : y.toNat < 2013265921) :
    (fixW (x + y - bbP)).toNat = (x.toNat + y.toNat) % 2013265921 := by
  unfold fixW
  rw [mask_eq]
  have hxy : (x + y).toNat = x.toNat + y.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  by_cases h : 2013265921 ≤ x.toNat + y.toNat
  · have hs : (x + y - bbP).toNat = x.toNat + y.toNat - 2013265921 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hxy, bbP_toNat]; exact h), hxy, bbP_toNat]
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [ite_eq_left (by omega), BitVec.toNat_add, hs, h0, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    rw [show x.toNat + y.toNat = (x.toNat + y.toNat - 2013265921) + 2013265921 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hs : (x + y - bbP).toNat = 2 ^ 64 - (2013265921 - (x.toNat + y.toNat)) := by
      rw [BitVec.toNat_sub, hxy, bbP_toNat]; omega
    rw [ite_eq_right (by omega), BitVec.sub_add_cancel, hxy, Nat.mod_eq_of_lt (by omega)]

/-- The Barrett-reduced product the emitted butterfly computes from twiddle `w`
and value `b`: `x = w·b`, `q = ((x >> 30)·MU) >> 32`, `t = x − q·p`, then one
correction of `t − p`. -/
def wbW (w b : BitVec 64) : BitVec 64 :=
  fixW (w * b - ((w * b) >>> 30 * bbMU) >>> 32 * bbP - bbP)

theorem wbW_toNat (w b : BitVec 64) (hw : w.toNat < 2013265921) (hb : b.toNat < 2013265921) :
    (wbW w b).toNat = w.toNat * b.toNat % 2013265921 := by
  have hwb : wbW w b = barrettReduceMU (w * b) := by
    simp only [wbW, fixW, barrettReduceMU, bbCsub, BitVec.and_comm]
  have hw' : w < bbP := by rw [BitVec.lt_def, bbP_toNat]; exact hw
  have hb' : b < bbP := by rw [BitVec.lt_def, bbP_toNat]; exact hb
  rw [hwb, barrettMul_correct w b hw' hb', BitVec.toNat_umod, bbP_toNat, BitVec.toNat_mul,
    Nat.mod_eq_of_lt (a := w.toNat * b.toNat) (b := 2 ^ 64) (by nlinarith)]

/-! ## 2. The waist semantics of one emitted butterfly -/

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront
  (seqL setE_run notTmp_of_head litClean readU64_of reader_of semScalar_seqL_cons
   semScalar_seqL_nil semScalar_seqL_append transTotal_seqL_append nameTys_upd_self
   nameTys_upd_ne)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerEmit
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-- The seven scratch names one butterfly writes besides its two value slots. -/
def bflyTemps : List String := ["x", "q", "t", "s", "wb", "d", "e"]

/-- The name conditions one butterfly on value slots `lo`, `hi` and twiddle slot
`tw` needs: the three slots and the constants `mu`, `p` are source names outside
the scratch names, and the three slots are pairwise distinct and distinct from
`mu`, `p`. -/
structure BflyNames (lo hi : Nat) (tw : String) : Prop where
  lo_src : ¬ isTmpName (vN lo)
  hi_src : ¬ isTmpName (vN hi)
  tw_src : ¬ isTmpName tw
  lo_tmp : vN lo ∉ "mu" :: "p" :: bflyTemps
  hi_tmp : vN hi ∉ "mu" :: "p" :: bflyTemps
  tw_tmp : tw ∉ "mu" :: "p" :: bflyTemps
  lo_hi : vN lo ≠ vN hi
  tw_lo : tw ≠ vN lo
  tw_hi : tw ≠ vN hi

theorem butterfly_run (lo hi : Nat) (tw : String) (hn : BflyNames lo hi tw)
    {env : SEnvScalar} {a b w : BitVec 64}
    (hL : env (vN lo) = some ⟨.sword 64, a⟩) (hH : env (vN hi) = some ⟨.sword 64, b⟩)
    (hT : env tw = some ⟨.sword 64, w⟩) (hmu : env "mu" = some ⟨.sword 64, bbMU⟩)
    (hp : env "p" = some ⟨.sword 64, bbP⟩) :
    ∃ env', semScalar (seqL (butterflyStmts lo hi tw)) env = some env'
      ∧ env' (vN hi) = some ⟨.sword 64, fixW (a - wbW w b)⟩
      ∧ env' (vN lo) = some ⟨.sword 64, fixW (a + wbW w b - bbP)⟩
      ∧ ∀ s, ¬ isTmpName s → s ∉ bflyTemps → s ≠ vN lo → s ≠ vN hi → env' s = env s := by
  obtain ⟨nL, nH, nT, tL, tH, tT, dLH, dTL, dTH⟩ := hn
  simp only [bflyTemps, List.mem_cons, List.not_mem_nil, not_or] at tL tH tT
  have nx : ¬ isTmpName "x" := notTmp_of_head (by decide)
  have nq : ¬ isTmpName "q" := notTmp_of_head (by decide)
  have nt : ¬ isTmpName "t" := notTmp_of_head (by decide)
  have ns : ¬ isTmpName "s" := notTmp_of_head (by decide)
  have nwb : ¬ isTmpName "wb" := notTmp_of_head (by decide)
  have nd : ¬ isTmpName "d" := notTmp_of_head (by decide)
  have ne : ¬ isTmpName "e" := notTmp_of_head (by decide)
  have nmu : ¬ isTmpName "mu" := notTmp_of_head (by decide)
  have np : ¬ isTmpName "p" := notTmp_of_head (by decide)
  have h0 : BitVec.ofNat 64 0 = 0 := rfl
  have h30 : (BitVec.ofNat 64 30).toNat = 30 := rfl
  have h32 : (BitVec.ofNat 64 32).toNat = 32 := rfl
  have h63 : (BitVec.ofNat 64 63).toNat = 63 := rfl
  -- x = tw * v[hi]
  obtain ⟨e1, r1, v1, f1⟩ := setE_run (x := "x") (env := env)
    (e := .SMul (.SVar tw) (.SVar (vN hi))) ⟨nT, nH⟩
    (by intro s hs; simp only [sexprVars, List.mem_cons, List.not_mem_nil, or_false,
          List.cons_append, List.nil_append] at hs
        rcases hs with rfl | rfl
        · exact readU64_of hT
        · exact readU64_of hH)
  simp only [SExpr.evalBV, reader_of hT, reader_of hH] at v1
  -- q = ((x >> 30) * mu) >> 32
  have m1 : e1 "mu" = some ⟨.sword 64, bbMU⟩ := by rw [f1 _ nmu (by decide)]; exact hmu
  obtain ⟨e2, r2, v2, f2⟩ := setE_run (x := "q") (env := e1)
    (e := .SShr (.SMul (.SShr (.SVar "x") (.SLit 30)) (.SVar "mu")) (.SLit 32))
    ⟨⟨⟨nx, litClean (by norm_num)⟩, nmu⟩, litClean (by norm_num)⟩
    (by intro s hs; simp only [sexprVars, List.mem_cons, List.not_mem_nil, or_false,
          List.cons_append, List.nil_append, List.append_nil] at hs
        rcases hs with rfl | rfl
        · exact readU64_of v1
        · exact readU64_of m1)
  simp only [SExpr.evalBV, reader_of v1, reader_of m1, h30, h32] at v2
  -- t = x - q * p
  have x2 : e2 "x" = some ⟨.sword 64, w * b⟩ := by rw [f2 _ nx (by decide)]; exact v1
  have p2 : e2 "p" = some ⟨.sword 64, bbP⟩ := by
    rw [f2 _ np (by decide), f1 _ np (by decide)]; exact hp
  obtain ⟨e3, r3, v3, f3⟩ := setE_run (x := "t") (env := e2)
    (e := .SSub (.SVar "x") (.SMul (.SVar "q") (.SVar "p"))) ⟨nx, ⟨nq, np⟩⟩
    (by intro s hs; simp only [sexprVars, List.mem_cons, List.not_mem_nil, or_false,
          List.cons_append, List.nil_append] at hs
        rcases hs with rfl | rfl | rfl
        · exact readU64_of x2
        · exact readU64_of v2
        · exact readU64_of p2)
  simp only [SExpr.evalBV, reader_of x2, reader_of v2, reader_of p2] at v3
  -- s = t - p
  have p3 : e3 "p" = some ⟨.sword 64, bbP⟩ := by rw [f3 _ np (by decide)]; exact p2
  obtain ⟨e4, r4, v4, f4⟩ := setE_run (x := "s") (env := e3)
    (e := .SSub (.SVar "t") (.SVar "p")) ⟨nt, np⟩
    (by intro s hs; simp only [sexprVars, List.mem_cons, List.not_mem_nil, or_false,
          List.cons_append, List.nil_append] at hs
        rcases hs with rfl | rfl
        · exact readU64_of v3
        · exact readU64_of p3)
  simp only [SExpr.evalBV, reader_of v3, reader_of p3] at v4
  -- wb = s + csub(s)
  have p4 : e4 "p" = some ⟨.sword 64, bbP⟩ := by rw [f4 _ np (by decide)]; exact p3
  obtain ⟨e5, r5, v5, f5⟩ := setE_run (x := "wb") (env := e4)
    (e := .SAdd (.SVar "s") (csubMask "s"))
    ⟨ns, ⟨⟨litClean (by norm_num), ⟨ns, litClean (by norm_num)⟩⟩, np⟩⟩
    (by intro s hs; simp only [csubMask, sexprVars, List.mem_cons, List.not_mem_nil, or_false,
          List.cons_append, List.nil_append, List.append_nil] at hs
        rcases hs with rfl | rfl | rfl
        · exact readU64_of v4
        · exact readU64_of v4
        · exact readU64_of p4)
  simp only [csubMask, SExpr.evalBV, reader_of v4, reader_of p4, h0, h63] at v5
  change e5 "wb" = some ⟨.sword 64, wbW w b⟩ at v5
  -- d = v[lo] - wb
  have l5 : e5 (vN lo) = some ⟨.sword 64, a⟩ := by
    rw [f5 _ nL tL.2.2.2.2.2.2.1, f4 _ nL tL.2.2.2.2.2.1, f3 _ nL tL.2.2.2.2.1,
      f2 _ nL tL.2.2.2.1, f1 _ nL tL.2.2.1]; exact hL
  obtain ⟨e6, r6, v6, f6⟩ := setE_run (x := "d") (env := e5)
    (e := .SSub (.SVar (vN lo)) (.SVar "wb")) ⟨nL, nwb⟩
    (by intro s hs; simp only [sexprVars, List.mem_cons, List.not_mem_nil, or_false,
          List.cons_append, List.nil_append] at hs
        rcases hs with rfl | rfl
        · exact readU64_of l5
        · exact readU64_of v5)
  simp only [SExpr.evalBV, reader_of l5, reader_of v5] at v6
  -- v[hi] = d + csub(d)
  have p6 : e6 "p" = some ⟨.sword 64, bbP⟩ := by
    rw [f6 _ np (by decide), f5 _ np (by decide)]; exact p4
  obtain ⟨e7, r7, v7, f7⟩ := setE_run (x := vN hi) (env := e6)
    (e := .SAdd (.SVar "d") (csubMask "d"))
    ⟨nd, ⟨⟨litClean (by norm_num), ⟨nd, litClean (by norm_num)⟩⟩, np⟩⟩
    (by intro s hs; simp only [csubMask, sexprVars, List.mem_cons, List.not_mem_nil, or_false,
          List.cons_append, List.nil_append, List.append_nil] at hs
        rcases hs with rfl | rfl | rfl
        · exact readU64_of v6
        · exact readU64_of v6
        · exact readU64_of p6)
  simp only [csubMask, SExpr.evalBV, reader_of v6, reader_of p6, h0, h63] at v7
  -- e = (v[lo] + wb) - p
  have l7 : e7 (vN lo) = some ⟨.sword 64, a⟩ := by
    rw [f7 _ nL dLH, f6 _ nL tL.2.2.2.2.2.2.2.1]; exact l5
  have w7 : e7 "wb" = some ⟨.sword 64, wbW w b⟩ := by
    rw [f7 _ nwb (fun h => tH.2.2.2.2.2.2.1 h.symm), f6 _ nwb (by decide)]; exact v5
  have p7 : e7 "p" = some ⟨.sword 64, bbP⟩ := by
    rw [f7 _ np (fun h => tH.2.1 h.symm)]; exact p6
  obtain ⟨e8, r8, v8, f8⟩ := setE_run (x := "e") (env := e7)
    (e := .SSub (.SAdd (.SVar (vN lo)) (.SVar "wb")) (.SVar "p")) ⟨⟨nL, nwb⟩, np⟩
    (by intro s hs; simp only [sexprVars, List.mem_cons, List.not_mem_nil, or_false,
          List.cons_append, List.nil_append] at hs
        rcases hs with rfl | rfl | rfl
        · exact readU64_of l7
        · exact readU64_of w7
        · exact readU64_of p7)
  simp only [SExpr.evalBV, reader_of l7, reader_of w7, reader_of p7] at v8
  -- v[lo] = e + csub(e)
  have p8 : e8 "p" = some ⟨.sword 64, bbP⟩ := by rw [f8 _ np (by decide)]; exact p7
  obtain ⟨e9, r9, v9, f9⟩ := setE_run (x := vN lo) (env := e8)
    (e := .SAdd (.SVar "e") (csubMask "e"))
    ⟨ne, ⟨⟨litClean (by norm_num), ⟨ne, litClean (by norm_num)⟩⟩, np⟩⟩
    (by intro s hs; simp only [csubMask, sexprVars, List.mem_cons, List.not_mem_nil, or_false,
          List.cons_append, List.nil_append, List.append_nil] at hs
        rcases hs with rfl | rfl | rfl
        · exact readU64_of v8
        · exact readU64_of v8
        · exact readU64_of p8)
  simp only [csubMask, SExpr.evalBV, reader_of v8, reader_of p8, h0, h63] at v9
  refine ⟨e9, ?_, ?_, v9, ?_⟩
  · simp only [butterflyStmts]
    rw [semScalar_seqL_cons r1, semScalar_seqL_cons r2, semScalar_seqL_cons r3,
      semScalar_seqL_cons r4, semScalar_seqL_cons r5, semScalar_seqL_cons r6,
      semScalar_seqL_cons r7, semScalar_seqL_cons r8, semScalar_seqL_cons r9,
      semScalar_seqL_nil]
  · rw [f9 _ nH (Ne.symm dLH), f8 _ nH tH.2.2.2.2.2.2.2.2.1]; exact v7
  · intro s hs hnt hsL hsH
    simp only [bflyTemps, List.mem_cons, List.not_mem_nil, not_or] at hnt
    obtain ⟨sx, sq, st, ss, swb, sd, se, -⟩ := hnt
    rw [f9 _ hs hsL, f8 _ hs se, f7 _ hs hsH, f6 _ hs sd, f5 _ hs swb, f4 _ hs ss,
      f3 _ hs st, f2 _ hs sq, f1 _ hs sx]

/-! ## 3. Slot names -/

theorem vN_toList (i : Nat) : (vN i).toList = 'v' :: (toString i).toList := by
  simp [vN, String.toList_append]

theorem twN_toList (j : Nat) : (twN j).toList = 't' :: 'w' :: (toString j).toList := by
  simp [twN, String.toList_append]

theorem qN_toList (i : Nat) : (qN i).toList = 'q' :: (toString i).toList := by
  simp [qN, String.toList_append]

theorem ne_of_head {s u : String} {c : Char} {t : List Char} (hs : s.toList = c :: t)
    (hu : (u.toList.head? != some c) = true) : s ≠ u := by
  rintro rfl; rw [hs] at hu; simp at hu

theorem vN_src (i : Nat) : ¬ isTmpName (vN i) := notTmp_of_headNe (vN_toList i) (by decide)
theorem twN_src (j : Nat) : ¬ isTmpName (twN j) := notTmp_of_headNe (twN_toList j) (by decide)
theorem qN_src (i : Nat) : ¬ isTmpName (qN i) := notTmp_of_headNe (qN_toList i) (by decide)

theorem toString_injective : Function.Injective (fun n : Nat => toString n) := by
  intro a b h
  exact repr_injective (by simpa [toString] using h)

theorem vN_inj {i k : Nat} (h : vN i = vN k) : i = k :=
  toString_injective ((String.append_right_inj "v").mp h)

theorem twN_inj {i k : Nat} (h : twN i = twN k) : i = k :=
  toString_injective ((String.append_right_inj "tw").mp h)

theorem qN_inj {i k : Nat} (h : qN i = qN k) : i = k :=
  toString_injective ((String.append_right_inj "q").mp h)

theorem vN_ne_twN (i j : Nat) : vN i ≠ twN j :=
  ne_of_head (vN_toList i) (by rw [twN_toList]; rfl)

theorem vN_ne_qN (i j : Nat) : vN i ≠ qN j :=
  ne_of_head (vN_toList i) (by rw [qN_toList]; rfl)

theorem twN_ne_qN (i j : Nat) : twN i ≠ qN j :=
  ne_of_head (twN_toList i) (by rw [qN_toList]; rfl)

theorem vN_notin (i : Nat) : vN i ∉ "mu" :: "p" :: bflyTemps := by
  simp only [bflyTemps, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact ne_of_head (vN_toList i) (by decide)

theorem twN_notin (j : Nat) : twN j ∉ "mu" :: "p" :: bflyTemps := by
  simp only [bflyTemps, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact ne_of_head (twN_toList j) (by decide)
    | (intro h; have := congrArg String.toList h; rw [twN_toList] at this; simp at this)

theorem bflyNames_of {lo hi : Nat} (h : lo ≠ hi) (t : Nat) : BflyNames lo hi (twN t) :=
  ⟨vN_src lo, vN_src hi, twN_src t, vN_notin lo, vN_notin hi, twN_notin t,
    fun e => h (vN_inj e), fun e => vN_ne_twN _ _ e.symm, fun e => vN_ne_twN _ _ e.symm⟩

/-! ## 4. Field values of the words -/

/-- The BabyBear field `ZMod p`, `p = 2013265921`. -/
abbrev BB := ZMod 2013265921

/-- A word encodes a field element: it is a canonical residue below `p` whose
value is that element. -/
def Enc (w : BitVec 64) (y : BB) : Prop := w.toNat < 2013265921 ∧ ((w.toNat : ℕ) : BB) = y

theorem enc_wbW {w b : BitVec 64} {yw yb : BB} (hw : Enc w yw) (hb : Enc b yb) :
    Enc (wbW w b) (yw * yb) := by
  refine ⟨?_, ?_⟩
  · rw [wbW_toNat w b hw.1 hb.1]; exact Nat.mod_lt _ (by norm_num)
  · rw [wbW_toNat w b hw.1 hb.1, ZMod.natCast_mod, Nat.cast_mul, hw.2, hb.2]

theorem enc_lo {a b w : BitVec 64} {ya yb yw : BB} (ha : Enc a ya) (hb : Enc b yb)
    (hw : Enc w yw) : Enc (fixW (a + wbW w b - bbP)) (ya + yw * yb) := by
  have hwb := enc_wbW hw hb
  refine ⟨?_, ?_⟩
  · rw [fixW_add a _ ha.1 hwb.1]; exact Nat.mod_lt _ (by norm_num)
  · rw [fixW_add a _ ha.1 hwb.1, ZMod.natCast_mod, Nat.cast_add, ha.2, hwb.2]

theorem enc_hi {a b w : BitVec 64} {ya yb yw : BB} (ha : Enc a ya) (hb : Enc b yb)
    (hw : Enc w yw) : Enc (fixW (a - wbW w b)) (ya - yw * yb) := by
  have hwb := enc_wbW hw hb
  refine ⟨?_, ?_⟩
  · rw [fixW_sub a _ ha.1 hwb.1]; exact Nat.mod_lt _ (by norm_num)
  · have hlt := hwb.1
    rw [fixW_sub a _ ha.1 hwb.1, ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add,
      ha.2, hwb.2, ZMod.natCast_self]
    ring

open CatCrypt.Crypto.Optimizer.Lattice.LayeredNtt (bupd)

/-- The environment holds `N` value slots `v0 …` encoding `Y`, `T` twiddle slots
`tw0 …` encoding `Tw`, and the constants `MU`, `p`. -/
structure FInv (N T : ℕ) (env : SEnvScalar) (Y Tw : ℕ → BB) : Prop where
  val : ∀ i, i < N → ∃ w, env (vN i) = some ⟨.sword 64, w⟩ ∧ Enc w (Y i)
  tw : ∀ j, j < T → ∃ w, env (twN j) = some ⟨.sword 64, w⟩ ∧ Enc w (Tw j)
  mu : env "mu" = some ⟨.sword 64, bbMU⟩
  p : env "p" = some ⟨.sword 64, bbP⟩

/-- One emitted butterfly moves the field values by `bupd`. -/
theorem finv_step {N T : ℕ} {env : SEnvScalar} {Y Tw : ℕ → BB} (hI : FInv N T env Y Tw)
    {lo hi t : ℕ} (hlo : lo < N) (hhi : hi < N) (hne : lo ≠ hi) (ht : t < T) :
    ∃ env', semScalar (seqL (butterflyStmts lo hi (twN t))) env = some env'
      ∧ FInv N T env' (bupd Tw Y (lo, hi, t)) Tw := by
  obtain ⟨a, hA, eA⟩ := hI.val lo hlo
  obtain ⟨b, hB, eB⟩ := hI.val hi hhi
  obtain ⟨w, hW, eW⟩ := hI.tw t ht
  obtain ⟨env', hrun, hH, hL, hfr⟩ :=
    butterfly_run lo hi (twN t) (bflyNames_of hne t) hA hB hW hI.mu hI.p
  have nmu : "mu" ∉ bflyTemps := by decide
  have np : "p" ∉ bflyTemps := by decide
  refine ⟨env', hrun, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro i hi'
    by_cases h1 : i = lo
    · subst h1
      exact ⟨_, hL, by simpa [bupd] using enc_lo eA eB eW⟩
    · by_cases h2 : i = hi
      · subst h2
        exact ⟨_, hH, by simpa [bupd, h1] using enc_hi eA eB eW⟩
      · obtain ⟨u, hU, eU⟩ := hI.val i hi'
        refine ⟨u, ?_, by simpa [bupd, h1, h2] using eU⟩
        rw [hfr _ (vN_src i) (fun h => vN_notin i (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ h)))
          (fun h => h1 (vN_inj h)) (fun h => h2 (vN_inj h))]
        exact hU
  · intro j hj
    obtain ⟨u, hU, eU⟩ := hI.tw j hj
    refine ⟨u, ?_, eU⟩
    rw [hfr _ (twN_src j) (fun h => twN_notin j (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ h)))
      (fun h => vN_ne_twN _ _ h.symm) (fun h => vN_ne_twN _ _ h.symm)]
    exact hU
  · rw [hfr _ (notTmp_of_head (by decide)) nmu (fun h => vN_notin lo (by rw [← h]; simp))
      (fun h => vN_notin hi (by rw [← h]; simp))]
    exact hI.mu
  · rw [hfr _ (notTmp_of_head (by decide)) np (fun h => vN_notin lo (by rw [← h]; simp))
      (fun h => vN_notin hi (by rw [← h]; simp))]
    exact hI.p

/-- The butterfly statements of a list of `(lo, hi, twiddle index)` triples. -/
def bflyStmtsOf (l : List (ℕ × ℕ × ℕ)) : List LowCT :=
  l.flatMap (fun q => butterflyStmts q.1 q.2.1 (twN q.2.2))

/-- A triple list is admissible for `N` values and `T` twiddles. -/
def PairsOk (N T : ℕ) (l : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ q ∈ l, q.1 < N ∧ q.2.1 < N ∧ q.1 ≠ q.2.1 ∧ q.2.2 < T

/-- A sequence of emitted butterflies moves the field values by the left fold of
`bupd`. -/
theorem finv_steps {N T : ℕ} {Tw : ℕ → BB} :
    ∀ (l : List (ℕ × ℕ × ℕ)) {env : SEnvScalar} {Y : ℕ → BB}, PairsOk N T l →
      FInv N T env Y Tw →
      ∃ env', semScalar (seqL (bflyStmtsOf l)) env = some env'
        ∧ FInv N T env' (l.foldl (bupd Tw) Y) Tw := by
  intro l
  induction l with
  | nil => intro env Y _ hI; exact ⟨env, semScalar_seqL_nil env, hI⟩
  | cons q l ih =>
    intro env Y hok hI
    obtain ⟨h1, h2, h3, h4⟩ := hok q (List.mem_cons_self ..)
    obtain ⟨e1, r1, i1⟩ := finv_step hI h1 h2 h3 h4
    obtain ⟨e2, r2, i2⟩ := ih (fun q' hq' => hok q' (List.mem_cons_of_mem _ hq')) i1
    refine ⟨e2, ?_, i2⟩
    simp only [bflyStmtsOf, List.flatMap_cons] at r2 ⊢
    rw [semScalar_seqL_append, r1, Option.bind_some]
    exact r2

/-- The output copies `q{i} := v{i}` over an index list. -/
def copyStmtsOf (l : List ℕ) : List LowCT :=
  l.map (fun i => .RScalarSetExpr (qN i) (.SVar (vN i)))

/-- The output copies leave in `q{i}` the value of `v{i}` and change no name outside
the copy destinations. -/
theorem copies_run {Y : ℕ → BB} {N : ℕ} :
    ∀ (l : List ℕ) {env : SEnvScalar}, l.Nodup → (∀ i ∈ l, i < N) →
      (∀ i, i < N → ∃ w, env (vN i) = some ⟨.sword 64, w⟩ ∧ Enc w (Y i)) →
      ∃ env', semScalar (seqL (copyStmtsOf l)) env = some env'
        ∧ (∀ s, ¬ isTmpName s → (∀ i ∈ l, s ≠ qN i) → env' s = env s)
        ∧ ∀ i ∈ l, ∃ w, env' (qN i) = some ⟨.sword 64, w⟩ ∧ Enc w (Y i) := by
  intro l
  induction l with
  | nil =>
    intro env _ _ _
    exact ⟨env, semScalar_seqL_nil env, fun _ _ _ => rfl, fun _ h => by simp at h⟩
  | cons c l ih =>
    intro env hnd hl hv
    obtain ⟨hcl, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨w, hw, ew⟩ := hv c (hl c (List.mem_cons_self ..))
    obtain ⟨e1, r1, v1, f1⟩ := setE_run (x := qN c) (env := env) (e := .SVar (vN c))
      (vN_src c) (by
        intro s hs; simp only [sexprVars, List.mem_cons, List.not_mem_nil, or_false] at hs
        subst hs; exact readU64_of hw)
    simp only [SExpr.evalBV, reader_of hw] at v1
    have hv1 : ∀ i, i < N → e1 (vN i) = env (vN i) := fun i _ =>
      f1 _ (vN_src i) (vN_ne_qN i c)
    obtain ⟨e2, r2, k2, q2⟩ := ih (env := e1) hnd'
      (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      (fun i hi => by rw [hv1 i hi]; exact hv i hi)
    refine ⟨e2, ?_, ?_, ?_⟩
    · simp only [copyStmtsOf, List.map_cons] at r2 ⊢
      rw [semScalar_seqL_cons r1]; exact r2
    · intro s hs hne
      rw [k2 s hs (fun i hi => hne i (List.mem_cons_of_mem _ hi)),
        f1 s hs (hne c (List.mem_cons_self ..))]
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · refine ⟨w, ?_, ew⟩
        rw [k2 _ (qN_src _) (fun j hj h => hcl (by rw [qN_inj h]; exact hj))]
        exact v1
      · exact q2 i hi

/-! ## 5. The front accepts the butterfly and copy statements -/

open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality

theorem upd_word {σ : NameTys} {x y : String} (h : σ y = some (.sword 64)) :
    σ.upd x (.sword 64) y = some (.sword 64) := by
  unfold NameTys.upd; split_ifs <;> simp_all

/-- The name-to-type map claims the value, twiddle and constant slots as words. -/
structure TyW (N T : ℕ) (σ : NameTys) : Prop where
  val : ∀ i, i < N → σ (vN i) = some (.sword 64)
  tw : ∀ j, j < T → σ (twN j) = some (.sword 64)
  mu : σ "mu" = some (.sword 64)
  p : σ "p" = some (.sword 64)

theorem TyW.mono {N T : ℕ} {σ σ' : NameTys} (h : TyW N T σ)
    (hm : ∀ y, σ y = some (.sword 64) → σ' y = some (.sword 64)) : TyW N T σ' :=
  ⟨fun i hi => hm _ (h.val i hi), fun j hj => hm _ (h.tw j hj), hm _ h.mu, hm _ h.p⟩

theorem butterfly_tt {N T lo hi t : ℕ} (hlo : lo < N) (hhi : hi < N) (ht : t < T)
    {σ : NameTys} (h : TyW N T σ) :
    ∃ σ', TransTotal σ (seqL (butterflyStmts lo hi (twN t))) σ'
      ∧ ∀ y, σ y = some (.sword 64) → σ' y = some (.sword 64) := by
  have hL := h.val lo hlo
  have hH := h.val hi hhi
  have hT := h.tw t ht
  have hmu := h.mu
  have hp := h.p
  have nx : ¬ isTmpName "x" := notTmp_of_head (by decide)
  have nq : ¬ isTmpName "q" := notTmp_of_head (by decide)
  have nt : ¬ isTmpName "t" := notTmp_of_head (by decide)
  have ns : ¬ isTmpName "s" := notTmp_of_head (by decide)
  have nwb : ¬ isTmpName "wb" := notTmp_of_head (by decide)
  have nd : ¬ isTmpName "d" := notTmp_of_head (by decide)
  have ne : ¬ isTmpName "e" := notTmp_of_head (by decide)
  have nmu : ¬ isTmpName "mu" := notTmp_of_head (by decide)
  have np : ¬ isTmpName "p" := notTmp_of_head (by decide)
  have nL := vN_src lo
  have nH := vN_src hi
  have nT := twN_src t
  have l0 : srcClean (.SLit 0) := litClean (by norm_num)
  have l30 : srcClean (.SLit 30) := litClean (by norm_num)
  have l32 : srcClean (.SLit 32) := litClean (by norm_num)
  have l63 : srcClean (.SLit 63) := litClean (by norm_num)
  refine ⟨((((((((σ.upd "x" (.sword 64)).upd "q" (.sword 64)).upd "t" (.sword 64)).upd "s"
    (.sword 64)).upd "wb" (.sword 64)).upd "d" (.sword 64)).upd (vN hi) (.sword 64)).upd "e"
    (.sword 64)).upd (vN lo) (.sword 64), ?_,
    fun y hy => upd_word (upd_word (upd_word (upd_word (upd_word (upd_word (upd_word
      (upd_word (upd_word hy))))))))⟩
  simp only [butterflyStmts, csubMask, seqL]
  refine .rSeq (.rScalarSetExpr _ _ nx ⟨nT, nH⟩ ?_) <| .rSeq (.rScalarSetExpr _ _ nq
    ⟨⟨⟨nx, l30⟩, nmu⟩, l32⟩ ?_) <| .rSeq (.rScalarSetExpr _ _ nt ⟨nx, ⟨nq, np⟩⟩ ?_) <|
    .rSeq (.rScalarSetExpr _ _ ns ⟨nt, np⟩ ?_) <| .rSeq (.rScalarSetExpr _ _ nwb
    ⟨ns, ⟨⟨l0, ⟨ns, l63⟩⟩, np⟩⟩ ?_) <| .rSeq (.rScalarSetExpr _ _ nd ⟨nL, nwb⟩ ?_) <|
    .rSeq (.rScalarSetExpr _ _ nH ⟨nd, ⟨⟨l0, ⟨nd, l63⟩⟩, np⟩⟩ ?_) <|
    .rSeq (.rScalarSetExpr _ _ ne ⟨⟨nL, nwb⟩, np⟩ ?_) <|
    .rSeq (.rScalarSetExpr _ _ nL ⟨ne, ⟨⟨l0, ⟨ne, l63⟩⟩, np⟩⟩ ?_) .rSkip
  all_goals
    intro y hy
    simp only [sexprVars, List.mem_cons, List.not_mem_nil, or_false, List.cons_append,
      List.nil_append] at hy
    repeat' (first | (rcases hy with rfl | hy) | (subst hy))
  all_goals (repeat (first | exact nameTys_upd_self _ _ _ | apply upd_word)); try assumption

theorem butterflies_tt {N T : ℕ} :
    ∀ (l : List (ℕ × ℕ × ℕ)) {σ : NameTys}, PairsOk N T l → TyW N T σ →
      ∃ σ', TransTotal σ (seqL (bflyStmtsOf l)) σ'
        ∧ ∀ y, σ y = some (.sword 64) → σ' y = some (.sword 64) := by
  intro l
  induction l with
  | nil => intro σ _ _; exact ⟨σ, .rSkip, fun _ h => h⟩
  | cons q l ih =>
    intro σ hok h
    obtain ⟨h1, h2, -, h4⟩ := hok q (List.mem_cons_self ..)
    obtain ⟨σ1, t1, m1⟩ := butterfly_tt h1 h2 h4 h
    obtain ⟨σ2, t2, m2⟩ := ih (fun q' hq' => hok q' (List.mem_cons_of_mem _ hq')) (h.mono m1)
    refine ⟨σ2, ?_, fun y hy => m2 _ (m1 _ hy)⟩
    simp only [bflyStmtsOf, List.flatMap_cons]
    exact transTotal_seqL_append t1 t2

theorem copies_tt {N : ℕ} :
    ∀ (l : List ℕ) {σ : NameTys}, (∀ i ∈ l, i < N) →
      (∀ i, i < N → σ (vN i) = some (.sword 64)) →
      ∃ σ', TransTotal σ (seqL (copyStmtsOf l)) σ'
        ∧ (∀ y, σ y = some (.sword 64) → σ' y = some (.sword 64))
        ∧ ∀ i ∈ l, σ' (qN i) = some (.sword 64) := by
  intro l
  induction l with
  | nil => intro σ _ _; exact ⟨σ, .rSkip, fun _ h => h, fun _ h => by simp at h⟩
  | cons c l ih =>
    intro σ hl hv
    have t1 : TransTotal σ (.RScalarSetExpr (qN c) (.SVar (vN c)))
        (σ.upd (qN c) (.sword 64)) :=
      .rScalarSetExpr _ _ (qN_src c) (vN_src c) (by
        intro y hy; simp only [sexprVars, List.mem_cons, List.not_mem_nil, or_false] at hy
        subst hy; exact hv c (hl c (List.mem_cons_self ..)))
    obtain ⟨σ2, t2, m2, q2⟩ := ih (σ := σ.upd (qN c) (.sword 64))
      (fun i hi => hl i (List.mem_cons_of_mem _ hi)) (fun i hi => upd_word (hv i hi))
    refine ⟨σ2, ?_, fun y hy => m2 _ (upd_word hy), ?_⟩
    · simp only [copyStmtsOf, List.map_cons, seqL] at t2 ⊢
      exact .rSeq t1 t2
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact m2 _ (nameTys_upd_self _ _ _)
      · exact q2 i hi

/-! ## 6. `seqAll` and `seqL` -/

theorem semScalar_seqAll : ∀ (l : List LowCT) (env : SEnvScalar),
    semScalar (seqAll l) env = semScalar (seqL l) env
  | [], _ => rfl
  | [c], env => by
      simp only [seqAll, seqL, semScalar]
      cases semScalar c env <;> rfl
  | c :: d :: l, env => by
      simp only [seqAll, seqL, semScalar]
      cases semScalar c env with
      | none => rfl
      | some e =>
        simp only [Option.bind_some]
        rw [semScalar_seqAll (d :: l) e]
        rfl

theorem transTotal_seqAll : ∀ (l : List LowCT) {σ σ' : NameTys},
    TransTotal σ (seqL l) σ' → TransTotal σ (seqAll l) σ'
  | [], _, _, h => h
  | [c], _, _, h => by
      cases h with
      | rSeq h1 h2 => cases h2; exact h1
  | c :: d :: l, _, _, h => by
      cases h with
      | rSeq h1 h2 => exact .rSeq h1 (transTotal_seqAll (d :: l) h2)

/-! ## 7. The deployed layer `plonky3_ntt_layer8_rc` on all inputs -/

open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl

/-- The four butterflies of the layer: pairs `(i, i+4)` with twiddle slot `i`. -/
def layerPairs : List (ℕ × ℕ × ℕ) := [(0, 4, 0), (1, 5, 1), (2, 6, 2), (3, 7, 3)]

theorem layerStmts_eq : layerStmts = bflyStmtsOf layerPairs := rfl

theorem outCopies_eq : outCopies = copyStmtsOf (List.range 8) := rfl

/-- The eighteen input names of the layer, in the order of `srcVM`. -/
def srcNames : List String :=
  ["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "tw0", "tw1", "tw2", "tw3",
   "mu", "p", "czero", "sh30", "sh32", "sh63"]

/-- The entry name-to-type map: every input name is a word. -/
def srcTys : NameTys := fun s => if s ∈ srcNames then some (.sword 64) else none

theorem srcTys_src : SrcTys srcTys := by
  intro x hx
  have hmem : x ∈ srcNames := by
    by_contra h; simp [srcTys, h] at hx
  have hh : ∀ y ∈ srcNames, (y.toList.headD '_' != '_') = true := by decide
  exact notTmp_of_head (hh x hmem)

theorem srcVM_lookup : ∀ y ∈ srcNames, (srcVM.lookup y).map (·.1) = some (.sword 64) := by
  decide

theorem srcTys_vmApprox : VmApprox srcTys srcVM := by
  intro x t hx
  have hmem : x ∈ srcNames := by
    by_contra h; simp [srcTys, h] at hx
  have ht : t = .sword 64 := by simp [srcTys, hmem] at hx; exact hx.symm
  subst ht
  have h := srcVM_lookup x hmem
  cases hl : srcVM.lookup x with
  | none => rw [hl] at h; simp at h
  | some p =>
    obtain ⟨t', v⟩ := p
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨v, hl⟩

theorem srcTys_tyW : TyW 8 4 srcTys := by
  have hv : ∀ i, i < 8 → vN i ∈ srcNames := by decide
  have ht : ∀ j, j < 4 → twN j ∈ srcNames := by decide
  exact ⟨fun i hi => by simp [srcTys, hv i hi], fun j hj => by simp [srcTys, ht j hj],
    by simp [srcTys, srcNames], by simp [srcTys, srcNames]⟩

/-- The input valuation of the layer: values `v 0 … v 7`, twiddles `tw 0 … tw 3`,
then the constants `MU, p, 0, 30, 32, 63`. -/
def layerVal (v tw : ℕ → BitVec 64) : Ctxt.Valuation (d := catCryptDialect) srcCtx :=
  .cons (v 0) (.cons (v 1) (.cons (v 2) (.cons (v 3) (.cons (v 4) (.cons (v 5)
    (.cons (v 6) (.cons (v 7) (.cons (tw 0) (.cons (tw 1) (.cons (tw 2) (.cons (tw 3)
    (.cons bbMU (.cons bbP (.cons (0 : BitVec 64) (.cons (30 : BitVec 64)
    (.cons (32 : BitVec 64) (.cons (63 : BitVec 64) .nil)))))))))))))))))

/-- The environment a valuation induces through `srcVM`. -/
def layerEnv (V : Ctxt.Valuation (d := catCryptDialect) srcCtx) : SEnvScalar :=
  fun s => (srcVM.lookup s).map (fun p => ⟨p.1, (toVIRVar p.2).lookup V⟩)

theorem layerEnv_v (v tw : ℕ → BitVec 64) :
    ∀ i, i < 8 → layerEnv (layerVal v tw) (vN i) = some ⟨.sword 64, v i⟩ := by
  intro i hi
  interval_cases i <;> rfl

theorem layerEnv_tw (v tw : ℕ → BitVec 64) :
    ∀ j, j < 4 → layerEnv (layerVal v tw) (twN j) = some ⟨.sword 64, tw j⟩ := by
  intro j hj
  interval_cases j <;> rfl

theorem layerEnv_mu (v tw : ℕ → BitVec 64) :
    layerEnv (layerVal v tw) "mu" = some ⟨.sword 64, bbMU⟩ := rfl

theorem layerEnv_p (v tw : ℕ → BitVec 64) :
    layerEnv (layerVal v tw) "p" = some ⟨.sword 64, bbP⟩ := rfl

theorem layerPairs_ok : PairsOk 8 4 layerPairs := by
  intro q hq
  simp only [layerPairs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> decide

/-- The front translates the layer body; its exit map claims every output copy as
a word. -/
theorem layerBody_tt : ∃ σ', TransTotal srcTys layerBody σ'
    ∧ ∀ i ∈ List.range 8, σ' (qN i) = some (.sword 64) := by
  obtain ⟨σ1, t1, m1⟩ := butterflies_tt (N := 8) (T := 4) layerPairs layerPairs_ok srcTys_tyW
  obtain ⟨σ2, t2, -, q2⟩ := copies_tt (N := 8) (List.range 8) (by simp)
    (fun i hi => m1 _ (srcTys_tyW.val i hi))
  refine ⟨σ2, ?_, q2⟩
  rw [layerBody, layerStmts_eq, outCopies_eq]
  exact transTotal_seqAll _ (transTotal_seqL_append t1 t2)

/-- **The deployed NTT layer on all inputs.** For canonical values `v 0 … v 7` and
twiddles `tw 0 … tw 3`, the front program capped at output copy `q j` exists,
lowers to `Com jasminDialect`, and returns a canonical word whose field value is
position `j` of the four butterflies `(i, i+4)` with twiddle `tw i` applied to the
field values of the inputs. -/
theorem layer_frontComAt_denote (v tw : ℕ → BitVec 64)
    (hv : ∀ i, i < 8 → (v i).toNat < 2013265921)
    (htw : ∀ j, j < 4 → (tw j).toNat < 2013265921) {j : ℕ} (hj : j < 8) :
    ∃ com, frontComAt (qN j) = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome
      ∧ Enc (com.denote (layerVal v tw))
          (layerPairs.foldl (bupd (fun k => ((tw k).toNat : BB)))
            (fun i => ((v i).toNat : BB)) j) := by
  obtain ⟨σ', htt, hq⟩ := layerBody_tt
  obtain ⟨o, htr, happ, hcont⟩ :=
    translateDialectControl_total htt srcVM srcTys_src srcTys_vmApprox
  obtain ⟨vq, hvq⟩ := happ (qN j) (.sword 64) (hq j (List.mem_range.mpr hj))
  obtain ⟨com, hcom, hlow⟩ := hcont (Com.ret (toVIRVar vq)) (by rfl)
  replace hcom : o.cont (Com.ret (toVIRVar vq)) = some com := hcom
  set V := layerVal v tw
  have hI : FInv 8 4 (layerEnv V) (fun i => ((v i).toNat : BB))
      (fun k => ((tw k).toNat : BB)) :=
    ⟨fun i hi => ⟨v i, layerEnv_v v tw i hi, hv i hi, rfl⟩,
     fun k hk => ⟨tw k, layerEnv_tw v tw k hk, htw k hk, rfl⟩,
     layerEnv_mu v tw, layerEnv_p v tw⟩
  obtain ⟨e1, r1, i1⟩ := finv_steps layerPairs layerPairs_ok hI
  obtain ⟨e2, r2, -, c2⟩ := copies_run (N := 8) (List.range 8) List.nodup_range (by simp)
    i1.val
  have hsem : semScalar layerBody (layerEnv V) = some e2 := by
    rw [layerBody, semScalar_seqAll, layerStmts_eq, outCopies_eq, semScalar_seqL_append, r1,
      Option.bind_some, r2]
  obtain ⟨V', hc', htail⟩ := translateDialectControl_denote htt.toIsCoveredS srcVM V
    (layerEnv V) e2 o (fun _ => rfl) htr hsem
  obtain ⟨com', hcom', hden⟩ := htail (Com.ret (toVIRVar vq))
  rw [hcom] at hcom'
  cases hcom'
  obtain ⟨w, hw, ew⟩ := c2 j (List.mem_range.mpr hj)
  refine ⟨com, ?_, hlow, ?_⟩
  · simp only [frontComAt, frontComOf, htr, hvq]; exact hcom
  · rw [hden, show (Com.ret (toVIRVar vq)).denote V' = (toVIRVar vq).lookup V' from rfl,
      ConsistentS.lookup_eq hc' hvq hw]
    exact ew

/-! ## 8. Butterfly-network kernels generated through the front -/

/-- Bind a list of word names, the first name at the head of the context. -/
def bindNames : (names : List String) → VarMap (List.replicate names.length (.sword 64))
  | [] => VarMap.empty
  | n :: ns => (bindNames ns).bind n

/-- A word valuation of a context of `names.length` words: word `k` is `g k`. -/
def valOfIdx : (names : List String) → (ℕ → BitVec 64) →
    Ctxt.Valuation (d := catCryptDialect) (List.replicate names.length (.sword 64))
  | [], _ => .nil
  | _ :: ns, g => .cons (g 0) (valOfIdx ns (fun k => g (k + 1)))

theorem bindNames_env : ∀ (names : List String) (g : ℕ → BitVec 64), names.Nodup →
    ∀ k (hk : k < names.length),
      ((bindNames names).lookup names[k]).map
          (fun p => (⟨p.1, (toVIRVar p.2).lookup (valOfIdx names g)⟩ : (t : CryptoTy) × ⟦t⟧))
        = some ⟨.sword 64, g k⟩ := by
  intro names
  induction names with
  | nil => intro _ _ k hk; simp at hk
  | cons n ns ih =>
    intro g hnd k hk
    obtain ⟨hn, hnd'⟩ := List.nodup_cons.mp hnd
    cases k with
    | zero => simp [bindNames, VarMap.bind]; rfl
    | succ k =>
      have hk' : k < ns.length := by simpa using hk
      have hne : ns[k] ≠ n := fun h => hn (h ▸ List.getElem_mem hk')
      have ih' := ih (fun k => g (k + 1)) hnd' k hk'
      simp only [List.getElem_cons_succ, bindNames, VarMap.bind, ite_eq_right hne]
      cases hl : (bindNames ns).lookup ns[k] with
      | none => rw [hl] at ih'; simp at ih'
      | some p =>
        rw [hl] at ih'
        obtain ⟨t, w⟩ := p
        exact ih'

/-- The input names of a kernel with `N` values and `T` twiddles. -/
def kInNames (N T : ℕ) : List String :=
  (List.range N).map vN ++ (List.range T).map twN ++ ["mu", "p"]

/-- The input context: one word per input name. -/
abbrev kCtx (N T : ℕ) : Ctx := List.replicate (kInNames N T).length (.sword 64)

/-- The kernel body: the butterflies of `l`, then the output copies `q{i} := v{i}`. -/
def kBody (N : ℕ) (l : List (ℕ × ℕ × ℕ)) : LowCT :=
  seqL (bflyStmtsOf l ++ copyStmtsOf (List.range N))

/-- The front program of the kernel, capped at slot `name`. -/
def kFrontAt (N T : ℕ) (l : List (ℕ × ℕ × ℕ)) (name : String) :
    Option (Com catCryptDialect (kCtx N T) (.sword 64)) :=
  match translateDialectControl (bindNames (kInNames N T)) (kBody N l) with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- Input word `k` of the kernel: values, then twiddles, then `MU`, `p`. -/
def kWord (N T : ℕ) (v tw : ℕ → BitVec 64) (k : ℕ) : BitVec 64 :=
  if k < N then v k else if k < N + T then tw (k - N) else if k = N + T then bbMU else bbP

/-- The input valuation of the kernel. -/
def kVal (N T : ℕ) (v tw : ℕ → BitVec 64) : Ctxt.Valuation (d := catCryptDialect) (kCtx N T) :=
  valOfIdx (kInNames N T) (kWord N T v tw)

theorem kInNames_nodup (N T : ℕ) : (kInNames N T).Nodup := by
  unfold kInNames
  refine List.Nodup.append (List.Nodup.append ?_ ?_ ?_) (by decide) ?_
  · exact List.Nodup.map (fun _ _ h => vN_inj h) List.nodup_range
  · exact List.Nodup.map (fun _ _ h => twN_inj h) List.nodup_range
  · simp only [List.disjoint_iff_ne, List.mem_map, List.mem_range]
    rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩; exact vN_ne_twN i j
  · simp only [List.disjoint_iff_ne, List.mem_append, List.mem_map, List.mem_range,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (⟨i, -, rfl⟩ | ⟨j, -, rfl⟩) _ (rfl | rfl)
    · exact fun h => vN_notin i (by rw [h]; simp)
    · exact fun h => vN_notin i (by rw [h]; simp)
    · exact fun h => twN_notin j (by rw [h]; simp)
    · exact fun h => twN_notin j (by rw [h]; simp)

/-- The environment a kernel valuation induces through the input `VarMap`. -/
def kEnv (N T : ℕ) (V : Ctxt.Valuation (d := catCryptDialect) (kCtx N T)) : SEnvScalar :=
  fun s => ((bindNames (kInNames N T)).lookup s).map (fun p => ⟨p.1, (toVIRVar p.2).lookup V⟩)

theorem kEnv_at (N T : ℕ) (v tw : ℕ → BitVec 64) (k : ℕ) (hk : k < (kInNames N T).length) :
    kEnv N T (kVal N T v tw) (kInNames N T)[k] = some ⟨.sword 64, kWord N T v tw k⟩ :=
  bindNames_env _ _ (kInNames_nodup N T) k hk

theorem kInNames_length (N T : ℕ) : (kInNames N T).length = N + T + 2 := by
  simp [kInNames]; omega

theorem kEnv_v (N T : ℕ) (v tw : ℕ → BitVec 64) (i : ℕ) (hi : i < N) :
    kEnv N T (kVal N T v tw) (vN i) = some ⟨.sword 64, v i⟩ := by
  have hk : i < (kInNames N T).length := by rw [kInNames_length]; omega
  have hn : (kInNames N T)[i] = vN i := by
    simp only [kInNames, List.append_assoc]
    rw [List.getElem_append_left (by simpa using hi)]
    simp
  have h := kEnv_at N T v tw i hk
  rw [hn] at h
  rw [h, kWord, ite_eq_left hi]

theorem kEnv_tw (N T : ℕ) (v tw : ℕ → BitVec 64) (j : ℕ) (hj : j < T) :
    kEnv N T (kVal N T v tw) (twN j) = some ⟨.sword 64, tw j⟩ := by
  have hk : N + j < (kInNames N T).length := by rw [kInNames_length]; omega
  have hn : (kInNames N T)[N + j] = twN j := by
    simp only [kInNames, List.append_assoc]
    rw [List.getElem_append_right (by simp)]
    rw [List.getElem_append_left (by simpa using hj)]
    simp
  have h := kEnv_at N T v tw (N + j) hk
  rw [hn] at h
  rw [h, kWord, ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem kEnv_mu (N T : ℕ) (v tw : ℕ → BitVec 64) :
    kEnv N T (kVal N T v tw) "mu" = some ⟨.sword 64, bbMU⟩ := by
  have hk : N + T < (kInNames N T).length := by rw [kInNames_length]; omega
  have hn : (kInNames N T)[N + T] = "mu" := by
    simp only [kInNames]
    rw [List.getElem_append_right (by simp)]
    simp
  have h := kEnv_at N T v tw (N + T) hk
  rw [hn] at h
  rw [h, kWord, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem kEnv_p (N T : ℕ) (v tw : ℕ → BitVec 64) :
    kEnv N T (kVal N T v tw) "p" = some ⟨.sword 64, bbP⟩ := by
  have hk : N + T + 1 < (kInNames N T).length := by rw [kInNames_length]; omega
  have hn : (kInNames N T)[N + T + 1] = "p" := by
    simp only [kInNames]
    rw [List.getElem_append_right (by simp)]
    simp
  have h := kEnv_at N T v tw (N + T + 1) hk
  rw [hn] at h
  rw [h, kWord, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The entry name-to-type map of a kernel: every input name is a word. -/
def kTys (N T : ℕ) : NameTys := fun s => if s ∈ kInNames N T then some (.sword 64) else none

theorem kTys_src (N T : ℕ) : SrcTys (kTys N T) := by
  intro x hx
  have hmem : x ∈ kInNames N T := by
    by_contra h; simp [kTys, h] at hx
  simp only [kInNames, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with (⟨i, -, rfl⟩ | ⟨j, -, rfl⟩) | rfl | rfl
  · exact vN_src i
  · exact twN_src j
  · exact notTmp_of_head (by decide)
  · exact notTmp_of_head (by decide)

theorem kTys_vmApprox (N T : ℕ) : VmApprox (kTys N T) (bindNames (kInNames N T)) := by
  intro x t hx
  have hmem : x ∈ kInNames N T := by
    by_contra h; simp [kTys, h] at hx
  have ht : t = .sword 64 := by simp [kTys, hmem] at hx; exact hx.symm
  subst ht
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hmem
  have h := bindNames_env _ (fun _ => 0) (kInNames_nodup N T) k hk
  cases hl : (bindNames (kInNames N T)).lookup (kInNames N T)[k] with
  | none => rw [hl] at h; simp at h
  | some p =>
    obtain ⟨t', w⟩ := p
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq, Sigma.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨w, hl⟩

theorem kTys_tyW (N T : ℕ) : TyW N T (kTys N T) := by
  refine ⟨fun i hi => ite_eq_left ?_, fun j hj => ite_eq_left ?_, ite_eq_left ?_, ite_eq_left ?_⟩
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))))
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))
  · exact List.mem_append.mpr (Or.inr (by simp))
  · exact List.mem_append.mpr (Or.inr (by simp))

/-- **A butterfly network generated through the front, on all inputs.** For any
admissible list `l` of butterflies over `N` values and `T` twiddles, canonical
values `v` and twiddles `tw`, the front program of the kernel capped at output copy
`q j` (`j < N`) exists, lowers to `Com jasminDialect`, and returns a canonical word
whose field value is position `j` of the butterflies of `l` applied in order to the
field values of the inputs. -/
theorem kFrontAt_denote (N T : ℕ) (l : List (ℕ × ℕ × ℕ)) (hl : PairsOk N T l)
    (v tw : ℕ → BitVec 64) (hv : ∀ i, i < N → (v i).toNat < 2013265921)
    (htw : ∀ j, j < T → (tw j).toNat < 2013265921) {j : ℕ} (hj : j < N) :
    ∃ com, kFrontAt N T l (qN j) = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome
      ∧ Enc (com.denote (kVal N T v tw))
          (l.foldl (bupd (fun k => ((tw k).toNat : BB))) (fun i => ((v i).toNat : BB)) j) := by
  obtain ⟨σ1, t1, m1⟩ := butterflies_tt l hl (kTys_tyW N T)
  obtain ⟨σ2, t2, -, q2⟩ := copies_tt (N := N) (List.range N) (by simp)
    (fun i hi => m1 _ ((kTys_tyW N T).val i hi))
  have htt : TransTotal (kTys N T) (kBody N l) σ2 := transTotal_seqL_append t1 t2
  obtain ⟨o, htr, happ, hcont⟩ :=
    translateDialectControl_total htt (bindNames (kInNames N T)) (kTys_src N T)
      (kTys_vmApprox N T)
  obtain ⟨vq, hvq⟩ := happ (qN j) (.sword 64) (q2 j (List.mem_range.mpr hj))
  obtain ⟨com, hcom, hlow⟩ := hcont (Com.ret (toVIRVar vq)) (by rfl)
  replace hcom : o.cont (Com.ret (toVIRVar vq)) = some com := hcom
  have hI : FInv N T (kEnv N T (kVal N T v tw)) (fun i => ((v i).toNat : BB))
      (fun k => ((tw k).toNat : BB)) :=
    ⟨fun i hi => ⟨v i, kEnv_v N T v tw i hi, hv i hi, rfl⟩,
     fun k hk => ⟨tw k, kEnv_tw N T v tw k hk, htw k hk, rfl⟩,
     kEnv_mu N T v tw, kEnv_p N T v tw⟩
  obtain ⟨e1, r1, i1⟩ := finv_steps l hl hI
  obtain ⟨e2, r2, -, c2⟩ := copies_run (N := N) (List.range N) List.nodup_range (by simp)
    i1.val
  have hsem : semScalar (kBody N l) (kEnv N T (kVal N T v tw)) = some e2 := by
    rw [kBody, semScalar_seqL_append, r1, Option.bind_some, r2]
  obtain ⟨V', hc', htail⟩ := translateDialectControl_denote htt.toIsCoveredS
    (bindNames (kInNames N T)) (kVal N T v tw)
    (kEnv N T (kVal N T v tw)) e2 o (fun _ => rfl) htr hsem
  obtain ⟨com', hcom', hden⟩ := htail (Com.ret (toVIRVar vq))
  rw [hcom] at hcom'
  cases hcom'
  obtain ⟨w, hw, ew⟩ := c2 j (List.mem_range.mpr hj)
  refine ⟨com, ?_, hlow, ?_⟩
  · simp only [kFrontAt, htr, hvq]; exact hcom
  · rw [hden, show (Com.ret (toVIRVar vq)).denote V' = (toVIRVar vq).lookup V' from rfl,
      ConsistentS.lookup_eq hc' hvq hw]
    exact ew

/-! ## 9. The deployed layer is the last Cooley–Tukey layer of the 8-point NTT -/

open CatCrypt.Crypto.Optimizer.Lattice.LayeredNtt
  (ctLayer layers bitrevInput nttPairs ctLayer_congr_lt foldl_layerPairs
   mem_nttPairs_bounds foldl_nttPairs foldl_bupd_congr_tw layers_congr layers_bitrev_eq_dft)
open CatCrypt.Crypto.Lattice.NTTRecursionPass (dft)
open CatCrypt.Crypto.Lattice.BitReversalGeneric (bitrevPerm)

theorem layerPairs_eq_layer :
    layerPairs = CatCrypt.Crypto.Optimizer.Lattice.LayeredNtt.layerPairs 3 2 := by
  decide

/-- **The deployed layer computes the last Cooley–Tukey layer of the 8-point NTT on
all inputs.** With twiddle words encoding `ω^0, …, ω^3`, output `j` encodes
`ctLayer 4 ω` of the input values at `j`: `Y j + ω^j·Y (j+4)` for `j < 4` and
`Y (j−4) − ω^(j−4)·Y j` otherwise. -/
theorem layer_frontComAt_ctLayer (v tw : ℕ → BitVec 64) (ω : BB)
    (hv : ∀ i, i < 8 → (v i).toNat < 2013265921)
    (htw : ∀ k, k < 4 → Enc (tw k) (ω ^ k)) {j : ℕ} (hj : j < 8) :
    ∃ com, frontComAt (qN j) = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome
      ∧ Enc (com.denote (layerVal v tw)) (ctLayer 4 ω (fun i => ((v i).toNat : BB)) j) := by
  obtain ⟨com, h1, h2, h3⟩ := layer_frontComAt_denote v tw hv (fun k hk => (htw k hk).1) hj
  refine ⟨com, h1, h2, ?_⟩
  have hfold : Plonky3NttLayerDenote.layerPairs.foldl (bupd (fun k => ((tw k).toNat : BB)))
      (fun i => ((v i).toNat : BB)) j = ctLayer 4 ω (fun i => ((v i).toNat : BB)) j := by
    rw [foldl_bupd_congr_tw (Tw' := fun k => ω ^ k) _ _ (by
      intro q hq
      simp only [Plonky3NttLayerDenote.layerPairs, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact (htw _ (by norm_num)).2)]
    rw [layerPairs_eq_layer, foldl_layerPairs 3 2 (by norm_num) ω _ (fun _ => rfl) _ j
      (by norm_num; omega)]
    norm_num
  rwa [hfold] at h3

/-- **The deployed layer finishes the 8-point DFT.** If the eight value words encode
the output of the first two layers of `ntt.rs` on the bit-reversed input `x`, the
twiddle words encode `ω^0, …, ω^3` and `ω^4 = −1`, then output `j` encodes the DFT
`Σ_i x_i ω^{ij}`. -/
theorem layer_frontComAt_dft (x : Fin (2 ^ 3) → BB) (ω : BB) (hω : ω ^ 4 = -1)
    (v tw : ℕ → BitVec 64)
    (hv : ∀ i, i < 8 → Enc (v i) (layers 3 ω 2 (bitrevInput 3 x) i))
    (htw : ∀ k, k < 4 → Enc (tw k) (ω ^ k)) (j : Fin (2 ^ 3)) :
    ∃ com, frontComAt (qN j) = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome
      ∧ Enc (com.denote (layerVal v tw)) (dft (2 ^ 3) ω x j) := by
  have hj : j.val < 8 := j.isLt
  obtain ⟨com, h1, h2, h3⟩ :=
    layer_frontComAt_ctLayer v tw ω (fun i hi => (hv i hi).1) htw hj
  refine ⟨com, h1, h2, ?_⟩
  have hc : ctLayer 4 ω (fun i => ((v i).toNat : BB)) j
      = ctLayer 4 ω (layers 3 ω 2 (bitrevInput 3 x)) j :=
    ctLayer_congr_lt 4 8 ω _ _ (by norm_num) (by norm_num) (fun i hi => (hv i hi).2) _ hj
  have hl : ctLayer 4 ω (layers 3 ω 2 (bitrevInput 3 x)) j
      = layers 3 ω 3 (bitrevInput 3 x) j := by
    simp only [layers]; norm_num
  rw [hc, hl, layers_bitrev_eq_dft 2 ω (by simpa using hω) x j] at h3
  exact h3

/-- The lowered layer exists, by the front's totality on the layer body. -/
theorem layerLoweredOpt_isSome' : layerLoweredOpt.isSome := by
  obtain ⟨com, h1, h2, -⟩ := layer_frontComAt_denote (fun _ => 0) (fun _ => 0)
    (fun _ _ => by decide) (fun _ _ => by decide) (j := 7) (by norm_num)
  simpa only [layerLoweredOpt, h1, Option.bind_some] using h2

/-- **The lowered jasmin-dialect layer on all inputs.** The lowering of the front
program capped at `q7` (the program `layerCom` names) returns output word `7` of the
layer, `Y 3 − ω^3·Y 7`, for twiddle words encoding `ω^0, …, ω^3`. -/
theorem layerLowered_denote (h : layerLoweredOpt.isSome) (v tw : ℕ → BitVec 64) (ω : BB)
    (hv : ∀ i, i < 8 → (v i).toNat < 2013265921)
    (htw : ∀ k, k < 4 → Enc (tw k) (ω ^ k)) :
    Enc ((layerLoweredOpt.get h).denote (DialectToJasminComCorrect.ctMapValD (layerVal v tw)))
      (ctLayer 4 ω (fun i => ((v i).toNat : BB)) 7) := by
  obtain ⟨com, h1, h2, h3⟩ := layer_frontComAt_ctLayer v tw ω hv htw (j := 7) (by norm_num)
  obtain ⟨jcom, hjc⟩ := Option.isSome_iff_exists.mp h2
  have hlc : layerLoweredOpt.get h = jcom := by
    have : layerLoweredOpt = some jcom := by
      simp only [layerLoweredOpt, h1, Option.bind_some, hjc]
    simp only [this, Option.get_some]
  have hden := DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq' com
    (layerVal v tw) jcom hjc
  rw [hlc]
  convert h3 using 1
  exact hden

/-- `layerLowered_denote` for `layerCom`, the program rendered as
`plonky3_ntt_layer8_rc`. -/
theorem layerCom_denote (v tw : ℕ → BitVec 64) (ω : BB)
    (hv : ∀ i, i < 8 → (v i).toNat < 2013265921)
    (htw : ∀ k, k < 4 → Enc (tw k) (ω ^ k)) :
    Enc (layerCom.denote (DialectToJasminComCorrect.ctMapValD (layerVal v tw)))
      (ctLayer 4 ω (fun i => ((v i).toNat : BB)) 7) :=
  layerLowered_denote layerLowered_isSome v tw ω hv htw

/-! ## 10. The generated `2^(e+1)`-point NTT kernel computes the DFT -/

/-- The butterflies of all `e + 1` layers of the `2^(e+1)`-point transform are
admissible for `2^(e+1)` values and `2^e` twiddles. -/
theorem nttPairs_ok (e : ℕ) : PairsOk (2 ^ (e + 1)) (2 ^ e) (nttPairs (e + 1) (e + 1)) := by
  intro q hq
  obtain ⟨h1, h2, h3, h4⟩ := mem_nttPairs_bounds le_rfl hq
  refine ⟨h1, h2, h3, ?_⟩
  rwa [pow_succ, Nat.mul_div_cancel _ (by norm_num)] at h4

/-- The front program of the `2^(e+1)`-point NTT kernel of `ntt.rs`, capped at slot
`name`: inputs the `2^(e+1)` values, the `2^e` twiddles, `MU` and `p`; body the
butterflies of all layers, then the output copies. -/
def nttKernelAt (e : ℕ) (name : String) :
    Option (Com catCryptDialect (kCtx (2 ^ (e + 1)) (2 ^ e)) (.sword 64)) :=
  kFrontAt (2 ^ (e + 1)) (2 ^ e) (nttPairs (e + 1) (e + 1)) name

/-- The value words of the kernel on input `x`, in bit-reversed order
(`ntt.rs::bit_reverse_permute`), `0` past the end. -/
def bitrevWords (n : ℕ) (x : Fin (2 ^ n) → BitVec 64) (i : ℕ) : BitVec 64 :=
  if hi : i < 2 ^ n then x ((bitrevPerm n) ⟨i, hi⟩) else 0

/-- **The generated NTT kernel computes the DFT on all inputs.** For `ω` with
`ω^(2^e) = −1` in BabyBear, canonical input words `x`, and twiddle words encoding
`ω^0, …, ω^(2^e − 1)`, the kernel front program capped at output copy `q k` exists,
lowers to `Com jasminDialect`, and on the bit-reversed input returns a canonical word
encoding `Σ_i x_i ω^{ik}`. -/
theorem nttKernelAt_dft (e : ℕ) (ω : BB) (hω : ω ^ (2 ^ e) = -1)
    (x : Fin (2 ^ (e + 1)) → BitVec 64) (hx : ∀ i, (x i).toNat < 2013265921)
    (tw : ℕ → BitVec 64) (htw : ∀ k, k < 2 ^ e → Enc (tw k) (ω ^ k))
    (k : Fin (2 ^ (e + 1))) :
    ∃ com, nttKernelAt e (qN k) = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome
      ∧ Enc (com.denote (kVal (2 ^ (e + 1)) (2 ^ e) (bitrevWords (e + 1) x) tw))
          (dft (2 ^ (e + 1)) ω (fun i => ((x i).toNat : BB)) k) := by
  have hv : ∀ i, i < 2 ^ (e + 1) → (bitrevWords (e + 1) x i).toNat < 2013265921 := by
    intro i hi; simp only [bitrevWords, dite_eq_left hi]; exact hx _
  obtain ⟨com, h1, h2, h3⟩ := kFrontAt_denote _ _ _ (nttPairs_ok e) (bitrevWords (e + 1) x) tw
    hv (fun j hj => (htw j hj).1) k.isLt
  refine ⟨com, h1, h2, ?_⟩
  have hok := nttPairs_ok e
  rw [foldl_bupd_congr_tw (Tw' := fun j => ω ^ j) _ _
      (fun q hq => (htw _ (hok q hq).2.2.2).2),
    foldl_nttPairs (e + 1) ω _ (fun _ => rfl) _ (e + 1) le_rfl _ k.isLt,
    layers_congr (e + 1) ω _ (bitrevInput (e + 1) (fun i => ((x i).toNat : BB)))
      (fun i hi => by simp [bitrevWords, bitrevInput, hi]) (e + 1) le_rfl _ k.isLt,
    layers_bitrev_eq_dft e ω hω] at h3
  exact h3

/-! ## 11. BabyBear roots of unity (`bb_root_of_unity`) -/

/-- Repeated squaring modulo `p`: `sqIter p k x = x^(2^k) mod p` on representatives. -/
def sqIter (p : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => sqIter p k (x * x % p)

theorem cast_pow_two_pow_sqIter (p : ℕ) : ∀ (k x : ℕ),
    ((x : ZMod p)) ^ (2 ^ k) = ((sqIter p k x : ℕ) : ZMod p) := by
  intro k
  induction k with
  | zero => intro x; simp [sqIter]
  | succ k ih =>
    intro x
    rw [pow_succ', pow_mul, sqIter, ← ih, ZMod.natCast_mod, Nat.cast_mul, sq]

/-- The BabyBear generator `31` is a quadratic non-residue: `31^((p−1)/2) = −1`. -/
theorem bbGen_pow_half : (31 : BB) ^ ((2013265921 - 1) / 2) = -1 := by
  have h : sqIter 2013265921 26 (31 ^ 15) = 2013265920 := by decide +kernel
  rw [show (2013265921 - 1) / 2 = 15 * 2 ^ 26 from rfl, pow_mul,
    show (31 : BB) ^ 15 = ((31 ^ 15 : ℕ) : BB) by push_cast; rfl,
    cast_pow_two_pow_sqIter, h]
  rfl

/-- `bb_root_of_unity(k) = 31^((p − 1) >> k)`, the root of unity of order `2^k` of
`plonky3-hax`. -/
def bbRoot (k : ℕ) : BB := (31 : BB) ^ ((2013265921 - 1) / 2 ^ k)

/-- For `1 ≤ k ≤ 27`, `bbRoot k ^ (2^(k−1)) = −1`, so `bbRoot k` is a primitive
`2^k`-th root of unity. -/
theorem bbRoot_pow_half (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 27) :
    bbRoot k ^ (2 ^ (k - 1)) = -1 := by
  have he : (2013265921 - 1) / 2 ^ k * 2 ^ (k - 1) = (2013265921 - 1) / 2 := by
    interval_cases k <;> norm_num
  rw [bbRoot, ← pow_mul, he, bbGen_pow_half]

/-- **The generated `2^k`-point BabyBear NTT kernel, `1 ≤ k ≤ 27`, with the root of
`bb_root_of_unity(k)`.** -/
theorem nttKernelAt_dft_bbRoot (e : ℕ) (he : e + 1 ≤ 27)
    (x : Fin (2 ^ (e + 1)) → BitVec 64) (hx : ∀ i, (x i).toNat < 2013265921)
    (tw : ℕ → BitVec 64) (htw : ∀ k, k < 2 ^ e → Enc (tw k) (bbRoot (e + 1) ^ k))
    (k : Fin (2 ^ (e + 1))) :
    ∃ com, nttKernelAt e (qN k) = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome
      ∧ Enc (com.denote (kVal (2 ^ (e + 1)) (2 ^ e) (bitrevWords (e + 1) x) tw))
          (dft (2 ^ (e + 1)) (bbRoot (e + 1)) (fun i => ((x i).toNat : BB)) k) :=
  nttKernelAt_dft e _ (by simpa using bbRoot_pow_half (e + 1) (by omega) he) x hx tw htw k

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerDenote
