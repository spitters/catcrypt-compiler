/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
import all CatCrypt.Core.Code
import all CatCrypt.Crypto.CryptoWord
import all CatCrypt.Crypto.Jasmin.JasminAST
import all CatCrypt.Crypto.Jasmin.JasminTypes
import all CatCrypt.Crypto.Jasmin.LowCT
import all CatCrypt.Crypto.SDist
import all CatCrypt.Crypto.SecureCompilation.CryptoSSA
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore

public meta import CatCrypt.Crypto.MAYO.KernelFromRustcmdFrontEmit
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.MAYO.KernelFromRustcmdFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar

/-!
# `semScalar`-level GF(16) correctness of the front-authored MAYO quadform kernel

`MAYO.KernelFromRustcmdFrontEmit` front-compiles the GF(16) quadratic-form kernel
`mayo_quadform_n8_rc` (`out = Σ_{j,l} mat[j][l]·s[j]·s[l]` over `GF(2)[x]/(x⁴+x+1)`);
its provenance gates (`mayoBody_translates`, `frontJasmin_isSome`, `kernelAsm_isSome`)
pin the chain success and the rendered `.s`, and byte-identity to the schoolbook
reference was carried by the rustcmd C KAT `kernel_from_rustcmd_kat.c`.

This module carries the value model into Lean. The ascent correspondence
(`Ascent.Corres`, the `semScalar` forward simulation) proves that the front-authored
bit-serial `GF(16)` multiply `gfMul` **computes the value-model multiply**
`gf16mulBV` for every input, over the `BitVec 64` word algebra (`SRwordBV`); the
value model is then tied to the schoolbook reference `gf16mulN` (the C oracle) on
the whole `GF(16)` domain by the closed multiply table `gf16mulBV_fin`.

The word value leaf `corres_setExprWord` and the list-sequencing combinator
`corres_seqAll` come from the shared scalar scaffold `Ascent.CorresScalar`. The
bit-serial multiply mixes `SSub` (`negMask`) with the bitwise ops, so neither the
arithmetic nor the bitwise leaf alone covers it — the identity `BitVec 64`
abstraction of the whole `srcClean` fragment does.

Section 6 front-compiles the two-argument multiply kernel `res := x · y` over the
scalar entry context and welds the value model to its `Com.denote`
(`gfMulFrontCom_denote`, via `Ascent.corresScalar_frontDenote`). The quadform
kernel of `KernelFromRustcmdFrontEmit` reads and writes `.memref` arrays, whose
slots are outside the word relation `SRwordBV`; its `frontDenote = quadRefBV`
statement is the memref-`ConsistentS` seam.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4000

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.MAYO.KernelFromRustcmdFrontEmit
  (gfMul gfAccStep gfXtime negMask bitOf gf16mulN)

namespace CatCrypt.Crypto.MAYO.KernelEmitDenote

/-! ## 1. The GF(16) value model over `BitVec 64`

Each definition is the word-algebra image (`SExpr.evalBV`) of the corresponding
`SExpr` node the bit-serial `gfMul` emits. -/

/-- `0 − e` — the all-ones/zero mask of `e`'s low bit (`negMask`'s value). -/
def negMaskBV (e : BitVec 64) : BitVec 64 := (0 : BitVec 64) - e

/-- Bit `i` of `w` as a `{0,1}` word (`bitOf`'s value). -/
def bitOfBV (w : BitVec 64) (i : Nat) : BitVec 64 :=
  (w >>> (BitVec.ofNat 64 i).toNat) &&& BitVec.ofNat 64 1

/-- One `xtime` over `GF(2)[x]/(x⁴+x+1)` (`gfXtime`'s value): reduce by `x⁴=x+1`. -/
def gfXtime16BV (ga : BitVec 64) : BitVec 64 :=
  ((ga <<< (BitVec.ofNat 64 1).toNat) ^^^ (negMaskBV (bitOfBV ga 3) &&& BitVec.ofNat 64 3))
    &&& BitVec.ofNat 64 15

/-- One bit-serial accumulate step (`gfAccStep i`'s value). -/
def gf16AccBV (gr ga gb : BitVec 64) (i : Nat) : BitVec 64 :=
  gr ^^^ (ga &&& negMaskBV (bitOfBV gb i))

/-- The bit-serial `GF(16)` multiply value model: 4 accumulate steps interleaved
    with 3 `xtime`s, masked to a nibble — the word-algebra image of `gfMul`. -/
def gf16mulBV (va vb : BitVec 64) : BitVec 64 :=
  let ga0 := va &&& BitVec.ofNat 64 15
  let gb  := vb
  let gr1 := gf16AccBV (0 : BitVec 64) ga0 gb 0
  let ga1 := gfXtime16BV ga0
  let gr2 := gf16AccBV gr1 ga1 gb 1
  let ga2 := gfXtime16BV ga1
  let gr3 := gf16AccBV gr2 ga2 gb 2
  let ga3 := gfXtime16BV ga2
  let gr4 := gf16AccBV gr3 ga3 gb 3
  gr4 &&& BitVec.ofNat 64 15

/-! ## 2. `gfMul` as a `seqAll` list of `RScalarSetExpr` leaves -/

/-- The 11 straight-line leaves of the bit-serial `GF(16)` multiply, matching
    `gfMul dst aE bE` (`gfMul16_eq`). -/
def gfMul16List (dst : String) (aE bE : SExpr) : List LowCT :=
  [ .RScalarSetExpr "ga" (.SAnd aE (.SLit 15)),
    .RScalarSetExpr "gb" bE,
    .RScalarSetExpr "gr" (.SLit 0),
    gfAccStep 0, gfXtime, gfAccStep 1, gfXtime, gfAccStep 2, gfXtime, gfAccStep 3,
    .RScalarSetExpr dst (.SAnd (.SVar "gr") (.SLit 15)) ]

theorem gfMul16_eq (dst : String) (aE bE : SExpr) :
    gfMul dst aE bE = KernelFromRustcmdFrontEmit.seqAll (gfMul16List dst aE bE) := rfl

/-- The abstract step of `gfMul` — the left fold of the 11 leaf word steps. -/
def gfMulSem16 (dst : String) (aE bE : SExpr) : (String → BitVec 64) → (String → BitVec 64) :=
  fun a => List.foldl (fun acc f => f acc) a ((gfMul16List dst aE bE).map wordStep)

/-- Each leaf of `gfMul16List` is the word value leaf `corres_setExprWord`. -/
theorem gfMul16List_leaf (dst : String) (aE bE : SExpr)
    (haE : srcClean aE) (hbE : srcClean bE) :
    ∀ c ∈ gfMul16List dst aE bE, Corres SRwordBV (fun _ => True) (wordStep c) c := by
  intro c hc
  have hga : ¬ isTmpName "ga" := notTmp_of_short "ga" (by decide)
  have hgb : ¬ isTmpName "gb" := notTmp_of_short "gb" (by decide)
  have hgr : ¬ isTmpName "gr" := notTmp_of_short "gr" (by decide)
  simp only [gfMul16List] at hc
  fin_cases hc <;>
    (first
      | rw [wordStep_setExpr]
      | simp only [gfAccStep, gfXtime, wordStep_setExpr]) <;>
    exact corres_setExprWord _ _ (by
      try simp only [srcClean, negMask, bitOf]
      repeat' first
        | exact haE | exact hbE | exact hga | exact hgb | exact hgr
        | refine ⟨?_, ?_⟩ | decide)

/-- **`gfMul` realizes the value-model fold.** For every input abstraction `a`, the
    bit-serial `GF(16)` multiply `gfMul dst aE bE` refines the abstract step
    `gfMulSem16 dst aE bE` over the `BitVec 64` word algebra `SRwordBV`. -/
theorem gfMul16_corres (dst : String) (aE bE : SExpr)
    (haE : srcClean aE) (hbE : srcClean bE) :
    Corres SRwordBV (fun _ => True) (gfMulSem16 dst aE bE) (gfMul dst aE bE) := by
  rw [gfMul16_eq]
  exact corres_seqAll SRwordBV (gfMul16List dst aE bE)
    ((gfMul16List dst aE bE).map wordStep)
    (forall2_map_self _ wordStep _ (gfMul16List_leaf dst aE bE haE hbE))

/-! ## 3. Closed form of the fold read at `dst`

The second leaf stores `gb := bE` in the env after `ga` was set, so the fold reads
`bE` under an updated environment. When `bE` does not itself read the multiply's
scratch names `{ga, gb, gr}` — which the quadform's nibble arguments never do — the
value is the same as evaluating `bE` in the original environment. -/

/-- `e` does not read the multiply's scratch names `ga` / `gb` / `gr`. -/
def noScratch : SExpr → Prop
  | .SVar x => x ≠ "ga" ∧ x ≠ "gb" ∧ x ≠ "gr"
  | .SLit _ => True
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b | .SLt a b | .SAsr a b
  | .SMulS a b | .SMulHiS a b => noScratch a ∧ noScratch b
  | .SLimb _ _ => True

/-- Evaluating a `noScratch` expression is invariant under updating a scratch name. -/
theorem evalBV_upd_noScratch (nm : String) (hnm : nm = "ga" ∨ nm = "gb" ∨ nm = "gr")
    (v : BitVec 64) (a : String → BitVec 64) :
    ∀ e : SExpr, noScratch e →
      SExpr.evalBV (fun s => if s = nm then v else a s) e = SExpr.evalBV a e := by
  intro e
  induction e with
  | SVar x =>
      intro h
      have hx : x ≠ nm := by
        rcases hnm with h' | h' | h' <;> subst h' <;>
          first
            | exact h.1 | exact h.2.1 | exact h.2.2
      simp only [SExpr.evalBV, if_neg hx]
  | SLit n => intro _; rfl
  | SLimb v i => intro _; rfl
  | _ a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, iha h.1, ihb h.2]

/-- The value-model fold read at the destination name equals the closed-form
    multiply `gf16mulBV` of the two argument values. -/
theorem gfMul16_readout (dst : String) (aE bE : SExpr) (a : String → BitVec 64)
    (hbE : noScratch bE) :
    gfMulSem16 dst aE bE a dst = gf16mulBV (aE.evalBV a) (bE.evalBV a) := by
  have key : ∀ v : BitVec 64,
      SExpr.evalBV (fun s => if s = "ga" then v else a s) bE = SExpr.evalBV a bE :=
    fun v => evalBV_upd_noScratch "ga" (Or.inl rfl) v a bE hbE
  simp [gfMulSem16, gfMul16List, wordStep_setExpr, gfAccStep, gfXtime, negMask,
    bitOf, SExpr.evalBV, gf16mulBV, gf16AccBV, gfXtime16BV, negMaskBV, bitOfBV, key]

/-! ## 4. The value model equals the schoolbook reference `gf16mulN`

`gf16mulBV` masks `va` and reads only bits `0..3` of `vb`, so it depends only on
the low nibbles. On the whole `GF(16)` domain it agrees with the schoolbook
reference `gf16mulN` (the C oracle), checked by the closed 16×16 multiply table. -/

/-- The value model reads only the low nibble of each argument. -/
theorem gf16mulBV_mask (va vb : BitVec 64) :
    gf16mulBV va vb = gf16mulBV (va &&& 15) (vb &&& 15) := by
  unfold gf16mulBV gf16AccBV gfXtime16BV negMaskBV bitOfBV
  bv_decide

/-- The closed `GF(16)` multiply table: on every nibble pair the value model
    `gf16mulBV` equals the schoolbook `gf16mulN`. The small closed `GF(16)` table
    is discharged by `native_decide`. -/
theorem gf16mulBV_fin : ∀ a b : Fin 16,
    gf16mulBV (BitVec.ofNat 64 a.val) (BitVec.ofNat 64 b.val)
      = BitVec.ofNat 64 (gf16mulN a.val b.val) := by
  native_decide

/-- The value model equals the schoolbook `gf16mulN` on any nibble arguments. -/
theorem gf16mulBV_spec (va vb : BitVec 64) (hva : va.toNat < 16) (hvb : vb.toNat < 16) :
    gf16mulBV va vb = BitVec.ofNat 64 (gf16mulN va.toNat vb.toNat) := by
  have e1 : BitVec.ofNat 64 va.toNat = va :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt va.isLt])
  have e2 : BitVec.ofNat 64 vb.toNat = vb :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt vb.isLt])
  have h := gf16mulBV_fin ⟨va.toNat, hva⟩ ⟨vb.toNat, hvb⟩
  rw [e1, e2] at h
  exact h

/-! ## 5. `gfMul` computes the value-model multiply from any word environment -/

/-- **The front-authored `gfMul` computes `gf16mulBV`.** Running `gfMul dst aE bE`
    under `semScalar` from any environment `SRwordBV`-related to `a` succeeds and
    binds the destination word to the value-model multiply of the two argument
    values. With `gf16mulBV_fin` this ties `gfMul` to the schoolbook `gf16mulN`. -/
theorem gfMul16_computes (dst : String) (aE bE : SExpr)
    (haE : srcClean aE) (hbE : srcClean bE) (hbEns : noScratch bE)
    (hnd : ¬ isTmpName dst) (env : SEnvScalar) (a : String → BitVec 64)
    (hSR : SRwordBV env a) :
    ∃ env', semScalar (gfMul dst aE bE) env = some env' ∧
      env' dst = some ⟨.sword 64, gf16mulBV (aE.evalBV a) (bE.evalBV a)⟩ := by
  obtain ⟨env', hstep, hSR'⟩ := gfMul16_corres dst aE bE haE hbE env a hSR trivial
  refine ⟨env', hstep, ?_⟩
  rw [hSR' dst hnd, gfMul16_readout dst aE bE a hbEns]

/-! ## 6. The front-compiled two-argument multiply kernel

`gfMul` on the two source names `x`, `y` is a scalar kernel: the entry context is
two `.sword 64` slots, and the front `translateDialectControl` compiles it to a
`Com catCryptDialect` returning the product word. The word state relation
`SRwordBV` constrains every non-temp name, so the entry `VarMap` consistent with
that relation resolves every name: `x` at the head slot, every other name at the
tail slot. -/

/-- Entry context of the multiply kernel: the two argument words. -/
def gfMulΓ : Ctx := [.sword 64, .sword 64]

/-- Entry `VarMap`: `x` at the head slot, every other name at the tail slot. -/
def gfMulVM : VarMap gfMulΓ :=
  { lookup := fun n =>
      if n = "x" then some ⟨.sword 64, .here⟩ else some ⟨.sword 64, .there .here⟩ }

/-- Entry valuation: `vx` in the head slot, `vy` in the tail slot. -/
def gfMulVal (vx vy : BitVec 64) : Ctxt.Valuation (d := catCryptDialect) gfMulΓ :=
  .cons vx (.cons vy .nil)

/-- Entry scalar environment: the valuation read through `gfMulVM`. -/
def gfMulEnv (vx vy : BitVec 64) : SEnvScalar :=
  fun s => some ⟨.sword 64, if s = "x" then vx else vy⟩

/-- Entry word abstraction: `x ↦ vx`, every other name `↦ vy`. -/
def gfMulAbs (vx vy : BitVec 64) : String → BitVec 64 := fun s => if s = "x" then vx else vy

/-- The front-compiled multiply kernel `res := x · y`: `gfMul` pushed through
    `translateDialectControl` and capped with `ret res`. -/
def gfMulFrontCom : Option (Com catCryptDialect gfMulΓ (.sword 64)) :=
  match translateDialectControl gfMulVM (gfMul "res" (.SVar "x") (.SVar "y")) with
  | some o =>
      match o.vm.lookup "res" with
      | some ⟨.sword 64, w⟩ => o.cont (Com.ret (toVIRVar w))
      | _ => none
  | none => none

/-- The front accepts the multiply kernel. -/
theorem gfMulFrontCom_isSome : gfMulFrontCom.isSome := by rfl

/-- The multiply body is in the covered scalar control fragment. -/
theorem gfMul16_coveredSCtl (dst : String) (aE bE : SExpr)
    (haE : srcClean aE) (hbE : srcClean bE) :
    IsCoveredSCtl (gfMul dst aE bE) := by
  have hga : ¬ isTmpName "ga" := notTmp_of_short "ga" (by decide)
  have hgb : ¬ isTmpName "gb" := notTmp_of_short "gb" (by decide)
  have hgr : ¬ isTmpName "gr" := notTmp_of_short "gr" (by decide)
  refine .ofStraight ?_
  simp only [KernelFromRustcmdFrontEmit.gfMul, gfAccStep, gfXtime, negMask, bitOf]
  repeat' first
    | apply IsCoveredS.rSeq
    | (apply IsCoveredS.rScalarSetExpr
       try simp only [srcClean]
       repeat' first
         | exact haE | exact hbE | exact hga | exact hgb | exact hgr
         | refine ⟨?_, ?_⟩ | decide)

/-- The entry environment is consistent with the entry valuation. -/
theorem gfMulEnv_consistent (vx vy : BitVec 64) :
    ConsistentS gfMulVM (gfMulVal vx vy) (gfMulEnv vx vy) := by
  intro s
  by_cases hs : s = "x" <;> simp only [gfMulVM, gfMulEnv, gfMulVal, hs, if_pos] <;> rfl

/-- The entry environment is word-related to the entry abstraction. -/
theorem gfMulEnv_SR (vx vy : BitVec 64) : SRwordBV (gfMulEnv vx vy) (gfMulAbs vx vy) :=
  fun _ _ => rfl

/-- **The front-compiled multiply kernel denotes the value model.** On the entry
    valuation binding the two argument words, the emitted `Com`'s denotation is the
    `GF(16)` value-model product `gf16mulBV vx vy`. The `Corres` result
    `gfMul16_corres` is carried into the emitted program by
    `Ascent.corresScalar_frontDenote`. -/
theorem gfMulFrontCom_denote (vx vy : BitVec 64)
    (com : Com catCryptDialect gfMulΓ (.sword 64)) (hcom : gfMulFrontCom = some com) :
    com.denote (gfMulVal vx vy) = gf16mulBV vx vy := by
  have hx : srcClean (.SVar "x") := notTmp_of_short "x" (by decide)
  have hy : srcClean (.SVar "y") := notTmp_of_short "y" (by decide)
  have hres : ¬ isTmpName "res" := notTmp_of_short "res" (by decide)
  rw [gfMulFrontCom] at hcom
  split at hcom
  · next o htr =>
      split at hcom
      · next w hw =>
          have hden := corresScalar_frontDenote
            (gfMul16_coveredSCtl "res" (.SVar "x") (.SVar "y") hx hy)
            (gfMul16_corres "res" (.SVar "x") (.SVar "y") hx hy)
            gfMulVM (gfMulVal vx vy) (gfMulEnv vx vy) (gfMulAbs vx vy)
            (gfMulEnv_consistent vx vy) (gfMulEnv_SR vx vy) o htr "res" hres w hw com hcom
          rw [hden, gfMul16_readout "res" (.SVar "x") (.SVar "y") (gfMulAbs vx vy)
            ⟨by decide, by decide, by decide⟩]
          simp [SExpr.evalBV, gfMulAbs]
      · exact absurd hcom (by simp)
  · exact absurd hcom (by simp)

/-- **The front-compiled multiply kernel denotes the schoolbook `GF(16)`
    product.** On nibble arguments the emitted `Com` denotes
    `gf16mulN` — the reference the C oracle computes. -/
theorem gfMulFrontCom_denote_gf16mulN (vx vy : BitVec 64)
    (hvx : vx.toNat < 16) (hvy : vy.toNat < 16)
    (com : Com catCryptDialect gfMulΓ (.sword 64)) (hcom : gfMulFrontCom = some com) :
    com.denote (gfMulVal vx vy) = BitVec.ofNat 64 (gf16mulN vx.toNat vy.toNat) := by
  rw [gfMulFrontCom_denote vx vy com hcom, gf16mulBV_spec vx vy hvx hvy]

/-- **The emitted multiply kernel computes the schoolbook `GF(16)` product.** The
    front-compiled program exists and, on nibble arguments, its denotation is
    `gf16mulN` — the reference the C oracle computes. -/
theorem gfMulFrontCom_map_denote (vx vy : BitVec 64)
    (hvx : vx.toNat < 16) (hvy : vy.toNat < 16) :
    gfMulFrontCom.map (fun com => com.denote (gfMulVal vx vy))
      = some (BitVec.ofNat 64 (gf16mulN vx.toNat vy.toNat)) := by
  obtain ⟨com, hcom⟩ := Option.isSome_iff_exists.mp gfMulFrontCom_isSome
  rw [hcom, Option.map_some, gfMulFrontCom_denote_gf16mulN vx vy hvx hvy com hcom]

end CatCrypt.Crypto.MAYO.KernelEmitDenote
