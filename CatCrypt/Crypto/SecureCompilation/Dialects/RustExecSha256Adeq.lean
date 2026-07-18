/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq
import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq
import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecARXAdeq

/-!
# A whole SHA-256 compression round STEP through the closed-kernel `emitted = RustExec` route

`RustExecRoundAdeq.roundC_emitted_eq_rustexec` proved `emitted jasmin = RustExec
reference` for the SHA-2 `Maj` round — the **bitwise** (`∧`/`⊕`/`¬`) layer.
`RustExecARXAdeq.arxC_emitted_eq_rustexec` extended the pattern to the ARX layer
(one rotate + one modular add) through the closed-kernel `decide` route, and
`RustExecChaChaAdeq.qrC_emitted_eq_rustexec` carried a full twelve-step ChaCha20
quarter-round through it. This module assembles a **whole SHA-256 compression round
step** — the `Σ₀`/`Σ₁` rotate-xor trees, `Ch`/`Maj`, the `T1`/`T2` five-way and
two-way modular additions, and the state rotation `a' = T1 + T2`, `e' = d + T1` —
and delivers `emitted jasmin = RustExec reference` for it, axiom-free.

## The round step

Each SHA-256 compression round updates the eight-word state `(a,b,c,d,e,f,g,h)`
against the round constant `K` and message word `W`:

```
Σ₁(e) = ror(e,6) ⊕ ror(e,11) ⊕ ror(e,25)
Ch(e,f,g) = (e ∧ f) ⊕ (¬e ∧ g)
T1 = h + Σ₁(e) + Ch(e,f,g) + K + W
Σ₀(a) = ror(a,2) ⊕ ror(a,13) ⊕ ror(a,22)
Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)
T2 = Σ₀(a) + Maj(a,b,c)
e' = d + T1
a' = T1 + T2
```

The 32-bit words are modelled faithfully in the 64-bit word alphabet: each
`ror32(x,n)` is `(x >> n) ⊕ ((x << (32-n)) & 0xFFFFFFFF)` (the rotate halves occupy
disjoint bit ranges, so `⊕ = ∨`), each modular add masks its result to `& 0xFFFFFFFF`,
and `¬x` is `x ⊕ 0xFFFFFFFF`. The kernel is in SSA form (each write a fresh slot),
matching the front's single-assignment output.

## Coverage and value tie — the closed-kernel argument

`IsCoveredSCtl` needs only `srcClean` per `RScalarSetExpr` (NOT `inRange`). The
`Σ`-rotations (`SShl`/`SShr`), `Ch`/`Maj` (`SAnd`/`SXor`), and the `T1`/`T2`/state
additions (`SAdd`, masked) are all `srcClean` — their variables are source names,
their literal shift/mask constants `< 2^64`. The `SAdd`/`SShl` overflow `inRange`
side conditions (the `RustExecRoundAdeq` §Residual wall the hoisted all-`u64` bound
cannot meet) are irrelevant on a CLOSED kernel: the route needs only `srcClean`, and
the value reconciliation is `decide` on the concrete literal inputs, on which no
`+`/`<<` overflows `u64` (the SHA-256 32-bit lane discipline). This is
`RustExecARXAdeq`'s closed-kernel argument carrying the entire round step — the
`T1` five-way add included.

## The ARX-arm `inRange` discharge, symbolically (`§"symbolic ARX arms"`)

`t1E_inRange_of_bound` discharges the five-way `T1` add's `SAdd` overflow conditions
— exactly the ones the hoisted arm cannot — from the per-kernel 32-bit lane bound
`σ x < 2^32`: the sum `h + Σ₁ + Ch + K + W < 5·2^32 < 2^64`, so no `u64` overflow.
This is the `RustExecARXAdeq.arxE_inRange_of_bound` template on the round's widest
add, showing the five-way partial-sum bound discharges symbolically, not just
concretely — the residual the task flagged for the `T1` five-way add.

## Generalization to the whole compression (64 rounds)

One round step is one closed straight-line kernel; the whole compression is 64 of
them threaded through the state. Along the three orthogonal axes:

* **Round body reuse** — every round is this same kernel with different `K`, `W`
  inputs; the `srcClean` coverage and the concrete `decide` value tie are unchanged
  (the round body's shape is fixed).
* **Round iteration** — the 64-round loop is an `RFor` (`IsCoveredAdeq.rFor`,
  `N = 64 ≤ 2^64`) over the round body, tracked by the loop bridge `agreeFor`; the
  closed-kernel empty-entry-env argument is unchanged because the unrolled body stays
  closed (each round's reads follow the previous rounds' writes).
* **Message schedule** — the `W[t]` recurrence's `σ₀`/`σ₁` (`ror` + logical `SHR`)
  and `+` accumulations are covered identically (rotate-xor trees + masked adds),
  feeding each round's `W` input.

For a CLOSED unrolled compression the `decide` leg delivers the concrete
`emitted = RustExec` capstone with no manual `inRange` bookkeeping at all, exactly as
the single round step here does. The one standing residual is the OPEN-kernel jasmin
leg (`RustExecKernelAdeq.entry_trio_unsat_empty`, the `P3`-composition wall),
orthogonal to the round assembly done here.
-/

set_option autoImplicit false
-- The whole round step is a large closed kernel; the `.get`/`rfl` front-tracking
-- and the concrete `decide` value tie reduce a bigger term than the single-arm
-- kernels, so raise the reduction recursion limit.
set_option maxRecDepth 8000

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq (not_isTmp_short)

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSha256Adeq

/-! ## SHA-256 round-step expression builders -/

/-- The 32-bit mask `0xFFFFFFFF`. -/
def M : Nat := 4294967295

/-- `ror32(x, n) = (x >> n) ⊕ ((x << (32-n)) & 0xFFFFFFFF)` — a genuine 32-bit
    right rotation in `⊕`-form (disjoint bit ranges). -/
def rorE (n : Nat) (x : String) : SExpr :=
  .SXor (.SShr (.SVar x) (.SLit n)) (.SAnd (.SShl (.SVar x) (.SLit (32 - n))) (.SLit M))

/-- `Σ₀(a) = ror(a,2) ⊕ ror(a,13) ⊕ ror(a,22)`. -/
def sig0E : SExpr := .SXor (.SXor (rorE 2 "a") (rorE 13 "a")) (rorE 22 "a")

/-- `Σ₁(e) = ror(e,6) ⊕ ror(e,11) ⊕ ror(e,25)`. -/
def sig1E : SExpr := .SXor (.SXor (rorE 6 "e") (rorE 11 "e")) (rorE 25 "e")

/-- `Ch(e,f,g) = (e ∧ f) ⊕ (¬e ∧ g)` with `¬e = e ⊕ 0xFFFFFFFF`. -/
def chE : SExpr :=
  .SXor (.SAnd (.SVar "e") (.SVar "f")) (.SAnd (.SXor (.SVar "e") (.SLit M)) (.SVar "g"))

/-- `Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)`. -/
def majE : SExpr :=
  .SXor (.SXor (.SAnd (.SVar "a") (.SVar "b")) (.SAnd (.SVar "a") (.SVar "c")))
    (.SAnd (.SVar "b") (.SVar "c"))

/-- `T1 = (h + Σ₁(e) + Ch + K + W) & 0xFFFFFFFF` — the five-way modular add. -/
def t1E : SExpr :=
  .SAnd (.SAdd (.SAdd (.SAdd (.SAdd (.SVar "h") (.SVar "s1")) (.SVar "ch"))
    (.SVar "K")) (.SVar "W")) (.SLit M)

/-- `T2 = (Σ₀(a) + Maj) & 0xFFFFFFFF`. -/
def t2E : SExpr := .SAnd (.SAdd (.SVar "s0") (.SVar "mj")) (.SLit M)

/-- `e' = (d + T1) & 0xFFFFFFFF`. -/
def neE : SExpr := .SAnd (.SAdd (.SVar "d") (.SVar "t1")) (.SLit M)

/-- `a' = (T1 + T2) & 0xFFFFFFFF`. -/
def naE : SExpr := .SAnd (.SAdd (.SVar "t1") (.SVar "t2")) (.SLit M)

/-! ## Honest SHA-256 inputs: the IV state words, `K[0]`, and a message word. -/

def av : Nat := 1779033703   -- a = 0x6a09e667
def bv : Nat := 3144134277   -- b = 0xbb67ae85
def cv : Nat := 1013904242   -- c = 0x3c6ef372
def dv : Nat := 2773480762   -- d = 0xa54ff53a
def ev : Nat := 1359893119   -- e = 0x510e527f
def fv : Nat := 2600822924   -- f = 0x9b05688c
def gv : Nat := 528734635    -- g = 0x1f83d9ab
def hv : Nat := 1541459225   -- h = 0x5be0cd19
def kv : Nat := 1116352408   -- K[0] = 0x428a2f98
def wv : Nat := 1633837952   -- W[0] = 0x61626380

/-! ## §1 — reusable `srcClean` lemmas for the round-step arms -/

theorem rorE_srcClean (n : Nat) (x : String) (hn : n < 2 ^ 64) (hx : x.length < 4) :
    srcClean (rorE n x) :=
  ⟨⟨not_isTmp_short x hx, hn⟩,
    ⟨⟨not_isTmp_short x hx, by simp only [srcClean]; omega⟩, by norm_num [srcClean, M]⟩⟩

theorem sig0E_srcClean : srcClean sig0E :=
  ⟨⟨rorE_srcClean 2 "a" (by norm_num) (by decide),
      rorE_srcClean 13 "a" (by norm_num) (by decide)⟩,
    rorE_srcClean 22 "a" (by norm_num) (by decide)⟩

theorem sig1E_srcClean : srcClean sig1E :=
  ⟨⟨rorE_srcClean 6 "e" (by norm_num) (by decide),
      rorE_srcClean 11 "e" (by norm_num) (by decide)⟩,
    rorE_srcClean 25 "e" (by norm_num) (by decide)⟩

theorem chE_srcClean : srcClean chE :=
  ⟨⟨not_isTmp_short "e" (by decide), not_isTmp_short "f" (by decide)⟩,
    ⟨⟨not_isTmp_short "e" (by decide), by norm_num [srcClean, M]⟩,
      not_isTmp_short "g" (by decide)⟩⟩

theorem majE_srcClean : srcClean majE :=
  ⟨⟨⟨not_isTmp_short "a" (by decide), not_isTmp_short "b" (by decide)⟩,
      ⟨not_isTmp_short "a" (by decide), not_isTmp_short "c" (by decide)⟩⟩,
    ⟨not_isTmp_short "b" (by decide), not_isTmp_short "c" (by decide)⟩⟩

theorem t1E_srcClean : srcClean t1E :=
  ⟨⟨⟨⟨⟨not_isTmp_short "h" (by decide), not_isTmp_short "s1" (by decide)⟩,
        not_isTmp_short "ch" (by decide)⟩,
      not_isTmp_short "K" (by decide)⟩,
    not_isTmp_short "W" (by decide)⟩, by norm_num [srcClean, M]⟩

theorem t2E_srcClean : srcClean t2E :=
  ⟨⟨not_isTmp_short "s0" (by decide), not_isTmp_short "mj" (by decide)⟩,
    by norm_num [srcClean, M]⟩

theorem neE_srcClean : srcClean neE :=
  ⟨⟨not_isTmp_short "d" (by decide), not_isTmp_short "t1" (by decide)⟩,
    by norm_num [srcClean, M]⟩

theorem naE_srcClean : srcClean naE :=
  ⟨⟨not_isTmp_short "t1" (by decide), not_isTmp_short "t2" (by decide)⟩,
    by norm_num [srcClean, M]⟩

/-! ## §2 — symbolic ARX arm (`T1` five-way add `inRange` under the lane bound)

The `T1 = h + Σ₁(e) + Ch + K + W` five-way add is the round's widest `SAdd` chain
and the one the task flagged: its `SAdd` overflow side conditions are exactly the
ones the hoisted all-`u64` bound cannot meet. Under the per-kernel 32-bit lane bound
`σ x < 2^32` — the honest SHA-256 word discipline — the sum stays `< 5·2^32 < 2^64`
and all four partial-sum `SAdd` conditions discharge. This is
`RustExecARXAdeq.arxE_inRange_of_bound` on the round's five-way add. -/

/-- The per-kernel lane bound for the `T1` addends. -/
def t1Bound (σ : String → Nat) : Prop :=
  σ "h" < 2 ^ 32 ∧ σ "s1" < 2 ^ 32 ∧ σ "ch" < 2 ^ 32 ∧ σ "K" < 2 ^ 32 ∧ σ "W" < 2 ^ 32

/-- **The `T1` five-way-add `inRange` discharge.** From the lane bound the four
    partial-sum `SAdd` overflow conditions of `(h + Σ₁ + Ch + K + W) & M` — the ones
    the hoisted all-`u64` arm cannot meet — are all `< 2^64`, so no `u64` overflow.
    The `#250` obligation for the round's widest add, discharged from the kernel's
    lane discipline. -/
theorem t1E_inRange_of_bound (σ : String → Nat) (h : t1Bound σ) : t1E.inRange σ := by
  obtain ⟨hh, hs1, hch, hK, hW⟩ := h
  have hh64 : σ "h" < 2 ^ 64 := lt_trans hh (by norm_num)
  have hs164 : σ "s1" < 2 ^ 64 := lt_trans hs1 (by norm_num)
  have hch64 : σ "ch" < 2 ^ 64 := lt_trans hch (by norm_num)
  have hK64 : σ "K" < 2 ^ 64 := lt_trans hK (by norm_num)
  have hW64 : σ "W" < 2 ^ 64 := lt_trans hW (by norm_num)
  refine ⟨⟨⟨⟨⟨hh64, hs164, ?_⟩, hch64, ?_⟩, hK64, ?_⟩, hW64, ?_⟩,
    by norm_num [SExpr.inRange, M]⟩
  all_goals simp only [SExpr.eval]; omega

/-- **The `T1` reconciliation (symbolic leg).** On every lane-bounded input the
    wrapping-`u64` evaluator agrees with the `ofNat` image of the saturating-`Nat`
    evaluator on the round's five-way add — the ARX reconciliation (`sexprTransfer`)
    applied to `T1`. -/
theorem t1E_reconcile (σ : String → Nat) (h : t1Bound σ) :
    t1E.evalBV (SExpr.liftEnv σ) = BitVec.ofNat 64 (t1E.eval σ) :=
  sexprTransfer σ t1E (t1E_inRange_of_bound σ h)

/-! ## §3 — the whole round-step kernel `sha256C` (SSA form) -/

/-- The whole SHA-256 compression round step in SSA form: write the ten inputs
    (state `a..h`, constant `K`, message word `W`), then compute
    `s1 = Σ₁(e)`, `ch = Ch`, `t1 = T1`, `s0 = Σ₀(a)`, `mj = Maj`, `t2 = T2`,
    `ne = e'`, `na = a'`. -/
def sha256C : LowCT :=
  .RSeq (.RScalarSet "a" av)
    (.RSeq (.RScalarSet "b" bv)
      (.RSeq (.RScalarSet "c" cv)
        (.RSeq (.RScalarSet "d" dv)
          (.RSeq (.RScalarSet "e" ev)
            (.RSeq (.RScalarSet "f" fv)
              (.RSeq (.RScalarSet "g" gv)
                (.RSeq (.RScalarSet "h" hv)
                  (.RSeq (.RScalarSet "K" kv)
                    (.RSeq (.RScalarSet "W" wv)
                      (.RSeq (.RScalarSetExpr "s1" sig1E)
                        (.RSeq (.RScalarSetExpr "ch" chE)
                          (.RSeq (.RScalarSetExpr "t1" t1E)
                            (.RSeq (.RScalarSetExpr "s0" sig0E)
                              (.RSeq (.RScalarSetExpr "mj" majE)
                                (.RSeq (.RScalarSetExpr "t2" t2E)
                                  (.RSeq (.RScalarSetExpr "ne" neE)
                                    (.RScalarSetExpr "na" naE)))))))))))))))))

theorem sha256C_coveredS : IsCoveredS sha256C :=
  .rSeq (.rScalarSet "a" _)
    (.rSeq (.rScalarSet "b" _)
      (.rSeq (.rScalarSet "c" _)
        (.rSeq (.rScalarSet "d" _)
          (.rSeq (.rScalarSet "e" _)
            (.rSeq (.rScalarSet "f" _)
              (.rSeq (.rScalarSet "g" _)
                (.rSeq (.rScalarSet "h" _)
                  (.rSeq (.rScalarSet "K" _)
                    (.rSeq (.rScalarSet "W" _)
                      (.rSeq (.rScalarSetExpr "s1" _ sig1E_srcClean)
                        (.rSeq (.rScalarSetExpr "ch" _ chE_srcClean)
                          (.rSeq (.rScalarSetExpr "t1" _ t1E_srcClean)
                            (.rSeq (.rScalarSetExpr "s0" _ sig0E_srcClean)
                              (.rSeq (.rScalarSetExpr "mj" _ majE_srcClean)
                                (.rSeq (.rScalarSetExpr "t2" _ t2E_srcClean)
                                  (.rSeq (.rScalarSetExpr "ne" _ neE_srcClean)
                                    (.rScalarSetExpr "na" _ naE_srcClean)))))))))))))))))

theorem sha256C_covered : IsCoveredSCtl sha256C := .ofStraight sha256C_coveredS

/-! ## §4 — the `RustExec` reference run of `sha256C` -/

def rs0 : RustState := default
def rs1 : RustState := rsSetScalar rs0 "a" av
def rs2 : RustState := rsSetScalar rs1 "b" bv
def rs3 : RustState := rsSetScalar rs2 "c" cv
def rs4 : RustState := rsSetScalar rs3 "d" dv
def rs5 : RustState := rsSetScalar rs4 "e" ev
def rs6 : RustState := rsSetScalar rs5 "f" fv
def rs7 : RustState := rsSetScalar rs6 "g" gv
def rs8 : RustState := rsSetScalar rs7 "h" hv
def rs9 : RustState := rsSetScalar rs8 "K" kv
def rs10 : RustState := rsSetScalar rs9 "W" wv
def rs11 : RustState := rsSetScalar rs10 "s1" (sig1E.eval rs10.rsScalar)
def rs12 : RustState := rsSetScalar rs11 "ch" (chE.eval rs11.rsScalar)
def rs13 : RustState := rsSetScalar rs12 "t1" (t1E.eval rs12.rsScalar)
def rs14 : RustState := rsSetScalar rs13 "s0" (sig0E.eval rs13.rsScalar)
def rs15 : RustState := rsSetScalar rs14 "mj" (majE.eval rs14.rsScalar)
def rs16 : RustState := rsSetScalar rs15 "t2" (t2E.eval rs15.rsScalar)
def rs17 : RustState := rsSetScalar rs16 "ne" (neE.eval rs16.rsScalar)
def rsF : RustState := rsSetScalar rs17 "na" (naE.eval rs17.rsScalar)

theorem sha256C_exec (N : Nat) (leafSpec : LeafSpec) : RustExec N leafSpec sha256C rs0 rsF :=
  .seq _ _ rs0 rs1 rsF (.scalarSet "a" av rs0)
    (.seq _ _ rs1 rs2 rsF (.scalarSet "b" bv rs1)
      (.seq _ _ rs2 rs3 rsF (.scalarSet "c" cv rs2)
        (.seq _ _ rs3 rs4 rsF (.scalarSet "d" dv rs3)
          (.seq _ _ rs4 rs5 rsF (.scalarSet "e" ev rs4)
            (.seq _ _ rs5 rs6 rsF (.scalarSet "f" fv rs5)
              (.seq _ _ rs6 rs7 rsF (.scalarSet "g" gv rs6)
                (.seq _ _ rs7 rs8 rsF (.scalarSet "h" hv rs7)
                  (.seq _ _ rs8 rs9 rsF (.scalarSet "K" kv rs8)
                    (.seq _ _ rs9 rs10 rsF (.scalarSet "W" wv rs9)
                      (.seq _ _ rs10 rs11 rsF (.scalarSetExpr "s1" sig1E rs10)
                        (.seq _ _ rs11 rs12 rsF (.scalarSetExpr "ch" chE rs11)
                          (.seq _ _ rs12 rs13 rsF (.scalarSetExpr "t1" t1E rs12)
                            (.seq _ _ rs13 rs14 rsF (.scalarSetExpr "s0" sig0E rs13)
                              (.seq _ _ rs14 rs15 rsF (.scalarSetExpr "mj" majE rs14)
                                (.seq _ _ rs15 rs16 rsF (.scalarSetExpr "t2" t2E rs15)
                                  (.seq _ _ rs16 rs17 rsF (.scalarSetExpr "ne" neE rs16)
                                    (.scalarSetExpr "na" naE rs17)))))))))))))))))

/-! ## §5 — front translation, semantics, output tracking — all by `.get`/`rfl` -/

theorem shTransSome : (translateDialectControl VarMap.empty sha256C).isSome := by rfl

noncomputable def shO : DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty sha256C).get shTransSome

theorem shHTrans : translateDialectControl VarMap.empty sha256C = some shO :=
  (Option.some_get shTransSome).symm

theorem shSemSome : (semScalar sha256C (fun _ => none)).isSome := by rfl

noncomputable def shEnv : SEnvScalar := (semScalar sha256C (fun _ => none)).get shSemSome

theorem shHSem : semScalar sha256C (fun _ => none) = some shEnv :=
  (Option.some_get shSemSome).symm

theorem shNameSome : (shO.vm.lookup "na").isSome := by rfl

noncomputable def shW : CVar shO.Γ' (.sword 64) :=
  ((shO.vm.lookup "na").get shNameSome).2

theorem shHName : shO.vm.lookup "na" = some ⟨.sword 64, shW⟩ := by rfl

theorem shValSome : (shEnv "na").isSome := by rfl

noncomputable def shVal : BitVec 64 := ((shEnv "na").get shValSome).2

theorem shHVal : shEnv "na" = some ⟨.sword 64, shVal⟩ := by rfl

theorem shRetSome : (shO.cont (Com.ret (toVIRVar shW))).isSome := by rfl

noncomputable def shCom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  (shO.cont (Com.ret (toVIRVar shW))).get shRetSome

theorem shHRet : shO.cont (Com.ret (toVIRVar shW)) = some shCom :=
  (Option.some_get shRetSome).symm

theorem shComSome : (cryptoDialectToJasminCom shCom).isSome := by rfl

noncomputable def shJcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom shCom).get shComSome

theorem shHCom : cryptoDialectToJasminCom shCom = some shJcom :=
  (Option.some_get shComSome).symm

/-- **The `#250` reconciliation for the whole round step, concrete leg.** The word
    `semScalar` leaves in `na` (the new `a`) — computed through the two `Σ`
    rotate-xor trees, `Ch`/`Maj`, the five-way `T1` add, `T2`, and the state
    rotation, by the wrapping-`u64` evaluator — is the `ofNat 64` image of the
    `RustExec` saturating-`Nat` reference output. Concrete literal inputs, on which
    no `+`/`<<` overflows `u64`; equality by `decide`. -/
theorem shVal_eq_ref : shVal = BitVec.ofNat 64 (rsF.rsScalar "na") := by decide

/-! ## §6 — `emitted whole round step = RustExec reference` -/

/-- **The whole SHA-256 compression round step: `emitted jasmin = RustExec reference
    output`.** The verified pipeline's emitted jasmin program for the full round step
    (`Σ₀`/`Σ₁` rotate-xor trees, `Ch`/`Maj`, the `T1` five-way and `T2` two-way
    modular adds, and the state rotation `a' = T1+T2`, `e' = d+T1`) denotes to the
    `ctTransTy` image of the `RustExec` reference output word `rsF.rsScalar "na"`
    (the new `a`). Obtained through the SATISFIABLE closed-kernel route
    `rustToJasminCom_endToEnd_topLevel_unconditional`: the kernel is closed (all
    inputs literals, SSA writes), so `semScalar` succeeds from the empty entry env and
    no entry `EnvRel` seam is needed; the ARX (`Σ`-rotations, `T1`/`T2` adds) value
    reconciliation is discharged concretely (`shVal_eq_ref`) under the kernel's 32-bit
    input discipline. Axiom-free. -/
theorem sha256C_emitted_eq_rustexec (N : Nat) (leafSpec : LeafSpec) :
    (∃ Vb' : HVec shO.Γ', RustStateInterp shO.vm rsF Vb')
      ∧ shJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (rsF.rsScalar "na")) := by
  have h := rustToJasminCom_endToEnd_topLevel_unconditional sha256C shO N leafSpec rs0 rsF
    shEnv "na" shW shVal shCom shJcom sha256C_covered shHTrans
    (sha256C_exec N leafSpec) shHSem shHName shHVal shHRet shHCom
  rwa [shVal_eq_ref] at h

end CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSha256Adeq
