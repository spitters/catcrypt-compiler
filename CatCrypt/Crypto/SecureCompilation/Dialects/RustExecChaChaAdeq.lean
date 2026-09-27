/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

-- The closed-kernel route reduces the front (`translateDialectControl`,
-- `semScalar`, `cryptoDialectToJasminCom`) by `rfl`/`decide`; under the module
-- system that reduction needs the front closure imported with `all`, and
-- `Nat.repr` (the front's slot names) exposed through `Init.Data.Repr`.
import all Init.Data.Repr
import all CatCrypt.Core.Code
import all CatCrypt.Crypto.CryptoWord
import all CatCrypt.Crypto.Jasmin.JasminAST
import all CatCrypt.Crypto.Jasmin.JasminTypes
import all CatCrypt.Crypto.Jasmin.LowCTExec
import all CatCrypt.Crypto.SDist
import all CatCrypt.Crypto.SecureCompilation.CryptoSSA
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecARXAdeq

/-!
# A real ChaCha20 quarter-round through the closed-kernel `emitted = RustExec` route

`RustExecRoundAdeq.roundC_emitted_eq_rustexec` proves `emitted jasmin = RustExec
reference` for the SHA-2 `Maj` round — the **bitwise** (`∧`/`⊕`/`¬`) layer, whose
`inRange` obligation holds for ALL `u64` inputs with no side condition. This module
applies the same closed-kernel route to the ChaCha20 quarter-round, whose 32-bit
add and rotate arms satisfy `inRange` under a per-kernel lane bound `σ x < 2^32`.

## The quarter-round

ChaCha20's core mixing step on four 32-bit words `a, b, c, d`:

```
a += b;  d ^= a;  d = rotl32(d, 16);
c += d;  b ^= c;  b = rotl32(b, 12);
a += b;  d ^= a;  d = rotl32(d,  8);
c += d;  b ^= c;  b = rotl32(b,  7);
```

Four modular additions (`+= mod 2^32`), four XORs, four 32-bit rotations.

## Two kernels

* **`qrXorC` — the bitwise XOR sub-part (`d ^= a; b ^= c`), axiom-free.** The two
  XOR steps are purely bitwise, so — exactly like `Maj` — their covered-fragment
  `inRange` obligation holds for ALL `u64` inputs with **no** side condition. This
  kernel lies in the STRONG `IsCoveredAdeq` fragment (`.rScalarSetExpr` with the
  hoisted all-`u64` `inRange`) and yields `emitted = RustExec` through the
  closed-kernel `topLevel_unconditional` route, axiom-free — the bitwise fragment,
  identical to `RustExecRoundAdeq`.

* **`qrC` — the full quarter-round, through the ARX closed-kernel route.** The
  `+=` and `rotl32` steps are the ARX layer: `SAdd` and `SShl` hit an input-dependent
  overflow condition that the hoisted all-`u64` bound cannot discharge (see
  `RustExecRoundAdeq` §Scope). For a CLOSED kernel this is irrelevant — the
  route needs only `IsCoveredSCtl` (whose `RScalarSetExpr` arm asks for `srcClean`,
  NOT `inRange`) and the value reconciliation is `decide` on the concrete literal
  inputs, on which no `+`/`<<` overflows `u64`. The closed-kernel argument carries
  the entire twelve-step quarter-round.

The 32-bit words are modelled faithfully: each `+=` masks to `& 0xFFFFFFFF`, each
`rotl32(x,n)` is `((x << n) & 0xFFFFFFFF) ^ (x >> (32-n))` (the rotate halves occupy
disjoint bit ranges, so `⊕ = ∨`). The kernel is in SSA form (each write a fresh
slot `a0,a1,…`), matching the front's own single-assignment output, so no in-place
rebinding is needed.

## The reusable ARX arm, instantiated on ChaCha (`§"symbolic ARX arms"`)

`addE_inRange_of_bound` / `rotlE_inRange_of_bound` discharge the `SAdd`/`SShl`
overflow side conditions the hoisted arm cannot, from the per-kernel 32-bit lane
bound `σ x < 2^32`. `qrAdd_reconcile` / `qrRotl_reconcile`
then feed them to `RustExecSemScalarBridge.sexprTransfer` to get the wrapping-`u64`
evaluator = `ofNat` image of the saturating-`Nat` evaluator on every lane-bounded
input — showing the ChaCha ARX arms reconcile symbolically, not just concretely.

## Scope

The full-quarter-round `emitted = RustExec` (`qrC_emitted_eq_rustexec`) routes
through the closed-kernel argument, as the ARX layer requires (the general open-kernel
jasmin leg meets `RustExecKernelAdeq.entry_trio_unsat_empty`). The symbolic ARX arms
(`§"symbolic ARX arms"`) reconcile the `semScalar` value with the `RustExec` value
for ChaCha's add/rotate; fusing that with the jasmin denotation leg for an OPEN
quarter-round (the end-to-end composition of `RustExecSemScalarBridge`) is outside
this module.
-/

@[expose] public section

set_option autoImplicit false
-- The full twelve-step quarter-round is a 16-statement closed kernel; the
-- `by rfl` front/lowering reductions and the `decide` value tie recurse deeper
-- than the default kernel-reduction depth.
set_option maxRecDepth 100000

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

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RustExecChaChaAdeq

/-! ## ChaCha expression builders -/

/-- The 32-bit mask `0xFFFFFFFF`. -/
def M : Nat := 4294967295

/-- `x += y` in 32-bit: `(x + y) & 0xFFFFFFFF`. -/
def addE (x y : String) : SExpr := .SAnd (.SAdd (.SVar x) (.SVar y)) (.SLit M)

/-- `x ^= y`: bitwise XOR (no mask needed — operands stay in their 32-bit lane). -/
def xorE (x y : String) : SExpr := .SXor (.SVar x) (.SVar y)

/-- `rotl32(x, n) = ((x << n) & 0xFFFFFFFF) ^ (x >> (32-n))`. -/
def rotlE (n : Nat) (x : String) : SExpr :=
  .SXor (.SAnd (.SShl (.SVar x) (.SLit n)) (.SLit M)) (.SShr (.SVar x) (.SLit (32 - n)))

/-- ChaCha20 sigma constants (`"expand 32-byte k"`), the 32-bit inputs. -/
def av : Nat := 1634760805   -- 0x61707865
def bv : Nat := 857760878    -- 0x3320646e
def cv : Nat := 2036477234   -- 0x79622d32
def dv : Nat := 1797285228   -- 0x6b206574

/-! ## §1 — The bitwise XOR sub-kernel `qrXorC` (axiom-free)

The two XOR steps `d ^= a; b ^= c` of the quarter-round, isolated over concrete
inputs. Purely bitwise, so — exactly like `Maj` — the `inRange` obligation is the
hoisted all-`u64` one with no side condition. Lands in `IsCoveredAdeq`. -/

/-- `dx := d ^ a`. -/
def dxE : SExpr := xorE "d0" "a0"
/-- `bx := b ^ c`. -/
def bxE : SExpr := xorE "b0" "c0"

/-- The bitwise sub-kernel: write the four inputs, then the two XOR steps into
    fresh SSA slots `dx`, `bx`. -/
def qrXorC : LowCT :=
  .RSeq (.RScalarSet "a0" av)
    (.RSeq (.RScalarSet "b0" bv)
      (.RSeq (.RScalarSet "c0" cv)
        (.RSeq (.RScalarSet "d0" dv)
          (.RSeq (.RScalarSetExpr "dx" dxE)
            (.RScalarSetExpr "bx" bxE)))))

theorem dxE_srcClean : srcClean dxE :=
  ⟨not_isTmp_short "d0" (by decide), not_isTmp_short "a0" (by decide)⟩

theorem bxE_srcClean : srcClean bxE :=
  ⟨not_isTmp_short "b0" (by decide), not_isTmp_short "c0" (by decide)⟩

theorem dxE_inRange : ∀ σ : String → Nat, (∀ y, σ y < 2 ^ 64) → dxE.inRange σ :=
  fun _σ h => ⟨h "d0", h "a0"⟩

theorem bxE_inRange : ∀ σ : String → Nat, (∀ y, σ y < 2 ^ 64) → bxE.inRange σ :=
  fun _σ h => ⟨h "b0", h "c0"⟩

theorem qrXorC_adeqS : IsCoveredAdeqS qrXorC :=
  .rSeq (.rScalarSet "a0" (by norm_num [av]))
    (.rSeq (.rScalarSet "b0" (by norm_num [bv]))
      (.rSeq (.rScalarSet "c0" (by norm_num [cv]))
        (.rSeq (.rScalarSet "d0" (by norm_num [dv]))
          (.rSeq (.rScalarSetExpr "dx" dxE dxE_srcClean dxE_inRange)
            (.rScalarSetExpr "bx" bxE bxE_srcClean bxE_inRange)))))

theorem qrXorC_adeq : IsCoveredAdeq qrXorC := .ofStraight qrXorC_adeqS

theorem qrXorC_covered : IsCoveredSCtl qrXorC := qrXorC_adeq.toIsCoveredSCtl

/-! ### The `RustExec` reference run of `qrXorC` -/

def xrs0 : RustState := default
def xrs1 : RustState := rsSetScalar xrs0 "a0" av
def xrs2 : RustState := rsSetScalar xrs1 "b0" bv
def xrs3 : RustState := rsSetScalar xrs2 "c0" cv
def xrs4 : RustState := rsSetScalar xrs3 "d0" dv
def xrs5 : RustState := rsSetScalar xrs4 "dx" (dxE.eval xrs4.rsScalar)
def xrsF : RustState := rsSetScalar xrs5 "bx" (bxE.eval xrs5.rsScalar)

theorem qrXorC_exec (N : Nat) (leafSpec : LeafSpec) : RustExec N leafSpec qrXorC xrs0 xrsF :=
  .seq _ _ xrs0 xrs1 xrsF (.scalarSet "a0" av xrs0)
    (.seq _ _ xrs1 xrs2 xrsF (.scalarSet "b0" bv xrs1)
      (.seq _ _ xrs2 xrs3 xrsF (.scalarSet "c0" cv xrs2)
        (.seq _ _ xrs3 xrs4 xrsF (.scalarSet "d0" dv xrs3)
          (.seq _ _ xrs4 xrs5 xrsF (.scalarSetExpr "dx" dxE xrs4)
            (.scalarSetExpr "bx" bxE xrs5)))))

/-! ### Front translation, semantics, output tracking — all by `.get`/`rfl` -/

theorem xTransSome : (translateDialectControl VarMap.empty qrXorC).isSome := by rfl

noncomputable def xO : DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty qrXorC).get xTransSome

theorem xHTrans : translateDialectControl VarMap.empty qrXorC = some xO :=
  (Option.some_get xTransSome).symm

theorem xSemSome : (semScalar qrXorC (fun _ => none)).isSome := by rfl

noncomputable def xEnv : SEnvScalar := (semScalar qrXorC (fun _ => none)).get xSemSome

theorem xHSem : semScalar qrXorC (fun _ => none) = some xEnv :=
  (Option.some_get xSemSome).symm

theorem xNameSome : (xO.vm.lookup "bx").isSome := by rfl

/-- The tracked slot's type is the 64-bit word: decided, since the slot name
    goes through `Nat.repr`, which the elaborator's definitional check does not
    reduce. -/
theorem xNameTy : ((xO.vm.lookup "bx").get xNameSome).1 = .sword 64 := by
  decide

/-- The tracked output slot for `bx`. -/
noncomputable def xW : CVar xO.Γ' (.sword 64) :=
  cast (congrArg (CVar xO.Γ') xNameTy) ((xO.vm.lookup "bx").get xNameSome).2

theorem xHName : xO.vm.lookup "bx" = some ⟨.sword 64, xW⟩ := by decide

theorem xValSome : (xEnv "bx").isSome := by rfl

theorem xValTy : ((xEnv "bx").get xValSome).1 = .sword 64 := by decide

/-- The word `semScalar` leaves in `bx`. -/
noncomputable def xVal : BitVec 64 :=
  cast (congrArg CryptoTy.denote xValTy) ((xEnv "bx").get xValSome).2

theorem xHVal : xEnv "bx" = some ⟨.sword 64, xVal⟩ := by
  rw [← Option.some_get xValSome]
  exact congrArg some (Sigma.ext xValTy
    (by unfold xVal
        exact (cast_heq (congrArg CryptoTy.denote xValTy)
          ((xEnv "bx").get xValSome).2).symm))

theorem xRetSome : (xO.cont (Com.ret (toVIRVar xW))).isSome := by rfl

noncomputable def xCom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  (xO.cont (Com.ret (toVIRVar xW))).get xRetSome

theorem xHRet : xO.cont (Com.ret (toVIRVar xW)) = some xCom :=
  (Option.some_get xRetSome).symm

theorem xComSome : (cryptoDialectToJasminCom xCom).isSome := by rfl

noncomputable def xJcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom xCom).get xComSome

theorem xHCom : cryptoDialectToJasminCom xCom = some xJcom :=
  (Option.some_get xComSome).symm

/-- The word `semScalar` leaves in `bx` is the `ofNat 64` image of the `RustExec`
    reference output. Concrete bitwise words; equality by `decide`. -/
theorem xVal_eq_ref : xVal = BitVec.ofNat 64 (xrsF.rsScalar "bx") := by decide

/-- **The bitwise XOR sub-part: `emitted jasmin = RustExec reference` (axiom-free).**
    The verified pipeline's emitted jasmin program for the ChaCha quarter-round's two
    XOR steps (`d ^= a; b ^= c`) denotes to the `ctTransTy` image of the `RustExec`
    reference output word `xrsF.rsScalar "bx"`. Purely bitwise, so the covered-fragment
    obligation is the hoisted all-`u64` `inRange` with no side condition; obtained through
    the SATISFIABLE closed-kernel route `rustToJasminCom_endToEnd_topLevel_unconditional`.
    Axiom-free. -/
theorem qrXorC_emitted_eq_rustexec (N : Nat) (leafSpec : LeafSpec) :
    (∃ Vb' : HVec xO.Γ', RustStateInterp xO.vm xrsF Vb')
      ∧ xJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (xrsF.rsScalar "bx")) := by
  have h := rustToJasminCom_endToEnd_topLevel_unconditional qrXorC xO N leafSpec xrs0 xrsF
    xEnv "bx" xW xVal xCom xJcom qrXorC_covered xHTrans
    (qrXorC_exec N leafSpec) xHSem xHName xHVal xHRet xHCom
  rwa [xVal_eq_ref] at h

/-! ## §2 — symbolic ARX arms

The `+=` and `rotl32` arms hit the `SAdd`/`SShl` overflow conditions the hoisted
all-`u64` bound cannot discharge. Under the per-kernel 32-bit lane bound `σ x < 2^32`
— the ChaCha word discipline — they are provable. -/

/-- **ChaCha add arm `inRange`.** `(x + y) & 0xFFFFFFFF` under `σ x, σ y < 2^32`:
    the `SAdd` sum `< 2^33 < 2^64`, so no overflow. -/
theorem addE_inRange_of_bound (x y : String) (σ : String → Nat)
    (hx : σ x < 2 ^ 32) (hy : σ y < 2 ^ 32) : (addE x y).inRange σ := by
  have hx64 : σ x < 2 ^ 64 := lt_trans hx (by norm_num)
  have hy64 : σ y < 2 ^ 64 := lt_trans hy (by norm_num)
  refine ⟨⟨hx64, hy64, ?_⟩, by norm_num [SExpr.inRange, M]⟩
  simp only [SExpr.eval]; omega

/-- **ChaCha rotate arm `inRange`.** `((x << n) & 0xFFFFFFFF) ^ (x >> (32-n))` under
    `σ x < 2^32` and `1 ≤ n ≤ 31`: the left shift `x << n < 2^(32+n) ≤ 2^63 < 2^64`
    (the `SShl` overflow condition), and the shift amounts `n, 32-n < 64`. -/
theorem rotlE_inRange_of_bound (n : Nat) (x : String) (σ : String → Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 31) (hx : σ x < 2 ^ 32) : (rotlE n x).inRange σ := by
  have hx64 : σ x < 2 ^ 64 := lt_trans hx (by norm_num)
  -- `x << n = x * 2^n < 2^32 * 2^n ≤ 2^63 < 2^64`
  have hshl : σ x <<< n < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    calc σ x * 2 ^ n < 2 ^ 32 * 2 ^ n := by gcongr
      _ = 2 ^ (32 + n) := by rw [pow_add]
      _ ≤ 2 ^ 63 := by apply Nat.pow_le_pow_right (by norm_num); omega
      _ < 2 ^ 64 := by norm_num
  refine ⟨⟨⟨hx64, ?_, ?_, hshl⟩, ?_⟩, hx64, ?_, ?_⟩
  all_goals simp only [SExpr.inRange, SExpr.eval, M]; omega

/-- **ChaCha add-arm reconciliation.** On every lane-bounded input the wrapping-`u64`
    evaluator agrees with the `ofNat` image of the saturating-`Nat` evaluator — the ARX
    reconciliation (`sexprTransfer`) applied to ChaCha's masked add. -/
theorem qrAdd_reconcile (x y : String) (σ : String → Nat)
    (hx : σ x < 2 ^ 32) (hy : σ y < 2 ^ 32) :
    (addE x y).evalBV (SExpr.liftEnv σ) = BitVec.ofNat 64 ((addE x y).eval σ) :=
  sexprTransfer σ (addE x y) (addE_inRange_of_bound x y σ hx hy)

/-- **ChaCha rotate-arm reconciliation.** As `qrAdd_reconcile`, for the masked rotate. -/
theorem qrRotl_reconcile (n : Nat) (x : String) (σ : String → Nat)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 31) (hx : σ x < 2 ^ 32) :
    (rotlE n x).evalBV (SExpr.liftEnv σ) = BitVec.ofNat 64 ((rotlE n x).eval σ) :=
  sexprTransfer σ (rotlE n x) (rotlE_inRange_of_bound n x σ hn1 hn2 hx)

/-! ## §3 — The full quarter-round `qrC` (closed-kernel ARX route)

All twelve steps, SSA form. `IsCoveredSCtl` needs only `srcClean` per `RScalarSetExpr`
(NOT `inRange`), and the value reconciliation is `decide` on the concrete literal
inputs; the closed-kernel argument carries the whole quarter-round. -/

theorem addE_srcClean (x y : String) (hx : x.length < 4) (hy : y.length < 4) :
    srcClean (addE x y) :=
  ⟨⟨not_isTmp_short x hx, not_isTmp_short y hy⟩, by norm_num [srcClean, M]⟩

theorem xorE_srcClean (x y : String) (hx : x.length < 4) (hy : y.length < 4) :
    srcClean (xorE x y) :=
  ⟨not_isTmp_short x hx, not_isTmp_short y hy⟩

theorem rotlE_srcClean (n : Nat) (x : String) (hn : n < 2 ^ 64) (hx : x.length < 4) :
    srcClean (rotlE n x) :=
  ⟨⟨⟨not_isTmp_short x hx, hn⟩, by norm_num [srcClean, M]⟩,
    ⟨not_isTmp_short x hx, by simp only [srcClean]; omega⟩⟩

/-- The full quarter-round in SSA form (each write a fresh slot). -/
def qrC : LowCT :=
  .RSeq (.RScalarSet "a0" av)
    (.RSeq (.RScalarSet "b0" bv)
      (.RSeq (.RScalarSet "c0" cv)
        (.RSeq (.RScalarSet "d0" dv)
          -- a += b; d ^= a; d = rotl(d,16)
          (.RSeq (.RScalarSetExpr "a1" (addE "a0" "b0"))
            (.RSeq (.RScalarSetExpr "d1" (xorE "d0" "a1"))
              (.RSeq (.RScalarSetExpr "d2" (rotlE 16 "d1"))
                -- c += d; b ^= c; b = rotl(b,12)
                (.RSeq (.RScalarSetExpr "c1" (addE "c0" "d2"))
                  (.RSeq (.RScalarSetExpr "b1" (xorE "b0" "c1"))
                    (.RSeq (.RScalarSetExpr "b2" (rotlE 12 "b1"))
                      -- a += b; d ^= a; d = rotl(d,8)
                      (.RSeq (.RScalarSetExpr "a2" (addE "a1" "b2"))
                        (.RSeq (.RScalarSetExpr "d3" (xorE "d2" "a2"))
                          (.RSeq (.RScalarSetExpr "d4" (rotlE 8 "d3"))
                            -- c += d; b ^= c; b = rotl(b,7)
                            (.RSeq (.RScalarSetExpr "c2" (addE "c1" "d4"))
                              (.RSeq (.RScalarSetExpr "b3" (xorE "b2" "c2"))
                                (.RScalarSetExpr "b4" (rotlE 7 "b3"))))))))))))))))

theorem qrC_coveredS : IsCoveredS qrC :=
  .rSeq (.rScalarSet "a0" _)
    (.rSeq (.rScalarSet "b0" _)
      (.rSeq (.rScalarSet "c0" _)
        (.rSeq (.rScalarSet "d0" _)
          (.rSeq (.rScalarSetExpr "a1" _ (addE_srcClean "a0" "b0" (by decide) (by decide)))
            (.rSeq (.rScalarSetExpr "d1" _ (xorE_srcClean "d0" "a1" (by decide) (by decide)))
              (.rSeq (.rScalarSetExpr "d2" _ (rotlE_srcClean 16 "d1" (by norm_num) (by decide)))
                (.rSeq (.rScalarSetExpr "c1" _ (addE_srcClean "c0" "d2" (by decide) (by decide)))
                  (.rSeq (.rScalarSetExpr "b1" _ (xorE_srcClean "b0" "c1" (by decide) (by decide)))
                    (.rSeq (.rScalarSetExpr "b2" _ (rotlE_srcClean 12 "b1" (by norm_num) (by decide)))
                      (.rSeq (.rScalarSetExpr "a2" _ (addE_srcClean "a1" "b2" (by decide) (by decide)))
                        (.rSeq (.rScalarSetExpr "d3" _ (xorE_srcClean "d2" "a2" (by decide) (by decide)))
                          (.rSeq (.rScalarSetExpr "d4" _ (rotlE_srcClean 8 "d3" (by norm_num) (by decide)))
                            (.rSeq (.rScalarSetExpr "c2" _ (addE_srcClean "c1" "d4" (by decide) (by decide)))
                              (.rSeq (.rScalarSetExpr "b3" _ (xorE_srcClean "b2" "c2" (by decide) (by decide)))
                                (.rScalarSetExpr "b4" _ (rotlE_srcClean 7 "b3" (by norm_num) (by decide)))))))))))))))))

theorem qrC_covered : IsCoveredSCtl qrC := .ofStraight qrC_coveredS

/-! ### The `RustExec` reference run of `qrC` -/

def qrs0 : RustState := default
def qrs1 : RustState := rsSetScalar qrs0 "a0" av
def qrs2 : RustState := rsSetScalar qrs1 "b0" bv
def qrs3 : RustState := rsSetScalar qrs2 "c0" cv
def qrs4 : RustState := rsSetScalar qrs3 "d0" dv
def qrs5 : RustState := rsSetScalar qrs4 "a1" ((addE "a0" "b0").eval qrs4.rsScalar)
def qrs6 : RustState := rsSetScalar qrs5 "d1" ((xorE "d0" "a1").eval qrs5.rsScalar)
def qrs7 : RustState := rsSetScalar qrs6 "d2" ((rotlE 16 "d1").eval qrs6.rsScalar)
def qrs8 : RustState := rsSetScalar qrs7 "c1" ((addE "c0" "d2").eval qrs7.rsScalar)
def qrs9 : RustState := rsSetScalar qrs8 "b1" ((xorE "b0" "c1").eval qrs8.rsScalar)
def qrs10 : RustState := rsSetScalar qrs9 "b2" ((rotlE 12 "b1").eval qrs9.rsScalar)
def qrs11 : RustState := rsSetScalar qrs10 "a2" ((addE "a1" "b2").eval qrs10.rsScalar)
def qrs12 : RustState := rsSetScalar qrs11 "d3" ((xorE "d2" "a2").eval qrs11.rsScalar)
def qrs13 : RustState := rsSetScalar qrs12 "d4" ((rotlE 8 "d3").eval qrs12.rsScalar)
def qrs14 : RustState := rsSetScalar qrs13 "c2" ((addE "c1" "d4").eval qrs13.rsScalar)
def qrs15 : RustState := rsSetScalar qrs14 "b3" ((xorE "b2" "c2").eval qrs14.rsScalar)
def qrsF : RustState := rsSetScalar qrs15 "b4" ((rotlE 7 "b3").eval qrs15.rsScalar)

theorem qrC_exec (N : Nat) (leafSpec : LeafSpec) : RustExec N leafSpec qrC qrs0 qrsF :=
  .seq _ _ qrs0 qrs1 qrsF (.scalarSet "a0" av qrs0)
    (.seq _ _ qrs1 qrs2 qrsF (.scalarSet "b0" bv qrs1)
      (.seq _ _ qrs2 qrs3 qrsF (.scalarSet "c0" cv qrs2)
        (.seq _ _ qrs3 qrs4 qrsF (.scalarSet "d0" dv qrs3)
          (.seq _ _ qrs4 qrs5 qrsF (.scalarSetExpr "a1" (addE "a0" "b0") qrs4)
            (.seq _ _ qrs5 qrs6 qrsF (.scalarSetExpr "d1" (xorE "d0" "a1") qrs5)
              (.seq _ _ qrs6 qrs7 qrsF (.scalarSetExpr "d2" (rotlE 16 "d1") qrs6)
                (.seq _ _ qrs7 qrs8 qrsF (.scalarSetExpr "c1" (addE "c0" "d2") qrs7)
                  (.seq _ _ qrs8 qrs9 qrsF (.scalarSetExpr "b1" (xorE "b0" "c1") qrs8)
                    (.seq _ _ qrs9 qrs10 qrsF (.scalarSetExpr "b2" (rotlE 12 "b1") qrs9)
                      (.seq _ _ qrs10 qrs11 qrsF (.scalarSetExpr "a2" (addE "a1" "b2") qrs10)
                        (.seq _ _ qrs11 qrs12 qrsF (.scalarSetExpr "d3" (xorE "d2" "a2") qrs11)
                          (.seq _ _ qrs12 qrs13 qrsF (.scalarSetExpr "d4" (rotlE 8 "d3") qrs12)
                            (.seq _ _ qrs13 qrs14 qrsF (.scalarSetExpr "c2" (addE "c1" "d4") qrs13)
                              (.seq _ _ qrs14 qrs15 qrsF (.scalarSetExpr "b3" (xorE "b2" "c2") qrs14)
                                (.scalarSetExpr "b4" (rotlE 7 "b3") qrs15)))))))))))))))

/-! ### Front translation, semantics, output tracking — all by `.get`/`rfl` -/

theorem qTransSome : (translateDialectControl VarMap.empty qrC).isSome := by rfl

noncomputable def qO : DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty qrC).get qTransSome

theorem qHTrans : translateDialectControl VarMap.empty qrC = some qO :=
  (Option.some_get qTransSome).symm

theorem qSemSome : (semScalar qrC (fun _ => none)).isSome := by rfl

noncomputable def qEnv : SEnvScalar := (semScalar qrC (fun _ => none)).get qSemSome

theorem qHSem : semScalar qrC (fun _ => none) = some qEnv :=
  (Option.some_get qSemSome).symm

theorem qNameSome : (qO.vm.lookup "b4").isSome := by rfl

/-- The tracked slot's type is the 64-bit word: decided, since the slot name
    goes through `Nat.repr`, which the elaborator's definitional check does not
    reduce. -/
theorem qNameTy : ((qO.vm.lookup "b4").get qNameSome).1 = .sword 64 := by
  decide

/-- The tracked output slot for `b4`. -/
noncomputable def qW : CVar qO.Γ' (.sword 64) :=
  cast (congrArg (CVar qO.Γ') qNameTy) ((qO.vm.lookup "b4").get qNameSome).2

theorem qHName : qO.vm.lookup "b4" = some ⟨.sword 64, qW⟩ := by decide

theorem qValSome : (qEnv "b4").isSome := by rfl

theorem qValTy : ((qEnv "b4").get qValSome).1 = .sword 64 := by decide

/-- The word `semScalar` leaves in `b4`. -/
noncomputable def qVal : BitVec 64 :=
  cast (congrArg CryptoTy.denote qValTy) ((qEnv "b4").get qValSome).2

theorem qHVal : qEnv "b4" = some ⟨.sword 64, qVal⟩ := by
  rw [← Option.some_get qValSome]
  exact congrArg some (Sigma.ext qValTy
    (by unfold qVal
        exact (cast_heq (congrArg CryptoTy.denote qValTy)
          ((qEnv "b4").get qValSome).2).symm))

theorem qRetSome : (qO.cont (Com.ret (toVIRVar qW))).isSome := by rfl

noncomputable def qCom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  (qO.cont (Com.ret (toVIRVar qW))).get qRetSome

theorem qHRet : qO.cont (Com.ret (toVIRVar qW)) = some qCom :=
  (Option.some_get qRetSome).symm

theorem qComSome : (cryptoDialectToJasminCom qCom).isSome := by rfl

noncomputable def qJcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom qCom).get qComSome

theorem qHCom : cryptoDialectToJasminCom qCom = some qJcom :=
  (Option.some_get qComSome).symm

/-- **The `inRange` reconciliation for the whole quarter-round, concrete leg.** The word
    `semScalar` leaves in `b4` — computed through the four adds, four XORs, four rotates
    by the wrapping-`u64` evaluator — is the `ofNat 64` image of the `RustExec`
    saturating-`Nat` reference output. Concrete literal inputs, on which no `+`/`<<`
    overflows `u64`; equality by `decide`. -/
theorem qVal_eq_ref : qVal = BitVec.ofNat 64 (qrsF.rsScalar "b4") := by decide

/-! ### `emitted full quarter-round = RustExec reference` -/

/-- **The full ChaCha20 quarter-round: `emitted jasmin = RustExec reference output`.**
    The verified pipeline's emitted jasmin program for the twelve-step quarter-round
    (`a += b; d ^= a; d = rotl(d,16); …`) denotes to the `ctTransTy` image of the
    `RustExec` reference output word `qrsF.rsScalar "b4"`. Obtained through the SATISFIABLE
    closed-kernel route `rustToJasminCom_endToEnd_topLevel_unconditional`: the kernel is
    closed (all inputs literals, SSA writes), so `semScalar` succeeds from the empty entry
    env and no entry `EnvRel` seam is needed; the ARX (`+=`, `rotl32`) value reconciliation
    is discharged concretely (`qVal_eq_ref`) under the kernel's 32-bit input discipline.
    Axiom-free. -/
theorem qrC_emitted_eq_rustexec (N : Nat) (leafSpec : LeafSpec) :
    (∃ Vb' : HVec qO.Γ', RustStateInterp qO.vm qrsF Vb')
      ∧ qJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (qrsF.rsScalar "b4")) := by
  have h := rustToJasminCom_endToEnd_topLevel_unconditional qrC qO N leafSpec qrs0 qrsF
    qEnv "b4" qW qVal qCom qJcom qrC_covered qHTrans
    (qrC_exec N leafSpec) qHSem qHName qHVal qHRet qHCom
  rwa [qVal_eq_ref] at h

end CatCrypt.Crypto.SecureCompilation.Dialects.RustExecChaChaAdeq

#print axioms CatCrypt.Crypto.SecureCompilation.Dialects.RustExecChaChaAdeq.qrXorC_emitted_eq_rustexec
#print axioms CatCrypt.Crypto.SecureCompilation.Dialects.RustExecChaChaAdeq.qrC_emitted_eq_rustexec
#print axioms CatCrypt.Crypto.SecureCompilation.Dialects.RustExecChaChaAdeq.addE_inRange_of_bound
#print axioms CatCrypt.Crypto.SecureCompilation.Dialects.RustExecChaChaAdeq.rotlE_inRange_of_bound
#print axioms CatCrypt.Crypto.SecureCompilation.Dialects.RustExecChaChaAdeq.qrAdd_reconcile
#print axioms CatCrypt.Crypto.SecureCompilation.Dialects.RustExecChaChaAdeq.qrRotl_reconcile
