/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSha256Adeq

/-!
# The SHA-256 compression as an `RFor` round loop through the `emitted = RustExec` route

`RustExecSha256Adeq.sha256C_emitted_eq_rustexec` proved `emitted jasmin = RustExec
reference` for ONE whole SHA-256 compression round STEP (a closed straight-line
kernel). Its header lays out the 64-round composition: the round body reused with
per-round `K`/`W`, the 64-round loop as an `RFor` (`IsCoveredAdeq.rFor`, `N ≤ 2^64`)
tracked by the loop bridge `agreeFor`. This module carries the round STEP up to the
round LOOP along the two orthogonal legs the compression composition needs.

## Two legs, two capabilities

The pipeline exposes two end-to-end routes, and the SHA-256 round loop lands on
each along one axis:

* **The closed jasmin-bytes leg (`§A`)** — `rustToJasminCom_endToEnd_topLevel_unconditional`
  takes a closed command all the way to emitted jasmin bytes, tying them to the
  `RustExec` reference by a concrete value `decide`. It needs `IsCoveredSCtl`
  (whose `RFor` arm `IsCoveredSCtl.rFor` is a first-class control node) and a
  `semScalar` that succeeds from the EMPTY entry env — i.e. every read must follow
  a write *inside* the command. `loopA = RFor "i" 2 bodyA` with a self-contained
  body (each iteration re-establishes its own `a,b,c` before computing `Maj`) is
  exactly such a closed loop: the FIRST genuine `RFor` control node taken to jasmin
  bytes = `RustExec` reference, axiom-free.

* **The symbolic value-adequacy leg (`§B`)** — `rustExec_semScalar_agree` ties the
  `semScalar` word-model output of an `IsCoveredAdeq` command to the `RustExec`
  `Nat`-model output for EVERY input, over ANY loop count `M ≤ 2^64`, through the
  loop bridge `agreeFor` (`Nat`-induction on the trip count). `loopB M = RFor "i" M
  bodyB` with a state-THREADING round body (iteration `i` reads iteration `i−1`'s
  `a,e` and writes them back) is the SHA-shaped iterated round: its threaded output
  word in `semScalar` is the `ofNat 64` image of the `RustExec` reference, for all
  `M` at once. This is the `agreeFor` reconciliation carrying a real round loop.

## Coverage (which SHA-256 round arms fit)

`IsCoveredAdeq`'s `RScalarSetExpr` arm asks for `srcClean e` AND the input-agnostic
`hir : ∀ σ, (∀ y, σ y < 2^64) → e.inRange σ`. The `∧`/`⊕`/`¬` layer (`Ch`, `Maj`,
and the `⊕`-mixes threading state) meets `hir` for ALL `u64` inputs with no side
condition (`SAnd`/`SXor` carry only their operand conditions). The `Σ`/`σ`
rotations (`SShl`) and the `T1`/`T2` modular adds (`SAdd`) do NOT — a left-shift or
an add of two full-range `u64`s overflows the saturating-`Nat` model, so the
input-agnostic `hir` fails on those arms (the `RustExecARXAdeq` §Residual wall).
So the threading round loop `bodyB` here is the maximal genuinely-iterated SHA-256
round expressible on the symbolic leg: the nonlinear `Ch`/`Maj` layer plus the
`⊕`-state mixing. The ARX `Σ`/`σ`/`+` arms reconcile only under a per-kernel
concrete input bound (`RustExecSha256Adeq.t1E_inRange_of_bound` /
`RustExecARXAdeq.arxE_inRange_of_bound`), which the closed-kernel `decide` leg
discharges concretely — as the whole round STEP does in `RustExecSha256Adeq`.

## The remaining scaling (the exact residual)

Three walls keep the *threading full-ARX 64-round* compression off a single
theorem; each is orthogonal and documented here:

1. **Threading × closed-bytes.** The closed jasmin-bytes leg needs an
   empty-entry-env `semScalar`, so its loop body must be self-contained (`bodyA`).
   A THREADING body reads state the loop's earlier iterations wrote, which is
   unbound in the empty entry env — so the threading loop takes the symbolic leg
   (`§B`), not the bytes leg. Fusing the two additionally needs the entry seam the
   `RustExecKernelAdeq.entry_trio_unsat_empty` clash blocks (`EnvRel` binds every
   non-temp name; `ConsistentS` pins the env to a finite `VarMap`).

2. **`RFor` output tracking on the empty-entry route.** `afterB (fun _ => False)
   (RFor …) name` is `False` (the loop's `afterB` is conservative — a loop output
   must be pre-initialised into the entry-bound set `B`). So the composed
   `rustToJasminCom_endToEnd_rustexec_adeq_topLevel` cannot track a bare top-level
   `RFor` output. The pre-loop `RScalarSet` that would seed `B` cannot be sequenced
   before the loop, by wall 3.

3. **`RSeq`-then-`RFor` front wall.** `translateDialectControl` handles `RFor` only
   as a top-level node; an `RSeq setup (RFor …)` delegates the whole `RSeq` to
   `translateDialectFull`, which declines every `RFor` (`| _ => none`). So a
   setup-before-loop kernel is not front-translatable; the loop must stand alone.

The genuine ARX round STEP is carried concretely by
`RustExecSha256Adeq.sha256C_emitted_eq_rustexec` (whole round, one `decide`); the
round LOOP is carried on the closed leg (`§A`, self-contained body, bytes) and the
symbolic leg (`§B`, threading body, any `M`); closing all three walls at once — a
threading full-ARX loop to bytes with symbolic `M` — is the standing composition
residual, orthogonal to the round arms and loop bridge established here.
-/

set_option autoImplicit false
-- The `RFor` front-tracking (`loopRForD`) and `semScalar` (`semRForD`) unroll the
-- loop count, and the concrete value tie `decide`s the unrolled output, so raise
-- the reduction recursion limit as the single-round kernel does.
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
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSha256Adeq
  (M av bv cv majE majE_srcClean chE chE_srcClean)

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSha256FullAdeq

/-! ## Shared all-`u64` `inRange` lemmas for the nonlinear SHA-256 round arms

The `∧`/`⊕`/`¬` arms meet the input-agnostic hoisted `inRange` bound with no side
condition (bitwise ops preserve `u64`-range); only the `¬`-mask literal `M` needs
`M < 2^64`. These feed both the closed leg's coverage and the symbolic leg's
`IsCoveredAdeqS` arms. -/

/-- `Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)` is `u64`-range for all `u64` inputs. -/
theorem majE_inRange : ∀ σ : String → Nat, (∀ y, σ y < 2 ^ 64) → majE.inRange σ :=
  fun _σ h => ⟨⟨⟨h "a", h "b"⟩, ⟨h "a", h "c"⟩⟩, ⟨h "b", h "c"⟩⟩

/-- `Ch(e,f,g) = (e ∧ f) ⊕ (¬e ∧ g)` with `¬e = e ⊕ M` is `u64`-range for all `u64`
    inputs (the mask literal `M = 0xFFFFFFFF < 2^64`). -/
theorem chE_inRange : ∀ σ : String → Nat, (∀ y, σ y < 2 ^ 64) → chE.inRange σ :=
  fun _σ h => ⟨⟨h "e", h "f"⟩, ⟨⟨h "e", by norm_num [SExpr.inRange, M]⟩, h "g"⟩⟩

/-! ## §A — a closed `RFor` round loop through the jasmin-bytes route

The self-contained round body re-establishes its inputs `a,b,c` each iteration,
then computes `Maj`. As a closed command every read follows a write, so `semScalar`
succeeds from the empty entry env and the closed route
`rustToJasminCom_endToEnd_topLevel_unconditional` applies to the `RFor` node. -/

/-- The self-contained round body: reset `a,b,c` to the SHA-256 IV words, compute
    `mj = Maj(a,b,c)`. Closed (reads follow writes), so the loop it drives runs
    from the empty entry env. -/
def bodyA : LowCT :=
  .RSeq (.RScalarSet "a" av)
    (.RSeq (.RScalarSet "b" bv)
      (.RSeq (.RScalarSet "c" cv)
        (.RScalarSetExpr "mj" majE)))

/-- The round loop: run the self-contained round body twice. A genuine `RFor`
    control node (loop count `2`); the `RScalarSet`-reset body keeps it closed. -/
def loopA : LowCT := .RFor "i" 2 bodyA

theorem bodyA_coveredS : IsCoveredS bodyA :=
  .rSeq (.rScalarSet "a" _)
    (.rSeq (.rScalarSet "b" _)
      (.rSeq (.rScalarSet "c" _)
        (.rScalarSetExpr "mj" majE majE_srcClean)))

theorem loopA_covered : IsCoveredSCtl loopA :=
  .rFor (.ofStraight bodyA_coveredS)

/-! ### The `RustExec` reference run of `loopA` -/

def rs0A : RustState := default

/-- One self-contained body run: reset `a,b,c`, write `mj = Maj`. -/
def runB (rs : RustState) : RustState :=
  rsSetScalar (rsSetScalar (rsSetScalar (rsSetScalar rs "a" av) "b" bv) "c" cv) "mj"
    (majE.eval (rsSetScalar (rsSetScalar (rsSetScalar rs "a" av) "b" bv) "c" cv).rsScalar)

/-- The state after iteration `0` (counter `i = 0`). -/
def rsA1 : RustState := runB (rsSetScalar rs0A "i" 0)

/-- The state after iteration `1` (counter `i = 1`) — the loop's final state. -/
def rsFA : RustState := runB (rsSetScalar rsA1 "i" 1)

/-- The reference execution of one self-contained body from any entry state. -/
theorem bodyA_exec (N : Nat) (leafSpec : LeafSpec) (rs : RustState) :
    RustExec N leafSpec bodyA rs (runB rs) :=
  .seq _ _ rs _ _ (.scalarSet "a" av rs)
    (.seq _ _ _ _ _ (.scalarSet "b" bv _)
      (.seq _ _ _ _ _ (.scalarSet "c" cv _)
        (.scalarSetExpr "mj" majE _)))

/-- The reference execution of the two-trip round loop, `forZero`/`forSucc`. -/
theorem loopA_exec (N : Nat) (leafSpec : LeafSpec) :
    RustExec N leafSpec loopA rs0A rsFA :=
  .forSucc "i" 1 bodyA rs0A rsA1 rsFA
    (.forSucc "i" 0 bodyA rs0A rs0A rsA1
      (.forZero "i" bodyA rs0A)
      (bodyA_exec N leafSpec (rsSetScalar rs0A "i" 0)))
    (bodyA_exec N leafSpec (rsSetScalar rsA1 "i" 1))

/-! ### Front translation, semantics, output tracking — all by `.get`/`rfl` -/

theorem loopATransSome : (translateDialectControl VarMap.empty loopA).isSome := by rfl

noncomputable def loopAO : DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty loopA).get loopATransSome

theorem loopAHTrans : translateDialectControl VarMap.empty loopA = some loopAO :=
  (Option.some_get loopATransSome).symm

theorem loopASemSome : (semScalar loopA (fun _ => none)).isSome := by rfl

noncomputable def loopAEnv : SEnvScalar := (semScalar loopA (fun _ => none)).get loopASemSome

theorem loopAHSem : semScalar loopA (fun _ => none) = some loopAEnv :=
  (Option.some_get loopASemSome).symm

theorem loopANameSome : (loopAO.vm.lookup "mj").isSome := by rfl

noncomputable def loopAW : CVar loopAO.Γ' (.sword 64) :=
  ((loopAO.vm.lookup "mj").get loopANameSome).2

theorem loopAHName : loopAO.vm.lookup "mj" = some ⟨.sword 64, loopAW⟩ := by rfl

theorem loopAValSome : (loopAEnv "mj").isSome := by rfl

noncomputable def loopAVal : BitVec 64 := ((loopAEnv "mj").get loopAValSome).2

theorem loopAHVal : loopAEnv "mj" = some ⟨.sword 64, loopAVal⟩ := by rfl

theorem loopARetSome : (loopAO.cont (Com.ret (toVIRVar loopAW))).isSome := by rfl

noncomputable def loopACom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  (loopAO.cont (Com.ret (toVIRVar loopAW))).get loopARetSome

theorem loopAHRet : loopAO.cont (Com.ret (toVIRVar loopAW)) = some loopACom :=
  (Option.some_get loopARetSome).symm

theorem loopAComSome : (cryptoDialectToJasminCom loopACom).isSome := by rfl

noncomputable def loopAJcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom loopACom).get loopAComSome

theorem loopAHCom : cryptoDialectToJasminCom loopACom = some loopAJcom :=
  (Option.some_get loopAComSome).symm

/-- **The round loop's `#250` reconciliation, concrete leg.** The word `semScalar`
    leaves in `mj` after two trips of the self-contained `Maj` round is the
    `ofNat 64` image of the `RustExec` reference output `rsFA.rsScalar "mj"`. Both
    concrete words on literal inputs; equality by `decide`. -/
theorem loopAVal_eq_ref : loopAVal = BitVec.ofNat 64 (rsFA.rsScalar "mj") := by decide

/-- **The SHA-256 round LOOP: `emitted jasmin = RustExec reference output`.** The
    verified pipeline's emitted jasmin program for the `RFor` round loop
    (`RFor "i" 2` over a self-contained `Maj` round) denotes to the `ctTransTy`
    image of the `RustExec` reference output word `rsFA.rsScalar "mj"`. Obtained
    through the closed-kernel route `rustToJasminCom_endToEnd_topLevel_unconditional`
    applied to a genuine `RFor` control node (`IsCoveredSCtl.rFor`): the loop is
    closed, so `semScalar` succeeds from the empty entry env and no entry seam is
    needed; the value reconciliation is discharged concretely (`loopAVal_eq_ref`).
    Axiom-free. -/
theorem loopA_emitted_eq_rustexec (N : Nat) (leafSpec : LeafSpec) :
    (∃ Vb' : HVec loopAO.Γ', RustStateInterp loopAO.vm rsFA Vb')
      ∧ loopAJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (rsFA.rsScalar "mj")) := by
  have h := rustToJasminCom_endToEnd_topLevel_unconditional loopA loopAO N leafSpec rs0A rsFA
    loopAEnv "mj" loopAW loopAVal loopACom loopAJcom loopA_covered loopAHTrans
    (loopA_exec N leafSpec) loopAHSem loopAHName loopAHVal loopAHRet loopAHCom
  rwa [loopAVal_eq_ref] at h

/-! ## §B — a state-threading round loop through the symbolic `agreeFor` bridge

The threading round body reads the eight-word state and writes back the mixed
`a`/`e`, so iteration `i` consumes iteration `i−1`'s outputs — a genuinely iterated
SHA-shaped round. Its arms are the nonlinear `Ch`/`Maj` and the `⊕`-mixes, all
all-`u64` `inRange`-clean, so `IsCoveredAdeq` covers it and `rustExec_semScalar_agree`
ties its `semScalar` output to the `RustExec` reference for ANY loop count `M`. -/

/-- `a' = a ⊕ Ch ⊕ Maj` — the state word `a`'s `⊕`-mix, feeding the next round. -/
def mixaE : SExpr := .SXor (.SXor (.SVar "a") (.SVar "ch")) (.SVar "mj")

/-- `e' = e ⊕ Ch` — the state word `e`'s `⊕`-mix, feeding the next round. -/
def mixeE : SExpr := .SXor (.SVar "e") (.SVar "ch")

theorem mixaE_srcClean : srcClean mixaE :=
  ⟨⟨not_isTmp_short "a" (by decide), not_isTmp_short "ch" (by decide)⟩,
    not_isTmp_short "mj" (by decide)⟩

theorem mixeE_srcClean : srcClean mixeE :=
  ⟨not_isTmp_short "e" (by decide), not_isTmp_short "ch" (by decide)⟩

theorem mixaE_inRange : ∀ σ : String → Nat, (∀ y, σ y < 2 ^ 64) → mixaE.inRange σ :=
  fun _σ h => ⟨⟨h "a", h "ch"⟩, h "mj"⟩

theorem mixeE_inRange : ∀ σ : String → Nat, (∀ y, σ y < 2 ^ 64) → mixeE.inRange σ :=
  fun _σ h => ⟨h "e", h "ch"⟩

/-- The state-threading round body: compute `ch = Ch(e,f,g)`, `mj = Maj(a,b,c)`,
    then thread `a := a ⊕ ch ⊕ mj` and `e := e ⊕ ch` back into the state. -/
def bodyB : LowCT :=
  .RSeq (.RScalarSetExpr "ch" chE)
    (.RSeq (.RScalarSetExpr "mj" majE)
      (.RSeq (.RScalarSetExpr "a" mixaE)
        (.RScalarSetExpr "e" mixeE)))

/-- The threading round loop over `M` trips (the SHA-256 compression's 64-round
    iteration at `M = 64`). -/
def loopB (M : Nat) : LowCT := .RFor "i" M bodyB

theorem bodyB_adeqS : IsCoveredAdeqS bodyB :=
  .rSeq (.rScalarSetExpr "ch" chE chE_srcClean chE_inRange)
    (.rSeq (.rScalarSetExpr "mj" majE majE_srcClean majE_inRange)
      (.rSeq (.rScalarSetExpr "a" mixaE mixaE_srcClean mixaE_inRange)
        (.rScalarSetExpr "e" mixeE mixeE_srcClean mixeE_inRange)))

/-- The threading round loop is in the covered word-adequacy fragment for any
    trip count `M ≤ 2^64` — the `RFor` arm of `IsCoveredAdeq` over the covered
    round body. -/
theorem loopB_adeq {M : Nat} (hM : M ≤ 2 ^ 64) : IsCoveredAdeq (loopB M) :=
  .rFor hM (.ofStraight bodyB_adeqS)

/-- **The SHA-256 threading round LOOP: `semScalar` output = `RustExec` reference,
    any loop count.** For every entry state `rs` with in-range scalars and every
    `RustExec` `Nat`-model run of the `M`-trip threading round loop to `rs'`, the
    `semScalar` word-model run from the reflected entry env (`derivedEnv rs`) is
    defined and leaves in the threaded state word `a` exactly the `ofNat 64` image
    of the `RustExec` reference output `rs'.rsScalar "a"`. The loop-count induction
    is the bridge `agreeFor`; the entry `EnvRel` seam is `derivedEnv`. Holds for
    ALL `M ≤ 2^64` (the compression's 64 rounds at `M = 64`) at once — the symbolic
    reconciliation the closed `decide` leg cannot reach for a threading body.
    Axiom-free. -/
theorem loopB_semScalar_eq_rustexec (N M : Nat) (leafSpec : LeafSpec) (hM : M ≤ 2 ^ 64)
    (rs rs' : RustState) (hexec : RustExec N leafSpec (loopB M) rs rs')
    (hir : ScalarInRange rs) :
    ∃ env', semScalar (loopB M) (derivedEnv rs) = some env' ∧
      env' "a" = some ⟨.sword 64, BitVec.ofNat 64 (rs'.rsScalar "a")⟩ := by
  obtain ⟨env', hSem, hRel, _⟩ :=
    rustExec_semScalar_agree (loopB_adeq hM) hexec (envRel_derivedEnv rs) hir
  exact ⟨env', hSem, hRel "a" (not_isTmp_short "a" (by decide))⟩

/-- **The 64-round instance.** The threading round loop specialised to the
    SHA-256 compression's `M = 64` trips: the `semScalar` output word `a` is the
    `ofNat 64` image of the 64-round `RustExec` reference, for every input. -/
theorem loopB64_semScalar_eq_rustexec (N : Nat) (leafSpec : LeafSpec)
    (rs rs' : RustState) (hexec : RustExec N leafSpec (loopB 64) rs rs')
    (hir : ScalarInRange rs) :
    ∃ env', semScalar (loopB 64) (derivedEnv rs) = some env' ∧
      env' "a" = some ⟨.sword 64, BitVec.ofNat 64 (rs'.rsScalar "a")⟩ :=
  loopB_semScalar_eq_rustexec N 64 leafSpec (by norm_num) rs rs' hexec hir

end CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSha256FullAdeq
