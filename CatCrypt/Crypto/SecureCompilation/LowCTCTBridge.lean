/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.LowCTCT
import CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import CatCrypt.Crypto.SecureCompilation.Framework
import CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge
import CatCrypt.Crypto.Jasmin.LowCTToJasmin
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim

/-!
# CT bridge for Pipeline (1): LowCT → catCryptDialect → Jasmin → x86

The constant-time (CT) side of the LowCT front. It carries a source
program from the syntactic source-level CT predicate `isCT_LowCT'`
(`LowCTCT.lean`) to the Jasmin syntactic CT whitelist `isCT_Cmd`
(`JasminCT.lean`) on the emitted command, and — modulo the external
`jasminc_preserves_ct` axiom of `JasminCompilerBridge.lean` (arXiv
2511.11292) — to the x86-64 leakage predicate `X86Prog.isCT`.

## Scope: no dialect-level CT conclusion

A CT-preservation statement into `Com catCryptDialect` requires a
value-carrying leak trace. `CryptoDialectLeakTraceValued.lean` provides
one: `Com.leakTraceV` threads the runtime `Ctxt.Valuation`, and
`Com.isConstantTimeV` is the corresponding input-independence predicate.
The valuation-free `Com.leakTrace` (`CryptoDialectLeakTrace.lean`) emits
the same `List LeakEvent` for every input, so `Com.isConstantTime`
reduces to an argument-free equality (`Com.all_com_ct = fun _ _ _ =>
rfl`) that holds for every term and constrains no program. A dialect
CT-preservation theorem must therefore conclude over the valued trace:

    isCT_LowCT' leaves secrets c = true →
    translateDialectControl vm c = some o →
    o.cont tail = some assembled →
    Com.isConstantTimeV assembled

so that the source CT hypothesis is consumed. This is the leakage /
robust-hyperproperty preservation port over the descent, which no lemma
in the tree currently closes; `CryptoDialectLeakTraceValued.lean`
records it as the outstanding follow-up. This module states no dialect
CT conclusion.

## Contents

* `compose_compiler_preserves_uc` — transports concurrent UC security
  along compiler correctness (`compiler_preserves_uc`, `Framework.lean`).
* `jasminCTSafe` and `isCT_Cmd_of_jasminCTSafe` — on the `jasminCTSafe`
  fragment of `LowCT`, the Jasmin command `toJasminCmd` produces is
  syntactically constant-time (`isCT_Cmd`), by structural induction over
  every LowCT constructor.
* `rustcmd_ct_implies_x86_ct` and
  `rustcmd_ct_implies_x86_ct_of_isCT_LowCT'` — the source→x86 CT chain,
  closing the final step with the `jasminc_preserves_ct` axiom.
* `isCT_LowCT'_imp_jasminCTSafe` — on `inCertifiedCTFragment`, the
  user-facing `isCT_LowCT'` implies the certified `jasminCTSafe`.
-/

namespace CatCrypt.Crypto.SecureCompilation.LowCTCTBridge

open CatCrypt.Core CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation
open CatCrypt.Crypto.SecureCompilation.LowCTCT
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT
open UCMonad UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open scoped ENNReal

set_option autoImplicit false

/-! ## §2  Composition with `compiler_preserves_uc`

`compiler_preserves_uc` (in `Framework.lean`) transports concurrent UC
security along compiler correctness.  This corollary re-exposes it at
the LowCT front boundary. -/
theorem compose_compiler_preserves_uc
    {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {hon S out_t leak view : Type}
    {source target : hon → StatefulITreeN S n E (out_t ⊕ leak)}
    {F : hon → StatefulITreeN S n E (out_t ⊕ view)}
    {ε : ENNReal}
    (hcc : CompilerCorrectStateful source target)
    (hsec : UCEmulatesConcurrentStateful handler n ε source F) :
    UCEmulatesConcurrentStateful handler n ε target F :=
  compiler_preserves_uc handler hcc hsec

/-! ## §3  Composition with `cryptoSSA_to_x86_preserves_ct` (track C3.3)

The Jasmin compiler bridge in `JasminCompilerBridge.lean` axiomatises
that `jasminc` preserves syntactic CT from Jasmin source to x86-64
binary.  Combining it with our LowCT→CryptoSSA bridge gives a
full source→x86 CT chain *modulo* two glue facts:

1. **`LowCT`-syntactic-CT → Jasmin-syntactic-CT** lifting.  We need
   that the Jasmin command produced by `LowCTToJasmin.toJasminCmd`
   is accepted by `JasminCT.isCT_Cmd`.  After C3.4's whitelist
   extension, this is a structural induction on `LowCT` covering
   all 10 constructors:

   * `RSkip`/`RSeq`/`RLetU64Zero`/`RScalarSet`/`RWhileNz` — accepted
     by the original C3.3 whitelist (`Cassgn` shapes + the public-flag
     `Cwhile` clause).
   * `RLetZero` lowers to `Cassgn (Lvar _) _ _ (Parr_init n) :: …` —
     accepted by C3.4's `Parr_init` clause in `isCT_PExpr`.
   * `RCall` / `RCloneCall` lower to `Ccall` and `Copn (Oasm
     "CLONE_TOWER")` — accepted by C3.4's `Ccall` clause in
     `isCT_InstrR` and the `CLONE_TOWER` entry in `ct_intrinsic`.
   * `RIfNz` lowers to `[Cif (Papp2 (Oneq U64) (Pvar _) (...)) _ _]`
     — accepted by C3.4's `Cif` clause in `isCT_InstrR` (which
     requires the public-flag guard shape, mirroring the existing
     `Cwhile` rule).
   * `RLimbStore` lowers to `[Copn _ _ (Oasm "STORE64") _]` —
     accepted by C3.4's `STORE64` entry in `ct_intrinsic`.

   The connector lemma `isCT_Cmd_of_jasminCTSafe` discharges every
   case structurally; the predicate `jasminCTSafe` recurses into
   bodies/branches just like `isCT_LowCT'` does.

2. **`Jasminc.compilesTo`** witness.  As in `JasminCompilerBridge`'s
   smoke test, the actual x86 binary that `jasminc` emits is supplied
   by the build pipeline; on the Lean side we treat it as a parameter.

`SSALeakage` and `JasminToSSA` co-import cleanly, so
`JasminCompilerBridge` and `LowCTToJasmin` are imported above. -/

/-- A subset of `LowCT` for which `toJasminCmd`'s output is
accepted by the Jasmin syntactic CT whitelist `isCT_Cmd`.

After the C3.4 whitelist extension to `JasminCT.lean` (admitting
`Parr_init`, `Cif` on the public-flag guard shape, `Ccall`, and the
`STORE64`/`CLONE_TOWER` assembly intrinsics), every LowCT
constructor lowers to a CT-accepted Jasmin shape:

* `RSkip`              → `[]` (vacuously CT)
* `RSeq c1 c2`         → `toJasminCmd c1 ++ toJasminCmd c2`
* `RLetU64Zero _ body` → `Cassgn (Lvar _) AT_none .sword (Pconst 0) :: ...`
* `RScalarSet _ _`     → `[Cassgn (Lvar _) AT_none .sword (Papp1 (Oword_of_int U64) (Pconst _))]`
* `RWhileNz _ body`    → `[Cwhile [] (Papp2 (Oneq U64) (Pvar _) (Pconst 0)) ...]`
* **`RLetZero _ _ body`**  → `Cassgn (Lvar _) _ _ (Parr_init n) :: ...` (C3.4)
* **`RCall _ _ _`**        → `[Ccall .DoNotInline [_] {name := f} _]` (C3.4)
* **`RCloneCall _ …`**     → `Copn _ _ (Oasm "CLONE_TOWER") _ :: Ccall …` (C3.4)
* **`RIfNz _ ct cf`**      → `[Cif (Papp2 (Oneq U64) (Pvar _) (...)) _ _]` (C3.4)
* **`RLimbStore _ _ _`**   → `[Copn _ _ (Oasm "STORE64") _]` (C3.4)

The new entries recurse on bodies/branches just like the original
five.  `RScalarSet`, `RCall`, `RCloneCall`, `RLimbStore` carry no
sub-`LowCT`, so no recursive obligation.  The connector lemma
`isCT_Cmd_of_jasminCTSafe` covers all 10 constructors. -/
def jasminCTSafe : LowCT → Bool
  | .RSkip                  => true
  | .RSeq c1 c2             => jasminCTSafe c1 && jasminCTSafe c2
  | .RLetU64Zero _ body     => jasminCTSafe body
  | .RScalarSet _ _         => true
  | .RWhileNz _ body        => jasminCTSafe body
  -- C3.4 additions:
  | .RLetZero _ _ body      => jasminCTSafe body
  | .RCall _ _ _            => true
  | .RCloneCall _ _ _ _ _ _ => true
  | .RIfNz _ ct cf          => jasminCTSafe ct && jasminCTSafe cf
  | .RFor _ _ body          => jasminCTSafe body
  | .RForRuntime _ _ body   => jasminCTSafe body
  | .RLimbStore _ _ _       => true
  -- Phase R5: lowers to a STORE64 `Copn` whose value argument is the lowered
  -- `SExpr`.  Unlike `RLimbStore` (literal value, always CT), a runtime
  -- expression is CT-safe exactly when its lowered `PExpr` passes the
  -- (deliberately shallow) `isCT_PExpr` whitelist — e.g. `a[i] + b[i]`
  -- (`Papp2 Oadd (Pvar) (Pvar)`) is accepted, but a deeply-nested arithmetic
  -- tree is not.
  | .RLimbStoreExpr _ _ e   =>
      CatCrypt.Crypto.Jasmin.isCT_PExpr
        (CatCrypt.Crypto.Jasmin.LowCT.sexprToPExpr e)
  -- #235: the back-end `isCT_InstrR` whitelist now covers the lowerings of
  -- these constructors, so they are admitted here (previously rejected
  -- pending the whitelist extension).  Each citation is to
  -- CT_INSTRUCTION_REFERENCES.md.
  --   `RCallSwap f` → two sequential `Ccall`s.  Compositional CT (the
  --   call mechanism is CT-neutral, reduces to callee CT) — §"Multi-output
  --   call".  The `isCT_InstrR` `Ccall` clause accepts both.
  | .RCallSwap _ _ _ _      => true
  --   `RCallN f` → multi-output `Ccall`.  Compositional CT (§"Multi-output
  --   call").
  | .RCallN _ _ _           => true
  --   `RSelect` → `Copn (Oasm "CMOV")`.  CMOVcc is on the Intel DOIT list
  --   and is *the* branchless CT selection primitive (§"CMOV / branchless
  --   select").
  | .RSelect _ _ _ _        => true
  -- `RAssert` lowers to the empty Cmd `[]`, which is trivially CT.
  | .RAssert _              => true
  | .RBlock body            => jasminCTSafe body
  -- #235: helper definition / call.  `RFnDef body cont` → `body ++ cont`
  -- (compositional, reduce to body+cont CT — §"Multi-output call"
  -- compositionality); `RFnCall f` → multi-output `Ccall` (compositional CT).
  | .RFnDef _ _ _ body cont => jasminCTSafe body && jasminCTSafe cont
  | .RFnCall _ _ _          => true
  -- Phase I (2026-05-03): tuple component load lowers to `[]` at
  -- this layer, so the resulting Jasmin Cmd is trivially CT.
  | .RTupleLoad _ _ _       => true
  -- #229 / Phase RND (2026-05-30): the dynamic-index array store/load and the
  -- SExpr scalar-set lower to real instructions.  Under Phase RND,
  -- `LowCTToJasmin.toJasminCmd` emits:
  --   * `.RArrStore arr idxVar src` → `Cassgn (Laset _ _ _ (Pvar idxVar)) _ _ _`
  --   * `.RArrLoad dst src idxVar`  → `Cassgn (Lvar _) _ _ (Pget _ _ _ (Pvar idxVar))`
  --   * `.RScalarSetExpr x e`       → `Cassgn (Lvar x) _ _ (sexprToPExpr e)` (or a
  --     `Copn MULX/IMUL` for the high-word multiplies), where `sexprToPExpr e`
  --     is a NESTED `Papp2`/`Papp1` tree for compound `e`.
  -- The back-end `isCT_InstrR`/`isCT_PExpr`/`isCT_LVal` whitelist is the CT
  -- soundness oracle (per `bench/framework/CT_INSTRUCTION_REFERENCES.md`):
  --   * a `Pvar`-indexed `Laset`/`Pget` leaks a SECRET-DEPENDENT address (the
  --     index is a runtime scalar, not a `Pconst`), so it is correctly NOT in
  --     the whitelist — only the literal-index `RArrStoreLit`/`RArrLoadLit`
  --     (`Pconst` index → public address) are accepted.  This is precisely the
  --     #229 dynamic-index gap: admitting these arms unconditionally claimed CT
  --     for a leaking access.
  --   * `isCT_PExpr` only matches one-level `Papp2 op (Pvar _) (Pvar _|Pconst _)`,
  --     so a NESTED `sexprToPExpr` tree (e.g. `(a >> 13) + 1`) is not accepted.
  -- Sound-conservative fix: reject these three arms (`false`).  A dynamic-index
  -- array access must be routed through `RArrStoreLit`/`RArrLoadLit` (literal,
  -- public index) to be admitted; compound scalar arithmetic must be unfolded
  -- into single-op `RScalarSet` steps.  Soundly accepting a dynamic
  -- index under a public-index hypothesis requires the `LevelTable`-threaded
  -- `cmdCT` analyser (`LowCTCTAnalysis.lean`, `cmdCT_sound`); `jasminCTSafe`
  -- carries no level info, so it cannot gate on index publicness here.  See
  -- `bench/framework/CMDCT_CONSOLIDATION_229.md` for the consolidation plan.
  | .RArrStore _ _ _        => false
  | .RArrLoad _ _ _         => false
  | .RScalarSetExpr _ _     => false
  -- #235: literal-indexed array store/load lower to a `Cassgn` with a
  -- `Laset`/`Pget` at a **literal (`Pconst`) index**.  The back-end
  -- `isCT_InstrR` whitelist now admits these (the leaked address is the
  -- literal index — public/data-independent — per CT_INSTRUCTION_REFERENCES.md
  -- §"Public/constant-index memory"), so they are accepted here.  A *secret*
  -- index would lower to a `Pvar`-index shape, which the back-end does NOT
  -- whitelist (falls through to `false`).
  | .RArrStoreLit _ _ _     => true
  | .RArrLoadLit _ _ _      => true
  | .RCallDstThreaded _ _ _ => true

/-- `isCT_Cmd` is preserved by list append.  Helper for the connector's
`RSeq` case (where `toJasminCmd (.RSeq c1 c2) = toJasminCmd c1 ++ toJasminCmd c2`). -/
private lemma isCT_Cmd_append (c1 c2 : CatCrypt.Crypto.Jasmin.Cmd) :
    CatCrypt.Crypto.Jasmin.isCT_Cmd (c1 ++ c2) =
      (CatCrypt.Crypto.Jasmin.isCT_Cmd c1 && CatCrypt.Crypto.Jasmin.isCT_Cmd c2) := by
  simp [CatCrypt.Crypto.Jasmin.isCT_Cmd_eq_all, List.all_append]

/-- Track C3.4 helper: every `Located` argument list passed to `RCall` /
`RCloneCall` is lowered to a list of `Pvar`s (via `locToPExpr`), each
of which is unconditionally CT.  Used to discharge the `args.all
isCT_PExpr` obligation in the `Ccall` clause of `isCT_InstrR`. -/
private lemma all_locToPExpr_isCT (args : List CatCrypt.Crypto.Jasmin.LowCT.Located) :
    (args.map CatCrypt.Crypto.Jasmin.LowCT.locToPExpr).all
        CatCrypt.Crypto.Jasmin.isCT_PExpr = true := by
  induction args with
  | nil => rfl
  | cons _ rest ih =>
    simp only [List.map_cons, List.all_cons, ih, Bool.and_true]
    rfl

/-- Companion to `all_locToPExpr_isCT` for l-value lists: every `Located`
destination lowered via `locToLVal` is an `Lvar`, which is unconditionally
CT.  Discharges the `lvs.all isCT_LVal` obligation in the `Ccall` clause for
the multi-destination call constructors (`RCallN`/`RFnCall`). -/
private lemma all_locToLVal_isCT (dests : List CatCrypt.Crypto.Jasmin.LowCT.Located) :
    (dests.map CatCrypt.Crypto.Jasmin.LowCT.locToLVal).all
        CatCrypt.Crypto.Jasmin.isCT_LVal = true := by
  induction dests with
  | nil => rfl
  | cons _ rest ih =>
    simp only [List.map_cons, List.all_cons, ih, Bool.and_true]
    rfl

/-- **Connector lemma (C3.3 step 1, extended by C3.4)**: on the
`jasminCTSafe` fragment of `LowCT`, the Jasmin command produced
by `toJasminCmd` is syntactically constant-time (`isCT_Cmd`).

Proof: structural induction on `c` covering all 10 LowCT
constructors.  Each accepted shape unfolds to one or two
`isCT_InstrR` clauses that close by `rfl` after unfolding the
defining equations of `toJasminCmd` and `isCT_Cmd`.  The `RSeq`
case uses `isCT_Cmd_append`; the `RCall` and `RCloneCall` cases use
`all_locToPExpr_isCT` to discharge the `args.all isCT_PExpr`
obligation in the `Ccall` clause; the `RIfNz`/`RWhileNz` cases do
not need their branch IHs (the `isCT_InstrR` clauses for `Cif`/
`Cwhile` only inspect the guard, not the bodies — matching the
existing `Cfor` handling).  Soundness of the body-erasure pattern
is preserved by the source-level `jasminCTSafe`'s recursion on
sub-`LowCT`s. -/
theorem isCT_Cmd_of_jasminCTSafe (c : LowCT) (h : jasminCTSafe c = true) :
    CatCrypt.Crypto.Jasmin.isCT_Cmd
      (CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd c) = true := by
  induction c with
  | RSkip => rfl
  | RSeq c1 c2 ih1 ih2 =>
    simp only [jasminCTSafe, Bool.and_eq_true] at h
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RSeq, isCT_Cmd_append,
               ih1 h.1, ih2 h.2, Bool.and_self]
  | RLetU64Zero x body ih =>
    simp only [jasminCTSafe] at h
    have hb := ih h
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RLetU64Zero,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, Bool.and_eq_true]
    exact ⟨rfl, hb⟩
  | RScalarSet x v =>
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RScalarSet,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, List.all_nil,
               Bool.and_true]
    rfl
  | RWhileNz x body ih =>
    simp only [jasminCTSafe] at h
    have hb := ih h
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RWhileNz,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, Bool.and_eq_true,
               List.all_nil, and_true]
    -- post body-recursion: `isCT_InstrR (Cwhile [] guard cafter) = isCT_Cmd cafter`,
    -- so the `Cwhile` obligation is exactly the body IH `hb`.
    show CatCrypt.Crypto.Jasmin.isCT_Cmd (CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd body) = true
    exact hb
  | RFor x n body ih =>
    -- toJasminCmd lowers `RFor x n body` to the static unrolling
    -- `unrollForJ x (toJasminCmd body) n`, which is `n` repetitions of
    -- a `Cassgn` (the loop-counter scalarSet, always CT-safe) followed by
    -- `toJasminCmd body`.  Hence it's CT iff `toJasminCmd body` is CT,
    -- which follows from the body IH.
    simp only [jasminCTSafe] at h
    have hb := ih h
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RFor]
    -- Reduce `isCT_Cmd` to the list-wide `List.all` form (after body
    -- recursion `isCT_Cmd` is not definitionally `List.all`; `isCT_Cmd_eq_all`
    -- bridges the two so the unroll induction below goes through).
    rw [CatCrypt.Crypto.Jasmin.isCT_Cmd_eq_all]
    rw [CatCrypt.Crypto.Jasmin.isCT_Cmd_eq_all] at hb
    induction n with
    | zero => rfl
    | succ k ihk =>
        simp only [CatCrypt.Crypto.Jasmin.LowCT.unrollForJ,
                   List.all_append, List.all_cons,
                   Bool.and_eq_true]
        refine ⟨ihk, ?_, ?_⟩
        · -- The scalarSet `Cassgn` is always CT (its PExpr is a constant).
          rfl
        · -- The body is CT by hb (in `List.all body isCT_InstrR = true` form).
          exact hb
  | RForRuntime x bound body ih =>
    -- toJasminCmd rejects the runtime loop (foldNode leaf → `[]`), so the
    -- lowered program is empty and trivially CT.
    rfl
  -- C3.4: RLetZero lowers to `Cassgn (Lvar _) _ _ (Parr_init n) :: body`.
  -- The first instruction matches `Cassgn (.Lvar _) _ _ (.Parr_init _)`,
  -- which is in `isCT_PExpr` (Parr_init clause), so `isCT_InstrR` accepts.
  | RLetZero x t body ih =>
    simp only [jasminCTSafe] at h
    have hb := ih h
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RLetZero,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, Bool.and_eq_true]
    exact ⟨rfl, hb⟩
  -- C3.4: RCall lowers to a single `Ccall .DoNotInline [dest] f args`.
  -- Args are `Pvar`s built by `locToPExpr`, which are CT.
  | RCall f dest args =>
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RCall,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, List.all_nil,
               Bool.and_true]
    show ([CatCrypt.Crypto.Jasmin.LowCT.locToLVal dest].all
              CatCrypt.Crypto.Jasmin.isCT_LVal &&
          (args.map CatCrypt.Crypto.Jasmin.LowCT.locToPExpr).all
              CatCrypt.Crypto.Jasmin.isCT_PExpr) = true
    rw [all_locToPExpr_isCT]; rfl
  -- C3.4: RCloneCall lowers to `Copn [Lvar cv] _ (Oasm "CLONE_TOWER") [..] ::
  -- Ccall .DoNotInline [dest] f args :: []`.  Both shapes match.
  | RCloneCall _ _ _ f dest args =>
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RCloneCall,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, List.all_nil,
               Bool.and_true]
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · -- CLONE_TOWER Copn: intrinsic + Lvar lvs + Pvar args.
      rfl
    · -- Inner Ccall: same shape as RCall.
      show ([CatCrypt.Crypto.Jasmin.LowCT.locToLVal dest].all
                CatCrypt.Crypto.Jasmin.isCT_LVal &&
            (args.map CatCrypt.Crypto.Jasmin.LowCT.locToPExpr).all
                CatCrypt.Crypto.Jasmin.isCT_PExpr) = true
      rw [all_locToPExpr_isCT]; rfl
  -- C3.4: RIfNz lowers to a single `Cif (Papp2 (Oneq U64) (Pvar _) ...)
  -- (toJasminCmd ct) (toJasminCmd cf)`.  The `Cif` clause in `isCT_InstrR`
  -- accepts the public-flag guard shape regardless of the branches.
  | RIfNz e ct cf ih1 ih2 =>
    simp only [jasminCTSafe, Bool.and_eq_true] at h
    -- Branch IHs are unused (matches the Cwhile pattern: the
    -- isCT_InstrR clause for `Cif` does not recurse into branches).
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RIfNz,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, List.all_nil,
               Bool.and_true]
    rfl
  -- C3.4: RLimbStore lowers to a single `Copn [locToLVal loc] _
  -- (Oasm "STORE64") [...]`.  The intrinsic is on the C3.4 whitelist.
  | RLimbStore loc idx v =>
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RLimbStore,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, List.all_nil,
               Bool.and_true]
    rfl
  -- Phase R5: RLimbStoreExpr lowers to a STORE64 `Copn` whose value arg is
  -- `sexprToPExpr e`.  CT iff that arg is `isCT_PExpr`, which is exactly the
  -- `jasminCTSafe` guard `h`.
  | RLimbStoreExpr loc idx e =>
    simp only [jasminCTSafe] at h
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RLimbStoreExpr,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, List.all_nil,
               Bool.and_true]
    show CatCrypt.Crypto.Jasmin.isCT_InstrR
           (.Copn [CatCrypt.Crypto.Jasmin.LowCT.locToLVal loc]
              .AT_none (.Oasm { name := "STORE64" })
              [CatCrypt.Crypto.Jasmin.LowCT.locToPExpr loc,
               .Pconst ↑idx,
               CatCrypt.Crypto.Jasmin.LowCT.sexprToPExpr e]) = true
    simp only [CatCrypt.Crypto.Jasmin.isCT_InstrR, List.all_cons, List.all_nil,
               Bool.and_true]
    -- ct_intrinsic "STORE64" = true; lvs/first two args CT by rfl; the value
    -- arg's CT-ness is exactly `h`.
    simp only [h]
    rfl
  -- #235: RCallSwap/RCallN/RSelect lower to back-end-accepted
  -- shapes (two/multi `Ccall`, `CMOV` `Copn`).
  -- RAssert lowers to the empty Cmd; RBlock recurses.
  -- `RCallSwap f d1 d2 args` → `[Ccall [d1] f args, Ccall [d2] f args]`.
  | RCallSwap f dest1 dest2 args =>
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RCallSwap,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, List.all_nil,
               Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · show ([CatCrypt.Crypto.Jasmin.LowCT.locToLVal dest1].all
                CatCrypt.Crypto.Jasmin.isCT_LVal &&
            (args.map CatCrypt.Crypto.Jasmin.LowCT.locToPExpr).all
                CatCrypt.Crypto.Jasmin.isCT_PExpr) = true
      rw [all_locToPExpr_isCT]; rfl
    · show ([CatCrypt.Crypto.Jasmin.LowCT.locToLVal dest2].all
                CatCrypt.Crypto.Jasmin.isCT_LVal &&
            (args.map CatCrypt.Crypto.Jasmin.LowCT.locToPExpr).all
                CatCrypt.Crypto.Jasmin.isCT_PExpr) = true
      rw [all_locToPExpr_isCT]; rfl
  -- `RCallN f dests args` → `[Ccall (dests) f (args)]`.
  | RCallN f dests args =>
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RCallN,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, CatCrypt.Crypto.Jasmin.isCT_InstrR,
               Bool.and_true]
    show ((dests.map CatCrypt.Crypto.Jasmin.LowCT.locToLVal).all
              CatCrypt.Crypto.Jasmin.isCT_LVal &&
          (args.map CatCrypt.Crypto.Jasmin.LowCT.locToPExpr).all
              CatCrypt.Crypto.Jasmin.isCT_PExpr) = true
    rw [all_locToLVal_isCT, all_locToPExpr_isCT, Bool.and_true]
  -- `RSelect dst sel src0 src1` → `[Copn [dst] (Oasm "CMOV") [...]]`.
  -- "CMOV" is on the `ct_intrinsic` whitelist; the lval is an `Lvar` and the
  -- args are `Pvar`s, all CT.
  | RSelect dst sel src0 src1 =>
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RSelect,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, List.all_nil,
               Bool.and_true]
    rfl
  | RAssert _ =>
    simp [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RAssert,
          CatCrypt.Crypto.Jasmin.isCT_Cmd]
  | RBlock body ih =>
    simp only [jasminCTSafe] at h
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RBlock]
    exact ih h
  -- #235: `RFnDef _ _ _ body cont` → `toJasminCmd body ++ toJasminCmd cont`
  -- (compositional); `RFnCall f dests args` → `[Ccall (dests) f (args)]`.
  | RFnDef _ _ _ body cont ihBody ihCont =>
    simp only [jasminCTSafe, Bool.and_eq_true] at h
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RFnDef, isCT_Cmd_append,
               ihBody h.1, ihCont h.2, Bool.and_self]
  | RFnCall f dests args =>
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RFnCall,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, CatCrypt.Crypto.Jasmin.isCT_InstrR,
               Bool.and_true]
    show ((dests.map CatCrypt.Crypto.Jasmin.LowCT.locToLVal).all
              CatCrypt.Crypto.Jasmin.isCT_LVal &&
          (args.map CatCrypt.Crypto.Jasmin.LowCT.locToPExpr).all
              CatCrypt.Crypto.Jasmin.isCT_PExpr) = true
    rw [all_locToLVal_isCT, all_locToPExpr_isCT, Bool.and_true]
  -- Phase I: tuple component load lowers to `[]` (empty Cmd is CT).
  | RTupleLoad _ _ _ =>
    simp [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RTupleLoad,
          CatCrypt.Crypto.Jasmin.isCT_Cmd]
  -- #229 / Phase RND (2026-05-30): the dynamic-index `RArrStore`/`RArrLoad`
  -- and the SExpr `RScalarSetExpr` are now rejected by `jasminCTSafe`
  -- (their Phase-RND lowerings — `Pvar`-indexed `Laset`/`Pget` and nested
  -- `sexprToPExpr` — are NOT in the back-end `isCT_InstrR` whitelist).  The
  -- `jasminCTSafe` hypothesis `h` is therefore `false = true`, vacuous.
  | RArrStore _ _ _ => simp [jasminCTSafe] at h
  | RArrLoad _ _ _ => simp [jasminCTSafe] at h
  | RScalarSetExpr _ _ => simp [jasminCTSafe] at h
  -- #235: literal-indexed array store/load lower to a `Cassgn` whose
  -- `Laset`/`Pget` carries a literal (`Pconst`) index — now in the
  -- `isCT_InstrR` whitelist (public/data-independent address).
  -- `RArrStoreLit arr idx src` → `[Cassgn (Laset .AAscale .U8 _ (Pconst idx))
  --   _ _ (locToPExpr src)]` where `locToPExpr src` is a `Pvar`.
  | RArrStoreLit arr idx src =>
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RArrStoreLit,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, List.all_nil,
               Bool.and_true]
    rfl
  -- `RArrLoadLit dst src idx` → `[Cassgn (Lvar _) _ _ (Pget .AAscale .U8 _
  --   (Pconst idx))]`; the `Lvar` LHS + `Pget`-at-`Pconst` RHS are both CT.
  | RArrLoadLit dst src idx =>
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RArrLoadLit,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, List.all_nil,
               Bool.and_true]
    rfl
  -- `RCallDstThreaded f dst args` lowers to a single
  -- `Ccall .DoNotInline [locToLVal dst] f (locToPExpr dst :: args.map locToPExpr)`.
  -- The l-value list is a singleton CT `Lvar`; every argument is a `Pvar`
  -- (built by `locToPExpr`), hence CT — same discharge as `RCall`.
  | RCallDstThreaded f dst args =>
    simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminCmd_RCallDstThreaded,
               CatCrypt.Crypto.Jasmin.isCT_Cmd, List.all_cons, List.all_nil,
               Bool.and_true]
    show ([CatCrypt.Crypto.Jasmin.LowCT.locToLVal dst].all
              CatCrypt.Crypto.Jasmin.isCT_LVal &&
          (CatCrypt.Crypto.Jasmin.LowCT.locToPExpr dst ::
            args.map CatCrypt.Crypto.Jasmin.LowCT.locToPExpr).all
              CatCrypt.Crypto.Jasmin.isCT_PExpr) = true
    simp only [List.all_cons, all_locToPExpr_isCT, Bool.and_true]
    rfl

/-- **End-to-end CT transfer from LowCT source to x86-64**
(track C3.3 step 2).

Composes:

* (Lean-side, **Qed**) `isCT_LowCT' leaves secrets c = true` is the
  source-level acceptance witness fed into the front end.
* (Lean-side, **Qed**) `isCT_Cmd_of_jasminCTSafe` lifts a
  `jasminCTSafe`-checked `LowCT` to the syntactic Jasmin CT
  predicate `isCT_Cmd` on the emitted command.  This is the
  *connector* lemma — the C3.3 step that bridges the two halves.
* (Axiom, citing arXiv 2511.11292) `cryptoSSA_to_x86_preserves_ct`
  in `JasminCompilerBridge.lean` carries `isCT_Cmd` across `jasminc`
  to the x86-64 leakage predicate `X86Prog.isCT`.

Trust dependencies:

* The Lean-side connector lemma `isCT_Cmd_of_jasminCTSafe` — lifting
  `jasminCTSafe` to the Jasmin syntactic CT predicate `isCT_Cmd` on
  the emitted command — is proved in full.
* The `jasminc_preserves_ct` axiom in `JasminCompilerBridge.lean`
  cites arXiv 2511.11292 (Arranz-Olmos et al., 2025).
* The opaque types `X86Prog`, `Jasminc.compilesTo`, and
  `X86Prog.isCT` reflect the Jasmin paper's hardware-software
  contract assumptions; their soundness depends on `jasminc`'s
  implementation matching its formal model.

The `isCT_LowCT' leaves secrets c` hypothesis is preserved (and
unused in the proof body) as the front-end acceptance contract — it
documents what the user must discharge before invoking the
translator. -/
theorem rustcmd_ct_implies_x86_ct
    {leaves : CTLeaves} {secrets : SecretSet}
    (c : LowCT)
    (_h_ct : isCT_LowCT' leaves secrets c = true)
    (h_safe : jasminCTSafe c = true)
    (params results : List Located) (fname : String)
    (x86 : CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge.X86Prog)
    (h_compile : CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge.Jasminc.compilesTo
                   (CatCrypt.Crypto.Jasmin.LowCT.toJasminProg fname params results c) x86) :
    CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge.X86Prog.isCT x86 := by
  -- Step A: invoke the back-end CT bridge.  Its hypothesis is that *every*
  -- function declaration in the Jasmin program has a CT body.  Our
  -- `toJasminProg` produces a single function whose body is `toJasminCmd c`.
  apply CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge.cryptoSSA_to_x86_preserves_ct
        (CatCrypt.Crypto.Jasmin.LowCT.toJasminProg fname params results c) x86 h_compile
  intro fd hfd
  -- Step B: discharge the per-function CT obligation by structural induction
  -- on the (singleton) `funcs` list, then by the connector lemma.
  simp only [CatCrypt.Crypto.Jasmin.LowCT.toJasminProg, List.mem_singleton] at hfd
  subst hfd
  simp only [CatCrypt.Crypto.Jasmin.LowCT.toFunDecl]
  exact isCT_Cmd_of_jasminCTSafe c h_safe

/-! ## §4  Smoke test

A small LowCT program that consists entirely of public-local
operations: an `RLetU64Zero` followed by an `RScalarSet`.  The
syntactic CT predicate accepts it under `emptySecrets` and any leaves
(no `RCall`s in the program), and `translate` succeeds.  We then
exercise the bridge by slotting in the trivial tail program
`.ret .here`. -/

/-- A trivial CT-leaf whitelist that accepts no leaves; suffices because
the smoke program contains no `RCall`. -/
def smokeBridgeLeaves : CTLeaves := fun _ => false

/-- The smoke LowCT program: `let x = 0u64 in (i := 7)`.  No control
flow, no calls, all locals are public. -/
def smokeBridgeProg : LowCT :=
  .RLetU64Zero "x" (.RScalarSet "i" 7)

/-- The smoke program is accepted by the relaxed CT predicate. -/
theorem smokeBridgeProg_isCT' :
    isCT_LowCT' smokeBridgeLeaves emptySecrets smokeBridgeProg = true := by
  -- `decide` does not reduce
  -- `isCT_LowCT'` past the pattern-match elaboration boundary
  -- (Lean 4.28 well-founded recursion compiles to a wrapper that
  -- `decide` cannot unfold).  `native_decide` evaluates through the
  -- compiled code.
  native_decide

/-- The smoke program also satisfies the over-strict predicate (it has
no control flow), so the strict-corollary path applies. -/
theorem smokeBridgeProg_isCT :
    isCT_LowCT smokeBridgeLeaves smokeBridgeProg = true := by native_decide

/-- The dialect front `translateDialectControl` succeeds on the smoke program
from the empty VarMap. -/
theorem smokeBridge_translateDialect_isSome :
    (translateDialectControl (Γ := []) VarMap.empty smokeBridgeProg).isSome := by
  native_decide

/-! ## §5  Smoke test for C3.3 end-to-end theorem

`smokeBridgeProg` is in the `jasminCTSafe` fragment (it consists of
`RLetU64Zero` plus `RScalarSet`, both accepted by `jasminCTSafe`).
We exercise `rustcmd_ct_implies_x86_ct` end-to-end on it.

The `Jasminc.compilesTo` hypothesis is a parameter (no concrete x86
binary exists in the test setup — that is supplied by the `jasminc`
toolchain at extraction time), and the `params/results/fname`
metadata is left as parameters too.  The point of the smoke test is
to check that the *axiom shape* typechecks: given a concrete x86
binary with a `compilesTo` witness, the theorem fires and produces
`X86Prog.isCT` on it. -/

/-- The smoke program is in the `jasminCTSafe` fragment. -/
theorem smokeBridgeProg_jasminCTSafe :
    jasminCTSafe smokeBridgeProg = true := by decide

/-- **C3.3 smoke test**: end-to-end CT transfer for the smoke program.
Given any concrete x86 binary that `jasminc` produces from
`toJasminProg fname params results smokeBridgeProg`, the binary is
constant-time. -/
example
    (params results : List Located) (fname : String)
    (x86 : CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge.X86Prog)
    (h_compile : CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge.Jasminc.compilesTo
                   (CatCrypt.Crypto.Jasmin.LowCT.toJasminProg fname params results
                     smokeBridgeProg) x86) :
    CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge.X86Prog.isCT x86 :=
  rustcmd_ct_implies_x86_ct (leaves := smokeBridgeLeaves) (secrets := emptySecrets)
    smokeBridgeProg smokeBridgeProg_isCT' smokeBridgeProg_jasminCTSafe
    params results fname x86 h_compile

/-! ## §6  Track C3.4 smoke tests

After C3.4 (extending `JasminCT.isCT_Cmd`'s whitelist to admit
`Parr_init`, `Cif`-on-public-flag, `Ccall`, `STORE64`, and
`CLONE_TOWER`), the connector covers all 10 LowCT constructors.
We exercise `jasminCTSafe`'s `RIfNz` and `RCall` branches via
`decide`. -/

/-- Smoke program using `RIfNz` (branches on a public-flag U64).
`RIfNz f then-branch else-branch`, with both branches `RSkip`. -/
def smokeBridgeProgIf : LowCT :=
  .RIfNz "flag" .RSkip .RSkip

/-- The `RIfNz` smoke program is in the C3.4-extended `jasminCTSafe`
fragment.  This `decide` exercises the `RIfNz _ ct cf` clause of
`jasminCTSafe` (recursively `jasminCTSafe ct && jasminCTSafe cf`). -/
theorem smokeBridgeProgIf_jasminCTSafe :
    jasminCTSafe smokeBridgeProgIf = true := by decide

/-- Smoke program using `RCall`: invoke `f` with no arguments,
writing into a U64 destination. -/
def smokeBridgeProgCall : LowCT :=
  .RCall "callee" { locVar := "dst", locSrc := .TU64 } []

/-- The `RCall` smoke program is in the C3.4-extended `jasminCTSafe`
fragment. -/
theorem smokeBridgeProgCall_jasminCTSafe :
    jasminCTSafe smokeBridgeProgCall = true := by decide

/-! ## §8  Linking the user-facing CT predicate to the certified one (#234, collapsed in #235)

The end-to-end chain `rustcmd_ct_implies_x86_ct` is *driven* by the
certified predicate `jasminCTSafe`.  This section supplies the link from
the user-facing source predicate `isCT_LowCT'` to it.

### The two predicates now AGREE (#235)

#234 found `isCT_LowCT'` (`LowCTCT.lean`, user-facing) and
`jasminCTSafe` (this file, certified — the one `isCT_Cmd_of_jasminCTSafe`
consumes) to be *incomparable*, disagreeing on eight constructors whose
Jasmin lowering the back-end `isCT_InstrR` whitelist did not yet accept,
and bounded the gap with the decidable side-condition
`inCertifiedCTFragment`.  #235 closes the gap on both sides, grounded in
`bench/framework/CT_INSTRUCTION_REFERENCES.md`:

* The back-end `isCT_InstrR` whitelist (`JasminCT.lean`) was extended to
  accept the CT-safe lowerings of those constructors:
  - `CMOV` (`RSelect`) — Intel DOIT-listed branchless select;
  - literal-index `Laset`/`Pget` (`RArrStoreLit`/`RArrLoadLit`) — public,
    data-independent store/load address;
  - multi-output `Ccall` (`RCallN`/`RFnCall`/`RCallSwap`) — already
    accepted (compositional CT, call mechanism CT-neutral);
  - `Cfn`/append (`RFnDef`) — compositional, via the body lowering.
* `jasminCTSafe` was correspondingly relaxed on those constructors
  (accepted or recursed).

The result: on **every** constructor, `isCT_LowCT' leaves secrets c =
true` implies `jasminCTSafe c = true`.  For the call constructors the
implication is monotone (`isCT_LowCT'` gates on `leaves f`, which is a
*restriction*; `jasminCTSafe` accepts unconditionally, so any
`isCT_LowCT'`-accepted call is `jasminCTSafe`-accepted).  For the
structural constructors both recurse identically.

`inCertifiedCTFragment` is the decidable fragment on which `isCT_LowCT'`
and `jasminCTSafe` **agree**.  #229 / Phase RND (2026-05-30) re-narrowed it:
the dynamic-index `RArrStore`/`RArrLoad` and the SExpr `RScalarSetExpr` are
excluded from the agreeing fragment, because their Phase-RND lowerings
(`Pvar`-indexed `Laset`/`Pget`; nested `sexprToPExpr`) are correctly rejected
by the back-end `isCT_Cmd` whitelist while `isCT_LowCT'` (a source-level
leak-trace abstraction) still accepts them.  The link lemma therefore again
carries this fragment side-condition.  See
`bench/framework/CMDCT_CONSOLIDATION_229.md`. -/

/-- Decidable fragment side-condition: the `LowCT` constructors on which
`isCT_LowCT'` and `jasminCTSafe` agree.

#229 / Phase RND (2026-05-30): the three constructors whose Phase-RND Jasmin
lowering is NOT in the back-end `isCT_Cmd` whitelist — dynamic-index
`RArrStore`/`RArrLoad` (`Pvar`-indexed `Laset`/`Pget`, a secret-dependent
address) and `RScalarSetExpr` (nested `sexprToPExpr`) — are EXCLUDED.  Their
literal-index counterparts (`RArrStoreLit`/`RArrLoadLit`, `Pconst` index →
public address) remain in the fragment.  Structural constructors recurse;
everything else is accepted. -/
def inCertifiedCTFragment : LowCT → Bool
  | .RArrStore _ _ _        => false
  | .RArrLoad _ _ _         => false
  | .RScalarSetExpr _ _     => false
  -- Phase R5: runtime-valued limb store is excluded from the certified-CT
  -- fragment (like the other runtime-`SExpr` constructors).  Its lowering's
  -- CT-ness depends on the stored expression passing `isCT_PExpr`, which the
  -- shallow whitelist does not guarantee in general, so `jasminCTSafe` is not
  -- unconditionally `true` and the monotone implication does not hold here.
  | .RLimbStoreExpr _ _ _   => false
  | .RSeq c1 c2             => inCertifiedCTFragment c1 && inCertifiedCTFragment c2
  | .RLetZero _ _ body      => inCertifiedCTFragment body
  | .RLetU64Zero _ body     => inCertifiedCTFragment body
  | .RIfNz _ ct cf          => inCertifiedCTFragment ct && inCertifiedCTFragment cf
  | .RWhileNz _ body        => inCertifiedCTFragment body
  | .RFor _ _ body          => inCertifiedCTFragment body
  | .RForRuntime _ _ body   => inCertifiedCTFragment body
  | .RBlock body            => inCertifiedCTFragment body
  | .RFnDef _ _ _ body cont => inCertifiedCTFragment body && inCertifiedCTFragment cont
  | _                       => true

/-- **Link lemma (#234, re-gated by the fragment in #229)**: on the
`inCertifiedCTFragment` fragment, a user-facing `isCT_LowCT'` witness
yields the certified `jasminCTSafe` witness that the end-to-end chain
consumes.

The fragment hypothesis filters exactly the three constructors on which the
two predicates now disagree (dynamic-index `RArrStore`/`RArrLoad`,
`RScalarSetExpr`); on every other constructor the two agree, by structural
induction:
* structural (`RSeq`/`RLetZero`/`RLetU64Zero`/`RIfNz`/`RWhileNz`/`RFor`/
  `RBlock`/`RFnDef`) — both predicates recurse identically; close by IH
  (carrying the fragment hypothesis through);
* the three excluded constructors — `inCertifiedCTFragment = false`, so the
  fragment hypothesis is vacuous;
* every remaining call/structural-leaf constructor — `jasminCTSafe = true`
  by `rfl` (it accepts unconditionally).

Axiom-free of `jasminc_preserves_ct`: a pure syntactic fact. -/
theorem isCT_LowCT'_imp_jasminCTSafe
    {leaves : CTLeaves} {secrets : SecretSet} (c : LowCT)
    (hct : isCT_LowCT' leaves secrets c = true)
    (hfrag : inCertifiedCTFragment c = true) :
    jasminCTSafe c = true := by
  induction c with
  | RSeq c1 c2 ih1 ih2 =>
    simp only [isCT_LowCT', Bool.and_eq_true] at hct
    simp only [inCertifiedCTFragment, Bool.and_eq_true] at hfrag
    simp only [jasminCTSafe, Bool.and_eq_true]
    exact ⟨ih1 hct.1 hfrag.1, ih2 hct.2 hfrag.2⟩
  | RLetZero _ _ body ih =>
    simp only [isCT_LowCT'] at hct
    simp only [inCertifiedCTFragment] at hfrag
    simpa only [jasminCTSafe] using ih hct hfrag
  | RLetU64Zero _ body ih =>
    simp only [isCT_LowCT'] at hct
    simp only [inCertifiedCTFragment] at hfrag
    simpa only [jasminCTSafe] using ih hct hfrag
  | RIfNz _ ct cf ih1 ih2 =>
    simp only [isCT_LowCT', Bool.and_eq_true] at hct
    simp only [inCertifiedCTFragment, Bool.and_eq_true] at hfrag
    simp only [jasminCTSafe, Bool.and_eq_true]
    exact ⟨ih1 hct.1.2 hfrag.1, ih2 hct.2 hfrag.2⟩
  | RWhileNz _ body ih =>
    simp only [isCT_LowCT', Bool.and_eq_true] at hct
    simp only [inCertifiedCTFragment] at hfrag
    simpa only [jasminCTSafe] using ih hct.2 hfrag
  | RFor _ _ body ih =>
    simp only [isCT_LowCT'] at hct
    simp only [inCertifiedCTFragment] at hfrag
    simpa only [jasminCTSafe] using ih hct hfrag
  | RForRuntime _ _ body ih =>
    simp only [isCT_LowCT'] at hct
    simp only [inCertifiedCTFragment] at hfrag
    simpa only [jasminCTSafe] using ih hct hfrag
  | RBlock body ih =>
    simp only [isCT_LowCT'] at hct
    simp only [inCertifiedCTFragment] at hfrag
    simpa only [jasminCTSafe] using ih hct hfrag
  | RFnDef _ _ _ body cont ihBody ihCont =>
    simp only [isCT_LowCT', Bool.and_eq_true] at hct
    simp only [inCertifiedCTFragment, Bool.and_eq_true] at hfrag
    simp only [jasminCTSafe, Bool.and_eq_true]
    exact ⟨ihBody hct.1 hfrag.1, ihCont hct.2 hfrag.2⟩
  -- #229: the three dynamic-index / SExpr constructors are excluded from the
  -- fragment, so `hfrag : false = true` is vacuous.
  | RArrStore _ _ _ => simp only [inCertifiedCTFragment, Bool.false_eq_true] at hfrag
  | RArrLoad _ _ _ => simp only [inCertifiedCTFragment, Bool.false_eq_true] at hfrag
  | RScalarSetExpr _ _ => simp only [inCertifiedCTFragment, Bool.false_eq_true] at hfrag
  -- Phase R5: RLimbStoreExpr is excluded from the fragment too.
  | RLimbStoreExpr _ _ _ => simp only [inCertifiedCTFragment, Bool.false_eq_true] at hfrag
  -- All remaining constructors: `jasminCTSafe = true` by `rfl` (it accepts
  -- them unconditionally; the `isCT_LowCT'` `leaves` gate on calls is a
  -- restriction, so the implication is monotone).
  | _ => rfl

/-- **End-to-end CT from the user-facing predicate (#234)**.

A companion to `rustcmd_ct_implies_x86_ct` whose CT hypothesis is the
*user-facing* `isCT_LowCT'` (plus the decidable fragment
side-condition `inCertifiedCTFragment`) rather than the internal
`jasminCTSafe`.  It chains the link lemma
`isCT_LowCT'_imp_jasminCTSafe` into the existing bridge, so a user who
certifies their source program with `isCT_LowCT'` — the predicate the
Signal pipeline theorems carry — now actually obtains the x86 CT
conclusion from the proven chain.

### Axiom boundary (honest statement of the Lean CT guarantee)

The Lean side proves only **syntactic** facts:

* `isCT_LowCT'_imp_jasminCTSafe` (this file, axiom-free) — on the
  `inCertifiedCTFragment` fragment (which #229 re-narrowed to exclude the
  dynamic-index `RArrStore`/`RArrLoad` and the SExpr `RScalarSetExpr`), the
  user-facing source predicate implies the certified one;
* `isCT_Cmd_of_jasminCTSafe` (this file, axiom-free) — `jasminCTSafe`
  lifts to the Jasmin syntactic CT-whitelist predicate `isCT_Cmd` on the
  emitted command.

The step from the syntactic whitelist `isCT_Cmd` to **actual hardware /
machine constant-time** (the opaque `X86Prog.isCT`) is the **external
axiom `jasminc_preserves_ct`** in
`JasminCompilerBridge.lean`, citing arXiv 2511.11292 (Arranz-Olmos
et al., 2025).  There is **no x86 operational semantics in this
codebase**: `X86Prog`, `Jasminc.compilesTo`, and `X86Prog.isCT` are
`opaque` with no Lean definition, so `X86Prog.isCT x86` is an
uninterpreted predicate whose meaning is imported from the cited paper's
leakage model and `jasminc`'s formal model.  Pulling
`jasminc_preserves_ct` is therefore the **boundary of the Lean CT
guarantee** — everything from `isCT_Cmd` down to the wire is trusted,
not proved here. -/
theorem rustcmd_ct_implies_x86_ct_of_isCT_LowCT'
    {leaves : CTLeaves} {secrets : SecretSet}
    (c : LowCT)
    (h_ct : isCT_LowCT' leaves secrets c = true)
    (h_frag : inCertifiedCTFragment c = true)
    (params results : List Located) (fname : String)
    (x86 : CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge.X86Prog)
    (h_compile : CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge.Jasminc.compilesTo
                   (CatCrypt.Crypto.Jasmin.LowCT.toJasminProg fname params results c) x86) :
    CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge.X86Prog.isCT x86 :=
  rustcmd_ct_implies_x86_ct (leaves := leaves) (secrets := secrets) c h_ct
    (isCT_LowCT'_imp_jasminCTSafe (leaves := leaves) (secrets := secrets) c h_ct h_frag)
    params results fname x86 h_compile

/-- The smoke program is in the `inCertifiedCTFragment` fragment (it contains
no dynamic-index array op or SExpr scalar set). -/
theorem smokeBridgeProg_inCertifiedCTFragment :
    inCertifiedCTFragment smokeBridgeProg = true := rfl

/-- **#234 smoke test**: the user-facing end-to-end corollary fires on the
smoke program, discharging the `inCertifiedCTFragment` side-condition. -/
example
    (params results : List Located) (fname : String)
    (x86 : CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge.X86Prog)
    (h_compile : CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge.Jasminc.compilesTo
                   (CatCrypt.Crypto.Jasmin.LowCT.toJasminProg fname params results
                     smokeBridgeProg) x86) :
    CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge.X86Prog.isCT x86 :=
  rustcmd_ct_implies_x86_ct_of_isCT_LowCT'
    (leaves := smokeBridgeLeaves) (secrets := emptySecrets)
    smokeBridgeProg smokeBridgeProg_isCT' smokeBridgeProg_inCertifiedCTFragment
    params results fname x86 h_compile

end CatCrypt.Crypto.SecureCompilation.LowCTCTBridge
