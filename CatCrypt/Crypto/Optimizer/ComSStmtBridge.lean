/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.SLPVectorize
public import CatCrypt.Crypto.SecureCompilation.VIR.Peephole
public import Mathlib.Logic.Function.Basic

/-!
# Bridge between the typed `Com jasminDialect` IR and the `SStmt` scalar block IR

`Optimizer/SLPVectorize.lean` proves superword-level auto-vectorization over a
standalone scalar IR `List SStmt` (register file `SRegs = String → BitVec 32`,
executor `runScalar`).  Those block-denotation lemmas live over `runScalar`; the
`Com → Com` optimizer runs over `Com.denote` / `Ctxt.Valuation`.  This module ties
the two denotations with a register-naming embedding so the SLP block lemmas
transport into `Com`-land.

The bridge is denotation-level and typed-AST throughout: there is no text or
string serialization of a `Com`.  It is partial by construction — `comToSStmt`
extracts only the packable straight-line scalar fragment (a let-chain of
`regArith` binary ops over `reg 32` whose op is one of `add` / `xor` / `or`) and
returns `none` on any other node.

## The naming and the embedding

A De Bruijn variable is named by its **level** — distance from the context
bottom — which is stable as the let-chain grows (a De Bruijn *index* is not).
`nameAtLevel` is a unary tally string, injective by length.  `embed` sends a
`Ctxt.Valuation Γ` to the `SRegs` register file that carries each binding's
value at its level name (`embed_lookup` for `reg 32` variables).

## The denotation-agreement lemmas

* `comToSStmt_runScalar` — forward simulation: when `comToSStmt c = some g`,
  `runScalar g (embed V) = embed (comEval c V)`, where `comEval` denotes the
  whole let-chain into its final context valuation.  Proved by a one-statement
  step (`exprToSStmt_step`) threaded through the chain.
* `comToSStmt_denote` — the corollary the pipeline consumes: the extracted
  block, run from the embedded inputs and read at the return variable's level
  name, equals `Com.denote c V`.

## Reassembly and the vectorizing pass

`comToSStmt` is the analysis direction; `slpVectorizeCom` is the synthesis
direction: a `Com → Com` pass that, where `comToSStmt c = some g` and
`slpDetect g` fires on a group whose shared op packs to a `JasminBinOp` and
whose lanes include the return destination, rebuilds a `Com` carrying
`JasminOp.vsimd` over two gathered `reg 128` registers, and returns its input
otherwise.  `slpVectorizeCom_denote` proves `(slpVectorizeCom c).denote V =
c.denote V`.  The reg-128 gather is `gatherCom`, a cast/shift/or chain denoting
`packLanes32`; `resolveVar` recovers each source name's `Ctxt.Var Γ`, so
`gatherCom` of the resolved sources denotes the group's `groupPack`.
`rebuildLaneCom` composes the two gathers, the packed op, and the lane scatter;
`rebuild_eq_com_denote` ties its denotation to `Com.denote c` through
`packedCom_denote`.

## Main results

* `comToSStmt`: extract the packable straight-line scalar fragment of a
  `Com jasminDialect` (a let-chain of width-32 `regArith` `add`/`xor`/`or`) into
  a `List SStmt` block, `none` on any other node.
* `comToSStmt_runScalar`: forward simulation — `runScalar` on the extracted
  block from the embedded inputs equals `embed` of the whole-chain evaluation.
* `comToSStmt_denote`: the corollary the pipeline consumes — the extracted block,
  read at the return variable's level name, equals `Com.denote`.
* `embed_lookup`: reading the embedded register file at a `reg 32` variable's
  level name returns that variable's value.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ComSStmtBridge

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.SLPVectorize
  (LaneOp SStmt SRegs runScalar SLPGroup packSrc packedResult packLanes32
   packLanes32_lane slpDetect slpDetect_members slpVectorize_block_denote)
open CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridgeCom
  (packAvx2Com packAvx2Com_denote)
open CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridge (v128Pack32_lane)
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap (vmap₂)

/-! ## 1. Level-based variable naming -/

/-- The canonical name of De Bruijn *level* `n`: a unary tally string, injective
    by length. -/
def nameAtLevel (n : Nat) : String := String.ofList (List.replicate (n + 1) 'v')

/-- `nameAtLevel` is injective. -/
theorem nameAtLevel_inj {a b : Nat} (h : nameAtLevel a = nameAtLevel b) : a = b := by
  have hd := congrArg String.toList h
  simp only [nameAtLevel, String.toList_ofList] at hd
  simpa using congrArg List.length hd

/-- Distinct levels get distinct names. -/
theorem nameAtLevel_ne {a b : Nat} (h : a ≠ b) : nameAtLevel a ≠ nameAtLevel b :=
  fun he => h (nameAtLevel_inj he)

/-- De Bruijn index of a variable (distance from the context top). -/
def varIdx {Γ : Ctxt jasminDialect} {t : JasminTy} : Ctxt.Var Γ t → Nat
  | .here => 0
  | .there v => varIdx v + 1

/-- A variable's index is below the context length. -/
theorem varIdx_lt {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t) :
    varIdx v < Γ.length := by
  induction v with
  | here => simp [varIdx]
  | there v ih => simp only [varIdx, List.length_cons]; omega

/-- The canonical name of a variable: its level `Γ.length - 1 - index`. -/
def varNm {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t) : String :=
  nameAtLevel (Γ.length - 1 - varIdx v)

/-- Weakening a variable past one binder keeps its level name. -/
theorem varNm_there {Γ : Ctxt jasminDialect} {t s : JasminTy} (v : Ctxt.Var Γ t) :
    varNm (Ctxt.Var.there (s := s) v) = varNm v := by
  simp only [varNm, varIdx, List.length_cons]
  congr 1
  omega

/-! ## 2. The valuation → register-file embedding -/

/-- Coerce a value of any `JasminTy` to the `BitVec 32` register slot: the value
    itself for `reg 32`, `0` otherwise. -/
def regVal : (t : JasminTy) → ⟦t⟧ → BitVec 32
  | .reg 32, v => v
  | _, _ => 0

/-- Embed a valuation into the scalar register file: each binding writes its
    (coerced) value at its level name. -/
def embed : {Γ : Ctxt jasminDialect} → Ctxt.Valuation Γ → SRegs
  | [], _ => fun _ => 0
  | t :: Γ', .cons v V' =>
      Function.update (embed V') (nameAtLevel Γ'.length) (regVal t v)

/-- One-binder unfolding of `embed`. -/
theorem embed_cons {t : JasminTy} {Γ' : Ctxt jasminDialect} (v : ⟦t⟧)
    (V' : Ctxt.Valuation Γ') :
    embed (HVector.cons v V')
      = Function.update (embed V') (nameAtLevel Γ'.length) (regVal t v) := rfl

/-- Reading the embedded register file at a `reg 32` variable's level name
    returns that variable's value. -/
theorem embed_lookup {Γ : Ctxt jasminDialect} (v : Ctxt.Var Γ (.reg 32))
    (V : Ctxt.Valuation Γ) : embed V (varNm v) = v.lookup V := by
  induction Γ with
  | nil => nomatch v
  | cons s Γ' ih =>
      cases V with
      | cons hv V' =>
        cases v with
        | here =>
            rw [embed_cons]
            have hk : varNm (Ctxt.Var.here : Ctxt.Var (JasminTy.reg 32 :: Γ') (.reg 32))
                = nameAtLevel Γ'.length := rfl
            rw [hk, Function.update_self]
            rfl
        | there v' =>
            rw [varNm_there, embed_cons]
            have hlt : varIdx v' < _ := varIdx_lt v'
            rw [Function.update_of_ne]
            · exact ih v' V'
            · apply nameAtLevel_ne; omega

/-! ## 2b. Resolving a level name back to a `Ctxt.Var` -/

/-- The value a resolved source contributes: the variable's value, or `0` when
    the source name resolves to no `reg 32` variable of the context. -/
def valOf {Γ : Ctxt jasminDialect} (o : Option (Ctxt.Var Γ (.reg 32)))
    (V : Ctxt.Valuation Γ) : BitVec 32 :=
  match o with
  | some v => v.lookup V
  | none => 0

/-- `regVal` on a non-`reg 32` binding is `0`. -/
theorem regVal_ne {t : JasminTy} (h : t ≠ .reg 32) (v : ⟦t⟧) : regVal t v = 0 := by
  unfold regVal
  split
  · exact absurd rfl h
  · rfl

/-- Coerce `.here` of `t :: Γ'` to a `reg 32` variable when `t = .reg 32`. -/
def hereReg32 {t : JasminTy} {Γ' : Ctxt jasminDialect} (h : t = .reg 32) :
    Ctxt.Var (t :: Γ') (.reg 32) :=
  Eq.mp (congrArg (Ctxt.Var (t :: Γ')) h) Ctxt.Var.here

/-- Resolve a level name to the `reg 32` variable of `Γ` that carries it, if any.
    A binding at level `Γ'.length` (the head of `t :: Γ'`) matches the name
    `nameAtLevel Γ'.length` when its type is `reg 32`; any other head is skipped
    under `.there`.  Names of non-`reg 32` bindings and out-of-range levels
    resolve to `none`. -/
def resolveVar : (Γ : Ctxt jasminDialect) → String → Option (Ctxt.Var Γ (.reg 32))
  | [], _ => none
  | t :: Γ', name =>
      if h : t = .reg 32 ∧ name = nameAtLevel Γ'.length then
        some (hereReg32 h.1)
      else (resolveVar Γ' name).map Ctxt.Var.there

/-- An out-of-range level name resolves to no variable. -/
theorem resolveVar_none_ge : (Γ : Ctxt jasminDialect) → (m : Nat) → Γ.length ≤ m →
    resolveVar Γ (nameAtLevel m) = none
  | [], _, _ => rfl
  | t :: Γ', m, hle => by
      have hlt : Γ'.length < m := by simpa using hle
      have hne : ¬ (t = .reg 32 ∧ nameAtLevel m = nameAtLevel Γ'.length) := by
        rintro ⟨_, he⟩; exact absurd (nameAtLevel_inj he) (by omega)
      simp only [resolveVar, dif_neg hne,
        resolveVar_none_ge Γ' m (by simpa using Nat.le_of_lt hlt), Option.map_none]

/-- Reading the embedded register file at any name agrees with looking up the
    variable `resolveVar` returns for it (`0` when there is none).  The
    name→`Var` half of `embed_lookup`: `embed_lookup` reads at a *given*
    variable's name; this reads at an *arbitrary* name and recovers the variable. -/
theorem embed_resolveVar {Γ : Ctxt jasminDialect} (name : String)
    (V : Ctxt.Valuation Γ) : embed V name = valOf (resolveVar Γ name) V := by
  induction Γ with
  | nil => cases V; rfl
  | cons t Γ' ih =>
      cases V with
      | cons hv V' =>
        rw [embed_cons]
        by_cases h : t = .reg 32 ∧ name = nameAtLevel Γ'.length
        · obtain ⟨ht, hn⟩ := h
          subst ht; subst hn
          rw [Function.update_self, resolveVar, dif_pos ⟨rfl, rfl⟩]
          rfl
        · rw [resolveVar, dif_neg h]
          by_cases hn : name = nameAtLevel Γ'.length
          · have htne : t ≠ .reg 32 := fun ht => h ⟨ht, hn⟩
            subst hn
            rw [Function.update_self, regVal_ne htne,
              resolveVar_none_ge Γ' Γ'.length (le_refl _)]
            rfl
          · rw [Function.update_of_ne hn, ih]
            cases resolveVar Γ' name with
            | none => rfl
            | some v => rfl

/-! ## 3. Packable-op decoding -/

/-- Map a `JasminBinOp` to the SLP lane op it packs to.  Only the three
    two-operand ALU ops whose scalar and lane semantics coincide are packable:
    `add` / `xor` / `or`.  The register-count shifts are excluded — the SLP
    `LaneOp` shifts carry an immediate count, whereas `regArith .shl` / `.shr`
    read the count from a register operand, so a shift map would not preserve
    denotation. -/
def laneOpOf : JasminBinOp → Option LaneOp
  | .add => some .add
  | .xor => some .xor
  | .or  => some .orr
  | _    => none

/-- `laneOpOf` is denotation-faithful: a mapped lane op applies exactly as the
    lane operation of the source `JasminBinOp` at width 32. -/
theorem laneOpOf_faithful {bop : JasminBinOp} {lop : LaneOp}
    (h : laneOpOf bop = some lop) (a b : BitVec 32) : lop.apply a b = bop.applyLane a b := by
  cases bop with
  | add => simp only [laneOpOf, Option.some.injEq] at h; subst h; rfl
  | xor => simp only [laneOpOf, Option.some.injEq] at h; subst h; rfl
  | or  => simp only [laneOpOf, Option.some.injEq] at h; subst h; rfl
  | sub => simp [laneOpOf] at h
  | mul => simp [laneOpOf] at h
  | and => simp [laneOpOf] at h
  | shl => simp [laneOpOf] at h
  | shr => simp [laneOpOf] at h
  | andn => simp [laneOpOf] at h

/-- Decode one expression into a scalar statement with destination name `dst`.
    Returns `some` only for a width-32 binary `regArith` whose op is packable;
    `none` on every other node (partial by construction). -/
def exprToSStmt {Γ : Ctxt jasminDialect} {t : JasminTy} (dst : String)
    (e : Expr jasminDialect Γ t) : Option SStmt :=
  match e with
  | ⟨.regArith bop w, _, args⟩ =>
      if w = 32 then
        (laneOpOf bop).map fun lop =>
          { dst := dst, op := lop, s1 := varNm args.head, s2 := varNm args.tail.head }
      else none
  | _ => none

/-- **The one-statement step.**  When `exprToSStmt` decodes an expression bound
    at level `Γ.length`, executing that statement on the embedded register file
    reproduces the embedding of the valuation extended by the expression's
    denotation.  This is the per-binder correspondence the forward simulation
    threads. -/
theorem exprToSStmt_step {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (s : SStmt)
    (h : exprToSStmt (nameAtLevel Γ.length) e = some s) (V : Ctxt.Valuation Γ) :
    s.exec (embed V) = embed (HVector.cons (e.denote V) V) := by
  rcases e with ⟨op, hop, args⟩
  cases op with
  | regArith bop w =>
      by_cases hw : w = 32
      · subst hw
        subst hop
        cases args with
        | cons a rest => cases rest with
          | cons b rest2 => cases rest2 with
            | nil =>
              rcases hlan : laneOpOf bop with _ | lop
              · simp [exprToSStmt, hlan] at h
              · simp only [exprToSStmt, hlan, if_true, Option.map_some, Option.some.injEq,
                  HVector.head, HVector.tail] at h
                subst h
                funext n
                rw [embed_cons]
                simp only [SStmt.exec]
                by_cases hn : n = nameAtLevel Γ.length
                · subst hn
                  rw [Function.update_self, if_pos rfl,
                      embed_lookup a, embed_lookup b, laneOpOf_faithful hlan]
                  cases bop <;> first | rfl | simp [laneOpOf] at hlan
                · rw [Function.update_of_ne hn, if_neg hn]
      · simp [exprToSStmt, hw] at h
  | stackLoad w n => simp [exprToSStmt] at h
  | stackStore w n => simp [exprToSStmt] at h
  | castW w w' => simp [exprToSStmt] at h
  | extCall nm a r => simp [exprToSStmt] at h
  | regConst w n => simp [exprToSStmt] at h
  | vpackZMM b => simp [exprToSStmt] at h
  | vpackZMMd b => simp [exprToSStmt] at h
  | vprordZMM n => simp [exprToSStmt] at h
  | vpslldq n => simp [exprToSStmt] at h
  | vpsrldq n => simp [exprToSStmt] at h
  | vsimd o => simp [exprToSStmt] at h
  | vymm o => simp [exprToSStmt] at h
  | mulhi w => simp [exprToSStmt] at h
  | addCarryLo w => simp [exprToSStmt] at h
  | addCarryHi w => simp [exprToSStmt] at h
  | rorImm w n => simp [exprToSStmt] at h
  | shrImm w n => simp [exprToSStmt] at h
  | sarImm w n => simp [exprToSStmt] at h
  | shlImm w n => simp [exprToSStmt] at h
  | select w => simp [exprToSStmt] at h
  | callN nm a r => simp [exprToSStmt] at h
  | cmp c w => simp [exprToSStmt] at h
  | cmpImm c w n => simp [exprToSStmt] at h
  | stackZero w n => simp [exprToSStmt] at h

/-! ## 4. Straight-line extraction and the denotation agreement -/

/-- Extract a straight-line scalar block from a `Com` let-chain.  Returns `none`
    on any non-packable node.  Each let-bound expression at context `Γ` names its
    destination by the level `Γ.length` of the binding. -/
def comToSStmt : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Option (List SStmt)
  | _, _, .ret _ => some []
  | Γ, _, .var e body =>
      match exprToSStmt (nameAtLevel Γ.length) e with
      | some s => (comToSStmt body).map (s :: ·)
      | none => none

/-- The final context a `Com` let-chain leaves in scope (the input context
    extended by every let binding). -/
def comOutCtx : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Ctxt jasminDialect
  | Γ, _, .ret _ => Γ
  | _, _, .var _ body => comOutCtx body

/-- Denote a `Com` let-chain into its final context valuation (every binding's
    value in scope), rather than only the returned value. -/
def comEval : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → Ctxt.Valuation Γ → Ctxt.Valuation (comOutCtx c)
  | _, _, .ret _, V => V
  | _, _, .var e body, V => comEval body (HVector.cons (e.denote V) V)

/-- The return variable of a `Com`, resolved in its final context. -/
def comRetVar : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → Ctxt.Var (comOutCtx c) t
  | _, _, .ret v => v
  | _, _, .var _ body => comRetVar body

/-- `Com.denote` reads the return variable out of the final valuation. -/
theorem com_denote_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    c.denote V = (comRetVar c).lookup (comEval c V) := by
  induction c with
  | ret v => rfl
  | var e body ih =>
      simp only [Com.denote, comEval, comRetVar, Ctxt.Valuation.extend]
      exact ih (HVector.cons (e.denote V) V)

/-- **Forward simulation.**  When `comToSStmt c = some g`, running the extracted
    scalar block from the embedded input valuation reproduces the embedding of
    the `Com`'s final valuation.  Threads `exprToSStmt_step` through the chain. -/
theorem comToSStmt_runScalar {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (g : List SStmt)
    (h : comToSStmt c = some g) (V : Ctxt.Valuation Γ) :
    runScalar g (embed V) = embed (comEval c V) := by
  induction c generalizing g with
  | ret v =>
      simp only [comToSStmt, Option.some.injEq] at h
      subst h; rfl
  | var e body ih =>
      simp only [comToSStmt] at h
      split at h
      · next s heq =>
          rcases hr : comToSStmt body with _ | rest
          · simp [hr] at h
          · simp only [hr, Option.map_some, Option.some.injEq] at h
            subst h
            simp only [runScalar]
            rw [exprToSStmt_step e s heq V, ih rest hr (HVector.cons (e.denote V) V)]
            rfl
      · next heq => simp at h

/-- **Denotation agreement.**  When `comToSStmt c = some g`, the extracted block,
    run from the embedded inputs and read at the return variable's level name,
    equals `Com.denote c V`.  Composes the forward simulation with `embed_lookup`
    and `com_denote_eq`. -/
theorem comToSStmt_denote {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 32)) (g : List SStmt)
    (h : comToSStmt c = some g) (V : Ctxt.Valuation Γ) :
    runScalar g (embed V) (varNm (comRetVar c)) = c.denote V := by
  rw [comToSStmt_runScalar c g h V, embed_lookup (comRetVar c) (comEval c V),
      ← com_denote_eq c V]

/-! ## 5. The packed `reg 128` synthesis link

`comToSStmt` (§4) is the analysis direction; `comToSStmt_denote` ties the
extracted block to `Com.denote`.  This section supplies the synthesis direction:
pack a fired `SLPGroup`'s per-lane inputs into two packed `reg 128` registers,
apply the unified `JasminOp.vsimd (.packed bop 32)` op (the `Com` `packAvx2Com
bop`), and read a lane back out.  `packedCom_lane_eq` proves that lane read equals
`SLPVectorize`'s abstract `packedResult`; `packedCom_denote` composes it with
`slpVectorize_block_denote` and `comToSStmt_denote` to reproduce `Com.denote`. -/

/-- Gather a fired group's `k`-th source lanes from the scalar register file into
    a packed `reg 128`: lane `j` carries member `j`'s source (`useS1 = true` reads
    `.s1`, `false` reads `.s2`).  The gather feeding `packAvx2Com`. -/
def groupPack (G : SLPGroup) (r : SRegs) (useS1 : Bool) : BitVec 128 :=
  packLanes32 (packSrc G.members r useS1 4)

/-- **The packed-register denotation link.**  Reading lane `j` of the unified
    `vsimd (.packed bop 32)` op (`packAvx2Com bop`), applied to the two gathered
    packed registers of a fired group, equals `SLPVectorize`'s abstract
    `packedResult` at lane `j`.  Composes `packAvx2Com_denote`, the packed↔lane
    round-trip `v128Pack32_lane`, the gather round-trip `packLanes32_lane`, and the
    op-faithfulness `laneOpOf_faithful` (`bop`'s scalar op is the group's
    `LaneOp`). -/
theorem packedCom_lane_eq (bop : JasminBinOp) (G : SLPGroup)
    (hf : laneOpOf bop = some G.op) (r : SRegs) (j : Fin 4) :
    BitVec.extractLsb' (32 * j.val) 32
        ((packAvx2Com bop).denote
          (.cons (groupPack G r true) (.cons (groupPack G r false) .nil)))
      = packedResult G.op G.members r 4 j := by
  simp only [groupPack]
  rw [packAvx2Com_denote, v128Pack32_lane, packLanes32_lane, packLanes32_lane]
  simp only [packedResult, vmap₂]
  exact (laneOpOf_faithful hf _ _).symm

/-- **Reg-128 packed op reproduces the scalar block.**  Reading lane `j` of the
    packed op over a fired group's gathered registers equals the value the scalar
    block leaves at member `j`'s destination.  `packedCom_lane_eq` composed with
    `slpVectorize_block_denote`. -/
theorem packedCom_block_denote (bop : JasminBinOp) (g : List SStmt) (G : SLPGroup)
    (hf : laneOpOf bop = some G.op) (hd : slpDetect g = some G) (r : SRegs)
    (j : Fin 4) (sj : SStmt) (hj : G.members[j.val]? = some sj) :
    BitVec.extractLsb' (32 * j.val) 32
        ((packAvx2Com bop).denote
          (.cons (groupPack G r true) (.cons (groupPack G r false) .nil)))
      = runScalar G.members r sj.dst := by
  rw [packedCom_lane_eq bop G hf r j, slpVectorize_block_denote g G hd r 4 j sj hj]

/-- **The packed op reproduces `Com.denote`.**  When a `Com`'s extracted scalar
    block `g` detects a group `G` whose lane `j` writes the return variable's
    destination, reading lane `j` of the packed `vsimd` op over the group's
    gathered registers (from the embedded input valuation) equals `Com.denote c`.
    The three-part composition: `packedCom_block_denote` (reg-128 lane = scalar
    block value at the member destination), `slpDetect_members` (the fired group
    is the whole block), and `comToSStmt_denote` (the block, read at the return
    name, is `Com.denote`). -/
theorem packedCom_denote {Γ : Ctxt jasminDialect} (bop : JasminBinOp)
    (c : Com jasminDialect Γ (.reg 32)) (g : List SStmt) (G : SLPGroup)
    (hc : comToSStmt c = some g) (hd : slpDetect g = some G)
    (hf : laneOpOf bop = some G.op)
    (j : Fin 4) (sj : SStmt) (hj : G.members[j.val]? = some sj)
    (hret : sj.dst = varNm (comRetVar c)) (V : Ctxt.Valuation Γ) :
    BitVec.extractLsb' (32 * j.val) 32
        ((packAvx2Com bop).denote
          (.cons (groupPack G (embed V) true)
            (.cons (groupPack G (embed V) false) .nil)))
      = c.denote V := by
  rw [packedCom_block_denote bop g G hf hd (embed V) j sj hj,
      slpDetect_members g G hd, hret, comToSStmt_denote c g hc V]

/-! ## 5b. The reg-128 gather as a `Com` sub-chain

`packedCom_denote` reads the packed op over the two abstract `groupPack` registers.
This section builds those registers as `Com` sub-chains over `Γ`: `srcE` widens one
`reg 32` source (or `0`) to `reg 128`, and `gatherGo` folds the shift-and-or of
`packLanes32` into a straight-line `Com`, so `gatherCom` denotes exactly the
`packLanes32` of the four lane sources. -/

/-- Widen a `reg 32` source variable (or `0` when absent) to a `reg 128` binding:
    `castW 32 128` of the variable, or the constant `0`. -/
def srcE {Γ' : Ctxt jasminDialect} (o : Option (Ctxt.Var Γ' (.reg 32))) :
    Expr jasminDialect Γ' (.reg 128) :=
  match o with
  | some v => { op := .castW 32 128, retTy_eq := rfl, args := .cons v .nil }
  | none => { op := .regConst 128 0, retTy_eq := rfl, args := .nil }

/-- `srcE` denotes the widened source value (`0` when absent). -/
theorem srcE_denote {Γ' : Ctxt jasminDialect} (o : Option (Ctxt.Var Γ' (.reg 32)))
    (V' : Ctxt.Valuation Γ') : (srcE o).denote V' = (valOf o V').setWidth 128 := by
  cases o with
  | none => rfl
  | some v => rfl

/-- Immediate left-shift of a `reg 128` binding by `n`. -/
def shlE {Γ' : Ctxt jasminDialect} (n : Nat) (v : Ctxt.Var Γ' (.reg 128)) :
    Expr jasminDialect Γ' (.reg 128) :=
  { op := .shlImm 128 n, retTy_eq := rfl, args := .cons v .nil }

/-- `shlE` denotes the immediate left-shift. -/
theorem shlE_denote {Γ' : Ctxt jasminDialect} (n : Nat) (v : Ctxt.Var Γ' (.reg 128))
    (V' : Ctxt.Valuation Γ') :
    (shlE n v).denote V' = (show BitVec 128 from v.lookup V') <<< shiftMask 128 n := rfl

/-- Bitwise-or of two `reg 128` bindings. -/
def orE {Γ' : Ctxt jasminDialect} (a b : Ctxt.Var Γ' (.reg 128)) :
    Expr jasminDialect Γ' (.reg 128) :=
  { op := .regArith .or 128, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- `orE` denotes the bitwise or. -/
theorem orE_denote {Γ' : Ctxt jasminDialect} (a b : Ctxt.Var Γ' (.reg 128))
    (V' : Ctxt.Valuation Γ') :
    (orE a b).denote V' = (show BitVec 128 from a.lookup V') ||| b.lookup V' := rfl

/-- Weaken a variable past the three `reg 128` bindings one gather step adds. -/
def wk3 {Γ' : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ' t) :
    Ctxt.Var (JasminTy.reg 128 :: JasminTy.reg 128 :: JasminTy.reg 128 :: Γ') t :=
  .there (.there (.there v))

/-- Fold the remaining `(shift, source)` lanes into a running `reg 128`
    accumulator: each lane widens its source, shifts it, and ors it onto the
    accumulator.  `hom` weakens `Γ`'s source variables into the current context. -/
def gatherGo {Γ : Ctxt jasminDialect} :
    {Γ' : Ctxt jasminDialect} → Ctxt.Var Γ' (.reg 128) → Ctxt.Hom Γ Γ' →
    List (Nat × Option (Ctxt.Var Γ (.reg 32))) → Com jasminDialect Γ' (.reg 128)
  | _, acc, _, [] => .ret acc
  | _, acc, hom, (sh, o) :: rest =>
      .var (srcE (o.map hom))
        (.var (shlE sh Ctxt.Var.here)
          (.var (orE (Ctxt.Var.there (Ctxt.Var.there acc)) Ctxt.Var.here)
            (gatherGo Ctxt.Var.here (Ctxt.Hom.comp wk3 hom) rest)))

/-- `gatherGo` denotes the running `packLanes32`-style fold: each lane ors its
    shifted, widened source onto the accumulator. -/
theorem gatherGo_denote {Γ : Ctxt jasminDialect}
    (lanes : List (Nat × Option (Ctxt.Var Γ (.reg 32)))) :
    ∀ {Γ' : Ctxt jasminDialect} (acc : Ctxt.Var Γ' (.reg 128)) (hom : Ctxt.Hom Γ Γ')
      (V' : Ctxt.Valuation Γ'),
      (gatherGo acc hom lanes).denote V'
        = List.foldl
            (fun (a : BitVec 128) p =>
              a ||| ((valOf (p.2.map hom) V').setWidth 128 <<< shiftMask 128 p.1))
            (acc.lookup V') lanes := by
  induction lanes with
  | nil => intro Γ' acc hom V'; rfl
  | cons hd tl ih =>
      intro Γ' acc hom V'
      obtain ⟨sh, o⟩ := hd
      simp only [gatherGo, Com.denote]
      rw [ih Ctxt.Var.here (Ctxt.Hom.comp wk3 hom) _, List.foldl_cons]
      congr 1
      · funext a p
        obtain ⟨psh, po⟩ := p
        cases po with
        | none => rfl
        | some v => rfl
      · simp only [srcE_denote, shlE_denote, orE_denote, Ctxt.Valuation.extend]
        rfl

/-- Gather four `reg 32` lane sources into one packed `reg 128` register as a
    straight-line `Com`: widen lane `0`, then fold the shifted, widened lanes
    `1`–`3` onto it.  Its denotation is exactly `packLanes32` of the lane values. -/
def gatherCom {Γ : Ctxt jasminDialect} (src : Fin 4 → Option (Ctxt.Var Γ (.reg 32))) :
    Com jasminDialect Γ (.reg 128) :=
  .var (srcE (src 0))
    (gatherGo Ctxt.Var.here (Ctxt.Hom.weakenOne Γ (.reg 128))
      [(32, src 1), (64, src 2), (96, src 3)])

/-- `gatherCom` denotes the `packLanes32` gather of its four lane sources. -/
theorem gatherCom_denote {Γ : Ctxt jasminDialect}
    (src : Fin 4 → Option (Ctxt.Var Γ (.reg 32))) (V : Ctxt.Valuation Γ) :
    (gatherCom src).denote V = packLanes32 (fun k => valOf (src k) V) := by
  rw [gatherCom, Com.denote, gatherGo_denote]
  simp only [List.foldl_cons, List.foldl_nil, srcE_denote, packLanes32]
  rcases src 0 with _ | v0 <;> rcases src 1 with _ | v1 <;>
    rcases src 2 with _ | v2 <;> rcases src 3 with _ | v3 <;> rfl

/-! ## 5c. The lane sources and the assembled reg-128 rebuild -/

/-- The `s1` (first-operand) sources of a fired group, resolved to `Γ` variables;
    `none` past the group's members. -/
def s1Src (G : SLPGroup) (Γ : Ctxt jasminDialect) :
    Fin 4 → Option (Ctxt.Var Γ (.reg 32)) :=
  fun k => match G.members[k.val]? with
    | some s => resolveVar Γ s.s1
    | none => none

/-- The `s2` (second-operand) sources of a fired group, resolved to `Γ` variables. -/
def s2Src (G : SLPGroup) (Γ : Ctxt jasminDialect) :
    Fin 4 → Option (Ctxt.Var Γ (.reg 32)) :=
  fun k => match G.members[k.val]? with
    | some s => resolveVar Γ s.s2
    | none => none

/-- The resolved `s1` source value at lane `k` equals `packSrc`'s `s1` gather. -/
theorem valOf_s1Src (G : SLPGroup) (Γ : Ctxt jasminDialect) (V : Ctxt.Valuation Γ)
    (k : Fin 4) : valOf (s1Src G Γ k) V = packSrc G.members (embed V) true 4 k := by
  simp only [s1Src, packSrc]
  cases G.members[k.val]? with
  | none => rfl
  | some s => exact (embed_resolveVar s.s1 V).symm

/-- The resolved `s2` source value at lane `k` equals `packSrc`'s `s2` gather. -/
theorem valOf_s2Src (G : SLPGroup) (Γ : Ctxt jasminDialect) (V : Ctxt.Valuation Γ)
    (k : Fin 4) : valOf (s2Src G Γ k) V = packSrc G.members (embed V) false 4 k := by
  simp only [s2Src, packSrc]
  cases G.members[k.val]? with
  | none => rfl
  | some s => exact (embed_resolveVar s.s2 V).symm

/-- Gathering the resolved `s1` sources reproduces the group's `true` gather. -/
theorem gather_s1 (G : SLPGroup) (Γ : Ctxt jasminDialect) (V : Ctxt.Valuation Γ) :
    (gatherCom (s1Src G Γ)).denote V = groupPack G (embed V) true := by
  rw [gatherCom_denote, groupPack]
  congr 1
  funext k
  exact valOf_s1Src G Γ V k

/-- Gathering the resolved `s2` sources reproduces the group's `false` gather. -/
theorem gather_s2 (G : SLPGroup) (Γ : Ctxt jasminDialect) (V : Ctxt.Valuation Γ) :
    (gatherCom (s2Src G Γ)).denote V = groupPack G (embed V) false := by
  rw [gatherCom_denote, groupPack]
  congr 1
  funext k
  exact valOf_s2Src G Γ V k

/-- Packed `vsimd` op over two `reg 128` bindings. -/
def vsimdE {Γ' : Ctxt jasminDialect} (bop : JasminBinOp)
    (a b : Ctxt.Var Γ' (.reg 128)) : Expr jasminDialect Γ' (.reg 128) :=
  { op := .vsimd (.packed bop 32), retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- `vsimdE` denotes the packed-lane op. -/
theorem vsimdE_denote {Γ' : Ctxt jasminDialect} (bop : JasminBinOp)
    (a b : Ctxt.Var Γ' (.reg 128)) (V' : Ctxt.Valuation Γ') :
    (vsimdE bop a b).denote V'
      = SimdOp.denote (.packed bop 32) (a.lookup V') (b.lookup V') := rfl

/-- Immediate right-shift of a `reg 128` binding. -/
def shrE {Γ' : Ctxt jasminDialect} (n : Nat) (v : Ctxt.Var Γ' (.reg 128)) :
    Expr jasminDialect Γ' (.reg 128) :=
  { op := .shrImm 128 n, retTy_eq := rfl, args := .cons v .nil }

/-- `shrE` denotes the immediate right-shift. -/
theorem shrE_denote {Γ' : Ctxt jasminDialect} (n : Nat) (v : Ctxt.Var Γ' (.reg 128))
    (V' : Ctxt.Valuation Γ') :
    (shrE n v).denote V' = (show BitVec 128 from v.lookup V') >>> shiftMask 128 n := rfl

/-- Truncate a `reg 128` binding to `reg 32`. -/
def castE {Γ' : Ctxt jasminDialect} (v : Ctxt.Var Γ' (.reg 128)) :
    Expr jasminDialect Γ' (.reg 32) :=
  { op := .castW 128 32, retTy_eq := rfl, args := .cons v .nil }

/-- `castE` denotes the truncation. -/
theorem castE_denote {Γ' : Ctxt jasminDialect} (v : Ctxt.Var Γ' (.reg 128))
    (V' : Ctxt.Valuation Γ') :
    (castE v).denote V' = (show BitVec 128 from v.lookup V').setWidth 32 := rfl

/-- Assemble the reg-128 rebuild: gather the two operand registers, apply the
    packed `vsimd` op, right-shift to lane `j`, and truncate to `reg 32`. -/
def rebuildLaneCom {Γ : Ctxt jasminDialect} (bop : JasminBinOp)
    (aSrc bSrc : Fin 4 → Option (Ctxt.Var Γ (.reg 32))) (j : Fin 4) :
    Com jasminDialect Γ (.reg 32) :=
  let cA := gatherCom aSrc
  let cB := (gatherCom bSrc).rename cA.outContextHom
  let LB := cA.toLets.addComToEnd cB
  let LR := LB.var (vsimdE bop (cB.outContextHom cA.returnVar) cB.returnVar)
  let LS := LR.var (shrE (32 * j.val) Ctxt.Var.here)
  let LT := LS.var (castE Ctxt.Var.here)
  Zipper.toCom ⟨LT, .ret Ctxt.Var.here⟩

/-- The rebuild denotes lane `j` of the packed op over the two gathered registers. -/
theorem rebuildLaneCom_denote {Γ : Ctxt jasminDialect} (bop : JasminBinOp)
    (aSrc bSrc : Fin 4 → Option (Ctxt.Var Γ (.reg 32))) (j : Fin 4)
    (V : Ctxt.Valuation Γ) :
    (rebuildLaneCom bop aSrc bSrc j).denote V
      = BitVec.extractLsb' (32 * j.val) 32
          (SimdOp.denote (.packed bop 32)
            ((gatherCom aSrc).denote V) ((gatherCom bSrc).denote V)) := by
  have hvB : ((gatherCom bSrc).rename (gatherCom aSrc).outContextHom).returnVar.lookup
      (((gatherCom bSrc).rename (gatherCom aSrc).outContextHom).denoteLets
        ((gatherCom aSrc).denoteLets V)) = (gatherCom bSrc).denote V := by
    rw [Com.denoteLets_returnVar, Com.denote_rename, Com.comap_outContextHom_denoteLets]
  have hvA : (((gatherCom bSrc).rename (gatherCom aSrc).outContextHom).outContextHom
      (gatherCom aSrc).returnVar).lookup
      (((gatherCom bSrc).rename (gatherCom aSrc).outContextHom).denoteLets
        ((gatherCom aSrc).denoteLets V)) = (gatherCom aSrc).denote V := by
    rw [Com.lookup_outContextHom_denoteLets, Com.denoteLets_returnVar]
  simp only [rebuildLaneCom, Zipper.denote_toCom, Zipper.denote, Com.denote,
    Lets.denote, Lets.denote_addComToEnd, Com.denote_toLets, Ctxt.Valuation.extend,
    castE_denote, shrE_denote, vsimdE_denote, hvA, hvB]
  rw [shiftMask_of_lt (by omega)]
  rfl

/-! ## 6. The `Com → Com` vectorizing pass

`packedCom_denote` certifies that the packed `vsimd` op computes exactly
`Com.denote c` at the return lane.  `rebuildLaneCom` reifies that packed op as a
typed `Com jasminDialect Γ (.reg 32)`, and `slpVectorizeCom` fires it when the
extracted block's group packs to a `JasminBinOp` and writes the return
destination at one lane.  `slpVectorizeCom_denote` proves the pass is
denotation-preserving; `slpVectorizeComGoal_holds` discharges the reification
obligation `SlpVectorizeComGoal`. -/

/-- The `JasminBinOp` packing a `LaneOp`: the inverse of `laneOpOf` on the three
    binary ALU ops; `none` on the shifts (which `laneOpOf` also excludes). -/
def vbopOf : LaneOp → Option JasminBinOp
  | .add => some .add
  | .xor => some .xor
  | .orr => some .or
  | .shl _ => none
  | .shr _ => none

/-- `vbopOf` inverts `laneOpOf`: a packed `bop` maps back to the lane op. -/
theorem laneOpOf_of_vbopOf {lop : LaneOp} {bop : JasminBinOp}
    (h : vbopOf lop = some bop) : laneOpOf bop = some lop := by
  cases lop with
  | add => simp only [vbopOf, Option.some.injEq] at h; subst h; rfl
  | xor => simp only [vbopOf, Option.some.injEq] at h; subst h; rfl
  | orr => simp only [vbopOf, Option.some.injEq] at h; subst h; rfl
  | shl _ => simp [vbopOf] at h
  | shr _ => simp [vbopOf] at h

/-- Whether lane `k`'s member destination is `nm`. -/
def laneDstEq (G : SLPGroup) (nm : String) (k : Fin 4) : Bool :=
  match G.members[k.val]? with
  | some s => s.dst = nm
  | none => false

/-- The first lane whose member destination is `nm`, if any. -/
def findRetLane (G : SLPGroup) (nm : String) : Option (Fin 4) :=
  if laneDstEq G nm 0 then some 0
  else if laneDstEq G nm 1 then some 1
  else if laneDstEq G nm 2 then some 2
  else if laneDstEq G nm 3 then some 3
  else none

/-- A found return lane has `laneDstEq`. -/
theorem findRetLane_laneDstEq {G : SLPGroup} {nm : String} {j : Fin 4}
    (h : findRetLane G nm = some j) : laneDstEq G nm j = true := by
  unfold findRetLane at h
  split_ifs at h <;> simp_all

/-- `laneDstEq` witnesses the member at that lane and its destination. -/
theorem laneDstEq_spec {G : SLPGroup} {nm : String} {j : Fin 4}
    (h : laneDstEq G nm j = true) : ∃ sj, G.members[j.val]? = some sj ∧ sj.dst = nm := by
  unfold laneDstEq at h
  cases hm : G.members[j.val]? with
  | none => rw [hm] at h; simp at h
  | some s => rw [hm] at h; exact ⟨s, rfl, by simpa using h⟩

/-- **The reg-128 rebuild reproduces `Com.denote c`.**  When `c`'s extracted block
    fires group `G` whose lane `j` writes the return destination and `bop` packs
    `G.op`, the assembled rebuild denotes exactly `Com.denote c`.  Composes
    `rebuildLaneCom_denote` and `gather_s1`/`gather_s2` with `packedCom_denote`. -/
theorem rebuild_eq_com_denote {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 32)) (bop : JasminBinOp) (g : List SStmt)
    (G : SLPGroup) (hc : comToSStmt c = some g) (hd : slpDetect g = some G)
    (hf : laneOpOf bop = some G.op) (j : Fin 4) (sj : SStmt)
    (hj : G.members[j.val]? = some sj) (hret : sj.dst = varNm (comRetVar c))
    (V : Ctxt.Valuation Γ) :
    (rebuildLaneCom bop (s1Src G Γ) (s2Src G Γ) j).denote V = c.denote V := by
  rw [rebuildLaneCom_denote, gather_s1, gather_s2,
    ← packedCom_denote bop c g G hc hd hf j sj hj hret V]
  rfl

/-- The vectorizing `Com → Com` pass.  When the extracted straight-line block
    fires an SLP group whose shared op packs to a `JasminBinOp` and whose lanes
    include the return destination, the pass rebuilds the packed reg-128 `vsimd`
    op with the gather/scatter chain; otherwise it returns its input. -/
def slpVectorizeCom {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 32)) : Com jasminDialect Γ (.reg 32) :=
  match comToSStmt c with
  | none => c
  | some g =>
    match slpDetect g with
    | none => c
    | some G =>
      match vbopOf G.op with
      | none => c
      | some bop =>
        match findRetLane G (varNm (comRetVar c)) with
        | none => c
        | some j => rebuildLaneCom bop (s1Src G Γ) (s2Src G Γ) j

/-- `slpVectorizeCom` preserves denotation: the identity branches trivially, the
    rebuild branch by `rebuild_eq_com_denote`. -/
theorem slpVectorizeCom_denote {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 32)) (V : Ctxt.Valuation Γ) :
    (slpVectorizeCom c).denote V = c.denote V := by
  unfold slpVectorizeCom
  split
  · rfl
  · next g hc =>
    split
    · rfl
    · next G hd =>
      split
      · rfl
      · next bop hb =>
        split
        · rfl
        · next j hjf =>
          obtain ⟨sj, hmem, hret⟩ := laneDstEq_spec (findRetLane_laneDstEq hjf)
          exact rebuild_eq_com_denote c bop g G hc hd (laneOpOf_of_vbopOf hb) j sj hmem hret V

/-- **The reification obligation, discharged.**  For a `Com` whose extracted block
    fires a group with op faithful to `bop`, `rebuildLaneCom` is a typed
    `Com jasminDialect Γ (.reg 32)` whose denotation is the packed reg-128 lane
    read: the reg-128 gather (name→`Ctxt.Var Γ` resolution and the cast/shift/or
    chain denoting `packLanes32`), the `vsimd` application, and the lane scatter. -/
def SlpVectorizeComGoal : Prop :=
  ∀ {Γ : Ctxt jasminDialect} (c : Com jasminDialect Γ (.reg 32))
    (bop : JasminBinOp) (g : List SStmt) (G : SLPGroup) (j : Fin 4),
    comToSStmt c = some g → slpDetect g = some G → laneOpOf bop = some G.op →
    ∃ c' : Com jasminDialect Γ (.reg 32),
      ∀ V : Ctxt.Valuation Γ,
        c'.denote V
          = BitVec.extractLsb' (32 * j.val) 32
              ((packAvx2Com bop).denote
                (.cons (groupPack G (embed V) true)
                  (.cons (groupPack G (embed V) false) .nil)))

/-- `SlpVectorizeComGoal` holds: `rebuildLaneCom` is the witness. -/
theorem slpVectorizeComGoal_holds : SlpVectorizeComGoal := by
  intro Γ c bop g G j _ _ _
  refine ⟨rebuildLaneCom bop (s1Src G Γ) (s2Src G Γ) j, fun V => ?_⟩
  rw [rebuildLaneCom_denote, gather_s1, gather_s2, packAvx2Com_denote]
  rfl

end CatCrypt.Crypto.Optimizer.ComSStmtBridge
