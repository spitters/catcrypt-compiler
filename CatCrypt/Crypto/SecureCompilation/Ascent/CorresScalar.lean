/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.ExprLeaf
import Lean

/-!
# The scalar-`Corres` scaffold over the `srcClean` word algebra

The shared machinery for lifting a straight-line `RScalarSetExpr` kernel to a
`semScalar`-level `Ascent.Corres` result over the identity `BitVec 64` word
algebra (`SRwordBV`), and the weld tying such a result to the front-compiled
`Com catCryptDialect` denotation.

* `corres_setExprWord` generalizes `Ascent.ExprLeaf.corres_setExprBitwise` from the
  four-op bitwise fragment `IsWordClean` to the full `srcClean` word algebra
  (`SSub` / `SAdd` / `SMul` / `SMulHiU` / the shifts added), keeping the identity
  `BitVec 64` abstraction. A bit-serial `GF(2^k)` multiply mixes `SSub` (the
  `0 − bit` mask) with the bitwise ops, so neither the arithmetic (`ZMod 2^64`)
  nor the bitwise leaf alone covers it; the identity abstraction of the whole
  `srcClean` fragment does.
* `corres_seqAll` sequences a per-statement family of `Corres` leaves through the
  `RSeq` spine `seqAll` into one `Corres` over the left-folded abstract step.
* `corres_solve_scalar` walks the `RSeq` / `RScalarSetExpr` tree, applying
  `corres_setExprWord` at each leaf and discharging the `srcClean` side condition,
  synthesizing the folded abstract step. The scalar analogue of
  `Ascent.CorresSolver.corres_solve` (over `CorresJ` / `JInstr`).
* `corresScalar_frontDenote` welds a `Corres SRwordBV` result to the front
  homomorphism `translateDialectControl_denote_ctl`: from entry `ConsistentS`
  consistency and the state relation at entry, the front-compiled kernel's
  `Com.denote` at the tracked output slot reads out the abstract value the
  `Corres` result computes. This is the seam UOV / MAYO / NTRU / SNOVA / HAWK /
  Frodo `KernelEmitDenote` leaves left open; it composes
  `translateDialectControl_denote_ctl` with `ConsistentS.lookup_eq`, the same
  pieces `VIR.CompilerCorrectnessExtracted.semScalarToJasminCom_denote_eq` uses.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl

/-! ## 1. The `srcClean` word value leaf -/

/-- The `srcClean` word value leaf. From an env `SRwordBV`-related to abstract
    `a : String → BitVec 64`, the `semScalar` `RScalarSetExpr x e` arm makes
    progress and sets `x` to `SExpr.evalBV a e`, leaving every other source name
    untouched. Progress is `semLowerSExpr_ok'`; the value transfer is
    `evalBV_congr_on` (reader agreement), definitional for the word fragment. -/
theorem corres_setExprWord (x : String) (e : SExpr) (he : srcClean e) :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = x then SExpr.evalBV a e else a s)
      (.RScalarSetExpr x e) := by
  intro env a hSR _
  set rs : RustState := ⟨fun _ => none, fun y => (a y).toNat⟩ with hrs
  have hEB : EnvBoundOn rs env (fun _ => True) := by
    intro y _ hnt
    have hround : BitVec.ofNat 64 (a y).toNat = a y := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (a y).isLt
    show env y = some ⟨.sword 64, BitVec.ofNat 64 ((a y).toNat)⟩
    rw [hround]; exact hSR y hnt
  obtain ⟨env2, nm, cnt', hsem, _, hotb, _, _⟩ :=
    semLowerSExpr_ok' rs (fun _ => True) e env 0 hEB (varsBoundIn_true e) he
  have hval : SExpr.evalBV (envReader env) e = SExpr.evalBV a e := by
    apply evalBV_congr_on (fun _ => True) (envReader env) a e _ (varsBoundIn_true e) he
    intro s _ hns
    simp only [envReader, hSR s hns]
  refine ⟨env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e), ?_, ?_⟩
  · simp only [semScalar, hsem]
  · intro y hnt
    by_cases hyx : y = x
    · show (env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e)) y
        = some ⟨.sword 64, if y = x then SExpr.evalBV a e else a y⟩
      rw [if_pos hyx]
      simp only [SEnvScalar.upd, if_pos hyx]
      rw [hval]
    · show (env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e)) y
        = some ⟨.sword 64, if y = x then SExpr.evalBV a e else a y⟩
      rw [if_neg hyx]
      simp only [SEnvScalar.upd, if_neg hyx]
      rw [hotb y (Or.inl hnt)]
      exact hSR y hnt

/-! ## 2. The per-statement abstract step and its `seqAll` sequencing -/

/-- The per-statement abstract step of an `RScalarSetExpr` leaf. -/
def wordStep (c : LowCT) : (String → BitVec 64) → (String → BitVec 64) :=
  fun a => match c with
    | .RScalarSetExpr x e => fun s => if s = x then SExpr.evalBV a e else a s
    | _ => a

theorem wordStep_setExpr (x : String) (e : SExpr) :
    wordStep (.RScalarSetExpr x e) = fun a s => if s = x then SExpr.evalBV a e else a s := rfl

/-- `Forall₂` from a per-element relation against a map. -/
theorem forall2_map_self {A B : Type} (R : A → B → Prop) (f : A → B) (l : List A)
    (h : ∀ x ∈ l, R x (f x)) : List.Forall₂ R l (l.map f) := by
  induction l with
  | nil => exact .nil
  | cons c cs ih => exact .cons (h c (.head _)) (ih fun x hx => h x (.tail _ hx))

/-- A left fold of `wordStep`s preserves every name none of the statements write. -/
theorem foldl_wordStep_frame (s : String) :
    ∀ (steps : List LowCT) (a : String → BitVec 64),
      (∀ x e, (LowCT.RScalarSetExpr x e) ∈ steps → s ≠ x) →
      List.foldl (fun acc f => f acc) a (steps.map wordStep) s = a s := by
  intro steps
  induction steps with
  | nil => intro a _; rfl
  | cons c cs ih =>
      intro a h
      simp only [List.map_cons, List.foldl_cons]
      rw [ih (wordStep c a) (fun x e hm => h x e (List.mem_cons_of_mem _ hm))]
      show (wordStep c a) s = a s
      cases c with
      | RScalarSetExpr x e =>
          have hne : s ≠ x := h x e (List.mem_cons.mpr (Or.inl rfl))
          simp only [wordStep, if_neg hne]
      | _ => simp only [wordStep]

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- Sequence a list of per-statement `Corres` leaves through `seqAll`, into one
    `Corres` over the left-folded abstract step (all leaves at the trivial
    precondition, so the `corres_seq` re-establishment is vacuous). -/
theorem corres_seqAll {AState : Type} (SR : SEnvScalar → AState → Prop) :
    ∀ (stmts : List LowCT) (steps : List (AState → AState)),
      List.Forall₂ (fun c f => Corres SR (fun _ => True) f c) stmts steps →
      Corres SR (fun _ => True)
        (fun a => List.foldl (fun acc f => f acc) a steps) (seqAll stmts) := by
  intro stmts
  induction stmts with
  | nil =>
      intro steps h
      cases h
      simpa using corres_skip SR
  | cons c cs ih =>
      intro steps h
      cases h with
      | cons hcf hrest =>
          rename_i f fs
          cases cs with
          | nil =>
              cases hrest
              simpa [seqAll] using hcf
          | cons c' cs' =>
              have hseq := corres_seq SR hcf (ih fs hrest) (fun _ _ => trivial)
              have hrw : seqAll (c :: c' :: cs') = .RSeq c (seqAll (c' :: cs')) := rfl
              rw [hrw]
              exact hseq

/-! ## 3. The `BitVec 64 → ZMod n` readout bridge

The word value model lands in `BitVec 64`; a field/ring leaf reads it out into
`ZMod n` (`n = 2^k` for a `GF(2^k)` nibble/byte, a prime `p` for a prime field, a
power `2^16` for a lattice coefficient). `bvReadout` is the shared reader; on
`n = 2^64` it is the ParamTransfer word encoding `wEnc`. -/

/-- Read a `BitVec 64` word out into `ZMod n` (the field/ring the leaf works in). -/
def bvReadout (n : Nat) (w : BitVec 64) : ZMod n := (w.toNat : ZMod n)

/-- On `n = 2^64` the readout is the ParamTransfer word encoding `wEnc`. -/
theorem wEnc_eq_bvReadout (w : BitVec 64) : wEnc w = bvReadout (2 ^ 64) w := rfl

/-- The readout of a literal word is the cast of its residue. -/
theorem bvReadout_ofNat (n k : Nat) :
    bvReadout n (BitVec.ofNat 64 k) = ((k % 2 ^ 64 : Nat) : ZMod n) := by
  simp only [bvReadout, BitVec.toNat_ofNat]

/-! ## 4. The `corres_solve_scalar` tactic

The scalar analogue of `Ascent.CorresSolver.corres_solve`. It walks the
`RSeq` / `RScalarSetExpr` tree of a straight-line kernel (obtained by unfolding
`seqAll` of a leaf list), applies `corres_setExprWord` at each leaf, discharges
the `srcClean` side condition, and synthesizes the folded abstract step against a
metavariable — the `corres_seq` composition written as a tactic. -/

/-- Rewrite the abstract transition of a `Corres` along an equality. Lets
    `corres_solve_scalar` synthesize the fold against a fresh metavariable and
    reconcile it with the goal's pinned transition afterwards. The `Corres`
    analogue of `CorresSolver.corresJ_castFa`. -/
theorem corres_castFa {AState : Type} {SR : SEnvScalar → AState → Prop}
    {P : AState → Prop} {fa fa' : AState → AState} {c : LowCT}
    (h : Corres SR P fa c) (he : fa = fa') : Corres SR P fa' c :=
  he ▸ h

/-- Discharge a `srcClean e` side condition for a concrete word expression: split
    the conjunctions of the binary nodes, close a `¬ isTmpName` leaf on a short
    source name via `notTmp_of_short`, use a hypothesis for an abstract-argument
    cleanliness assumption, and close a literal bound by `decide`. -/
macro "corres_scalar_clean" : tactic =>
  `(tactic|
    repeat' first
      | assumption
      | exact notTmp_of_short _ (by decide)
      | refine ⟨?_, ?_⟩
      | simp only [srcClean]
      | decide)

/-- Apply the word value leaf `corres_setExprWord` to a single `RScalarSetExpr`
    goal and discharge its `srcClean` side condition. The scalar analogue of
    `CorresSolver.corres_leaf`. -/
macro "corres_leaf_scalar" : tactic =>
  `(tactic| (refine corres_setExprWord _ _ ?_; corres_scalar_clean))

/-- Compose the word value leaves over a straight-line `RSeq` tree against a
    metavariable abstract transition. A single `RScalarSetExpr` leaf is closed by
    `corres_leaf_scalar`; a `.RSeq c₁ c₂` node is split by `corres_seq` — the head
    matched by a leaf, the tail solved recursively, the precondition (all leaves
    have precondition `fun _ => True`) discharged by `fun _ _ => trivial`. The
    transition is a metavariable throughout, so `corres_seq` assigns it the composed
    fold `fun a => ga (fa a)` with no higher-order guessing. -/
syntax "corres_chain_scalar" : tactic
macro_rules
  | `(tactic| corres_chain_scalar) =>
    `(tactic|
      first
      | corres_leaf_scalar
      | (apply corres_seq
         · corres_leaf_scalar
         · corres_chain_scalar
         · exact fun _ _ => trivial))

/-- Refine a `Corres SRwordBV (fun _ => True) _ c` over a straight-line `RSeq` /
    `RScalarSetExpr` tree `c` by composing the `corres_setExprWord` word leaves.
    `corres_castFa` frees the goal's transition to a fresh metavariable,
    `corres_chain_scalar` builds the fold against it, and the residual
    `synthesized-fold = goal-transition` equality closes by `rfl` (they are
    definitionally equal). Composes the small per-statement leaves by application
    rather than elaborating a whole-block symbolic execution. -/
syntax "corres_solve_scalar" : tactic
macro_rules
  | `(tactic| corres_solve_scalar) =>
    `(tactic|
      (apply corres_castFa
       · corres_chain_scalar
       · rfl))

/-! ## 5. Tactic self-tests -/

/-- A ChaCha-style `d := d ^^^ a` closes through `corres_solve_scalar`. -/
example :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = "d" then SExpr.evalBV a (.SXor (.SVar "d") (.SVar "a")) else a s)
      (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a"))) := by
  corres_solve_scalar

/-- A two-statement mix `t := a &&& b; d := t ^^^ c` closes through the tree walk,
    synthesizing the fold `fun a => step₂ (step₁ a)`. -/
example :
    Corres SRwordBV (fun _ => True)
      (fun a => (fun a s => if s = "d" then SExpr.evalBV a (.SXor (.SVar "t") (.SVar "c")) else a s)
        ((fun a s => if s = "t" then SExpr.evalBV a (.SAnd (.SVar "a") (.SVar "b")) else a s) a))
      (.RSeq (.RScalarSetExpr "t" (.SAnd (.SVar "a") (.SVar "b")))
        (.RScalarSetExpr "d" (.SXor (.SVar "t") (.SVar "c")))) := by
  corres_solve_scalar

/-! ## 6. The weld: a `semScalar` `Corres` result to the front `Com.denote`

The front homomorphism `translateDialectControl_denote_ctl` transports the
`semScalar` waist of a covered kernel into the front-compiled
`Com catCryptDialect` denotation. Feeding it a `Corres SRwordBV` result — which
packages both the `semScalar c env = some env'` progress and the readout
`env' dst = some ⟨.sword 64, fa a dst⟩` at a non-temp destination — welds the
value model to the emitted program: closing the front prefix with the return of
the tracked slot `w`, the `Com.denote` reads out `fa a dst`. -/

/-- **The scalar weld.** From a `Corres SRwordBV` result for an `IsCoveredSCtl`
    kernel `c`, entry consistency `ConsistentS vm V env`, the state relation
    `SRwordBV env a` at entry, the front success `translateDialectControl vm c =
    some o`, and the tracked non-temp output `dst ↦ w`, the front prefix closed by
    returning `w` denotes exactly the abstract value `fa a dst` the `Corres` result
    leaves at `dst`. Composes `translateDialectControl_denote_ctl` (the front
    homomorphism) with `ConsistentS.lookup_eq` (the slot readout), the same route
    as `VIR.CompilerCorrectnessExtracted.semScalarToJasminCom_denote_eq`, but
    sourced from an `Ascent.Corres` result over the identity word algebra. -/
theorem corresScalar_frontDenote
    {c : LowCT} (hcov : IsCoveredSCtl c)
    {fa : (String → BitVec 64) → (String → BitVec 64)}
    (hcorr : Corres SRwordBV (fun _ => True) fa c)
    {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env : SEnvScalar) (a : String → BitVec 64)
    (hcons : ConsistentS vm V env) (hSR : SRwordBV env a)
    (o : DTransOut Γ) (htr : translateDialectControl vm c = some o)
    (dst : String) (hdst : ¬ isTmpName dst)
    (w : CVar o.Γ' (.sword 64)) (hw : o.vm.lookup dst = some ⟨.sword 64, w⟩)
    (com : Com catCryptDialect Γ (.sword 64))
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com) :
    com.denote V = fa a dst := by
  obtain ⟨env', hSem, hSR'⟩ := hcorr env a hSR trivial
  have hVal : env' dst = some ⟨.sword 64, fa a dst⟩ := hSR' dst hdst
  obtain ⟨V', hc', hcont⟩ :=
    translateDialectControl_denote_ctl hcov vm V env env' o hcons htr hSem
  obtain ⟨com', hcom', hden⟩ := hcont (Com.ret (toVIRVar w))
  rw [hRet] at hcom'
  obtain rfl := Option.some.inj hcom'
  rw [hden]
  exact hc'.lookup_eq hw hVal

end CatCrypt.Crypto.SecureCompilation.Ascent
