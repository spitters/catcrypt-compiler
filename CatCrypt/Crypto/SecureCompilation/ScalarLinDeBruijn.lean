/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ScalarLinNeutral
import CatCrypt.Crypto.SecureCompilation.ScalarLinFront
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# The general de-Bruijn faithfulness of `Com → RegProg`

The `comToReg` faithfulness is proved bottom-up from discrete lemmas, all of
them in this module:

* `envOf` / `envOf_extend` — reflect a `Com` valuation into the neutral `Env`
  (only `reg 64` bindings are placed) and the law for extending it.
* `repr_inj`, `lvlName_inj`, and `lvlName_ne_xzr` / `lvlName_ne_zero` /
  `lvlName_ne_x0` — level names are injective and never collide with the
  reserved register names.
* `envOf_lookup` and `resolveName_correct` — variable lookup through the
  reflection.
* `opToStmts_bin_correct`, `opToStmts_mulhi_correct`, `opToStmts_shift_correct`,
  `opToStmts_const_correct` — one lemma per supported op class: binary ALU,
  widening-high multiply, immediate shift, materialised constant.
* `comToReg_faithful` — the theorem: for a `ComOK` (supported, straight-line)
  `Com` over an all-`reg 64` context, `Com.denote` equals the neutral
  denotation of the flattened `RegProg` read at the result name.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront

/-- **Lemma 1.** Reflect a `Com` valuation into the neutral env: the head binding
    (de-Bruijn level `depth-1`) lands at `lvlName (depth-1)`, recursively for the
    tail. Only `reg 64` bindings are placed (the field fragment). -/
def envOf : {Γ : Ctxt jasminDialect} → Nat → Ctxt.Valuation Γ → Env
  | [], _, _ => fun _ => 0
  | (.reg 64) :: _, depth, .cons v V' => Env.set (envOf (depth - 1) V') (lvlName (depth - 1)) v
  | _ :: _, depth, .cons _ V' => envOf (depth - 1) V'

/-- **Lemma 2.** Extending the valuation with a new `reg 64` binding `val` updates
    the env at the new level name — by definitional unfolding of `envOf`. -/
theorem envOf_extend {Γ : Ctxt jasminDialect} (depth : Nat)
    (V : Ctxt.Valuation Γ) (val : BitVec 64) :
    envOf (depth + 1) (V.extend (t := JasminTy.reg 64) val)
      = Env.set (envOf depth V) (lvlName depth) val :=
  rfl

/-! ### Milestone A1: `Nat.repr` injectivity (the lemma-3 unblocker)

Proved from scratch via the decimal round-trip — `dval` reads a most-significant-
first digit string back to its value, and `dval (toDigits 10 n) = n`, so `Nat.repr`
(= `String.ofList ∘ toDigits 10`) has a left inverse and is injective. -/

/-- The fold step reading one decimal digit. -/
private def dstep (a : Nat) (c : Char) : Nat := a * 10 + (c.toNat - 48)

/-- The decimal value of a most-significant-first digit-char list. -/
private def dval (cs : List Char) : Nat := cs.foldl dstep 0

private theorem foldl_dstep_acc (cs : List Char) (a : Nat) :
    cs.foldl dstep a = a * 10 ^ cs.length + cs.foldl dstep 0 := by
  induction cs generalizing a with
  | nil => simp
  | cons c cs ih =>
      rw [List.foldl_cons, ih, List.foldl_cons, ih (dstep 0 c), List.length_cons,
        pow_succ, dstep, dstep]
      ring

private theorem dval_cons (c : Char) (cs : List Char) :
    dval (c :: cs) = (c.toNat - 48) * 10 ^ cs.length + dval cs := by
  rw [dval, List.foldl_cons, foldl_dstep_acc, dstep]
  simp only [dval]; ring

private theorem dval_toDigitsCore (fuel : Nat) :
    ∀ (n : Nat) (ds : List Char), n < fuel →
      dval (Nat.toDigitsCore 10 fuel n ds) = n * 10 ^ ds.length + dval ds := by
  induction fuel with
  | zero => intro n ds h; omega
  | succ fuel ih =>
      intro n ds h
      have hmod : n % 10 < 10 := Nat.mod_lt _ (by omega)
      have hchar : (Nat.digitChar (n % 10)).toNat - 48 = n % 10 := by
        interval_cases (n % 10) <;> decide
      unfold Nat.toDigitsCore
      by_cases hn' : n / 10 = 0
      · rw [if_pos hn', dval_cons, hchar, Nat.mod_eq_of_lt (by omega : n < 10)]
      · rw [if_neg hn']
        have hlt : n / 10 < fuel := by
          have := Nat.div_lt_self (show 0 < n by omega) (show 1 < 10 by omega); omega
        rw [ih (n / 10) (Nat.digitChar (n % 10) :: ds) hlt, dval_cons,
          hchar, List.length_cons, pow_succ,
          show n / 10 * (10 ^ ds.length * 10) + ((n % 10) * 10 ^ ds.length + dval ds)
            = (10 * (n / 10) + n % 10) * 10 ^ ds.length + dval ds from by ring,
          Nat.div_add_mod]

/-- **A1.** `Nat.repr` is injective. -/
theorem repr_inj {a b : Nat} (h : a.repr = b.repr) : a = b := by
  have hd : Nat.toDigits 10 a = Nat.toDigits 10 b := by
    have h2 : String.ofList (Nat.toDigits 10 a) = String.ofList (Nat.toDigits 10 b) := h
    have := congrArg String.toList h2
    rwa [String.toList_ofList, String.toList_ofList] at this
  have hv := congrArg dval hd
  rw [Nat.toDigits, Nat.toDigits, dval_toDigitsCore (a + 1) a [] (by omega),
    dval_toDigitsCore (b + 1) b [] (by omega)] at hv
  simpa using hv

/-- **A1 (applied): level names are injective.** -/
theorem lvlName_inj {a b : Nat} (h : lvlName a = lvlName b) : a = b := by
  simp only [lvlName, String.append_right_inj] at h
  exact repr_inj h

/-- A level name is never the zero register `xzr` (it starts with `'v'`). -/
theorem lvlName_ne_xzr (k : Nat) : lvlName k ≠ "xzr" := by
  intro h
  have h2 := congrArg String.toList h
  simp only [lvlName, String.toList_append] at h2
  rw [show "v".toList = ['v'] from rfl, show "xzr".toList = ['x', 'z', 'r'] from rfl,
    List.cons_append, List.nil_append] at h2
  injection h2 with hv _
  exact absurd hv (by decide)

theorem lvlName_ne_zero (k : Nat) : lvlName k ≠ "zero" := by
  intro h
  have h2 := congrArg String.toList h
  simp only [lvlName, String.toList_append] at h2
  rw [show "v".toList = ['v'] from rfl, show "zero".toList = ['z', 'e', 'r', 'o'] from rfl,
    List.cons_append, List.nil_append] at h2
  injection h2 with hv _
  exact absurd hv (by decide)

theorem lvlName_ne_x0 (k : Nat) : lvlName k ≠ "x0" := by
  intro h
  have h2 := congrArg String.toList h
  simp only [lvlName, String.toList_append] at h2
  rw [show "v".toList = ['v'] from rfl, show "x0".toList = ['x', '0'] from rfl,
    List.cons_append, List.nil_append] at h2
  injection h2 with hv _
  exact absurd hv (by decide)

/-! ### Milestone A: lemmas 3–6 of the de-Bruijn faithfulness -/

/-- A variable's de-Bruijn index is below the context length. -/
theorem varIndex_lt {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t) :
    varIndex v < Γ.length := by
  induction v with
  | here => simp [varIndex]
  | there v' ih => simp only [varIndex, List.length_cons]; omega

/-- A context whose bindings are all `reg 64` (the field fragment). -/
def AllReg64 (Γ : Ctxt jasminDialect) : Prop := ∀ t ∈ Γ, t = JasminTy.reg 64

/-- **Lemma 3 (`envOf_lookup`).** Over an all-`reg 64` context, every variable reads
    back its valuation value from its level name — the `.ret` base case. -/
theorem envOf_lookup {Γ : Ctxt jasminDialect} (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) (v : Ctxt.Var Γ (.reg 64)) :
    (envOf Γ.length V) (lvlName (Γ.length - 1 - varIndex v)) = v.lookup V := by
  -- `HEq` lets us induct with the type index a variable, no cast in the statement
  suffices h : ∀ {Δ : Ctxt jasminDialect} {t : JasminTy} (w : Ctxt.Var Δ t)
      (W : Ctxt.Valuation Δ), AllReg64 Δ →
      HEq ((envOf Δ.length W) (lvlName (Δ.length - 1 - varIndex w))) (w.lookup W) by
    exact eq_of_heq (h v V hΓ)
  intro Δ t w
  induction w with
  | @here Δ' =>
      intro W hΔ
      cases W with | cons val W' =>
      have hτ := hΔ _ (List.mem_cons_self ..)
      subst hτ
      apply heq_of_eq
      simp only [varIndex, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, envOf,
        Ctxt.Var.lookup]
      exact Env.set_self _ _ _ (lvlName_ne_xzr _)
  | @there Δ' tt s w' ih =>
      intro W hΔ
      cases W with | cons hval W' =>
      have hs := hΔ _ (List.mem_cons_self ..)
      subst hs
      have hΔ' : AllReg64 Δ' := fun u hu => hΔ u (List.mem_cons_of_mem _ hu)
      have hvlt : varIndex w' < Δ'.length := varIndex_lt w'
      apply HEq.trans _ (ih W' hΔ')
      apply heq_of_eq
      simp only [varIndex, List.length_cons, Nat.add_sub_cancel, envOf, Ctxt.Var.lookup]
      have hne : Δ'.length - 1 - varIndex w' ≠ Δ'.length := by omega
      rw [show Δ'.length - (varIndex w' + 1) = Δ'.length - 1 - varIndex w' from by omega]
      exact Env.set_other _ _ _ _ (fun hq => hne (lvlName_inj hq))

/-- **Lemma 4 (`resolveName_correct`).** At `depth = Γ.length` over an all-`reg 64`
    context, the env (`Env.get`) reads a variable's resolved name back to its
    valuation value. Direct from `envOf_lookup` (the name is never `xzr`). -/
theorem resolveName_correct {Γ : Ctxt jasminDialect} (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) (v : Ctxt.Var Γ (.reg 64)) :
    Env.get (envOf Γ.length V) (resolveName Γ.length v) = v.lookup V := by
  rw [resolveName, Env.get, if_neg (lvlName_ne_xzr _)]
  exact envOf_lookup hΓ V v

/-! The recursive `exprSrcs.go`/`lookupArgs` will not reduce under generic `simp`
    lemmas — `simp` cannot unify the recursor against an abstract pattern. The
    working automation is a pair of LOCAL `rfl`-`have`s per op-arity (whose LHS is
    the exact goal term, so `simp` rewrites them directly). -/

/-- **Lemma 5a — binary ALU ops** (`add/sub/mul/and/or/xor`). -/
theorem opToStmts_bin_correct {Γ : Ctxt jasminDialect} (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) (bop : JasminBinOp)
    (e : Expr jasminDialect Γ (.reg 64)) (hop : e.op = JasminOp.regArith bop 64)
    (hbop : bop = .add ∨ bop = .sub ∨ bop = .mul ∨ bop = .and ∨ bop = .or ∨ bop = .xor) :
    RegProg.denotePure (opToStmts (lvlName Γ.length) (exprSrcs Γ.length e) e.op)
        (envOf Γ.length V)
      = Env.set (envOf Γ.length V) (lvlName Γ.length) (e.denote V) := by
  obtain ⟨op, hretTy, args⟩ := e
  simp only at hop; subst hop
  match args with
  | .cons a (.cons b .nil) =>
    have ha := resolveName_correct hΓ V a
    have hb := resolveName_correct hΓ V b
    have hsrcs : exprSrcs.go (Γ := Γ) Γ.length (HVector.cons a (HVector.cons b HVector.nil))
        = [resolveName Γ.length a, resolveName Γ.length b] := rfl
    have hla : Expr.lookupArgs (HVector.cons a (HVector.cons b HVector.nil)) V
        = HVector.cons (a.lookup V) (HVector.cons (b.lookup V) HVector.nil) := rfl
    rcases hbop with h | h | h | h | h | h <;> subst h <;>
      simp only [exprSrcs, hsrcs, hla, Expr.denote, HVector.head, HVector.tail,
        DialectDenote.denote, jasminDenote, JasminBinOp.apply, opToStmts, RegProg.denotePure,
        List.foldl_cons, List.foldl_nil, evalRegStmtPure, ha, hb]

/-- **Lemma 5b — widening-high multiply** (`mulhi → umulh`); same shape, with the
    `>>> 64`/`/2^64` identity bridging `evalRegStmtPure`'s `umulh` to `mulHiW`. -/
theorem opToStmts_mulhi_correct {Γ : Ctxt jasminDialect} (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) (e : Expr jasminDialect Γ (.reg 64))
    (hop : e.op = JasminOp.mulhi 64) :
    RegProg.denotePure (opToStmts (lvlName Γ.length) (exprSrcs Γ.length e) e.op)
        (envOf Γ.length V)
      = Env.set (envOf Γ.length V) (lvlName Γ.length) (e.denote V) := by
  obtain ⟨op, hretTy, args⟩ := e
  simp only at hop; subst hop
  match args with
  | .cons a (.cons b .nil) =>
    have ha := resolveName_correct hΓ V a
    have hb := resolveName_correct hΓ V b
    have hsrcs : exprSrcs.go (Γ := Γ) Γ.length (HVector.cons a (HVector.cons b HVector.nil))
        = [resolveName Γ.length a, resolveName Γ.length b] := rfl
    have hla : Expr.lookupArgs (HVector.cons a (HVector.cons b HVector.nil)) V
        = HVector.cons (a.lookup V) (HVector.cons (b.lookup V) HVector.nil) := rfl
    simp only [exprSrcs, hsrcs, hla, Expr.denote, HVector.head, HVector.tail,
      DialectDenote.denote, jasminDenote, opToStmts, RegProg.denotePure, List.foldl_cons,
      List.foldl_nil, evalRegStmtPure, ha, hb, mulHiW, Nat.shiftRight_eq_div_pow]

/-- **Lemma 5c — immediate shifts** (`shrImm → shrI`, `shlImm → shlI`). Unary. -/
theorem opToStmts_shift_correct {Γ : Ctxt jasminDialect} (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) (n : Nat) (e : Expr jasminDialect Γ (.reg 64))
    (hop : e.op = JasminOp.shrImm 64 n ∨ e.op = JasminOp.shlImm 64 n) :
    RegProg.denotePure (opToStmts (lvlName Γ.length) (exprSrcs Γ.length e) e.op)
        (envOf Γ.length V)
      = Env.set (envOf Γ.length V) (lvlName Γ.length) (e.denote V) := by
  obtain ⟨op, hretTy, args⟩ := e
  rcases hop with hop | hop <;> simp only at hop <;> subst hop <;>
  · match args with
    | .cons a .nil =>
      have ha := resolveName_correct hΓ V a
      have hsrcs : exprSrcs.go (Γ := Γ) Γ.length (HVector.cons a HVector.nil)
          = [resolveName Γ.length a] := rfl
      have hla : Expr.lookupArgs (HVector.cons a HVector.nil) V
          = HVector.cons (a.lookup V) HVector.nil := rfl
      simp only [exprSrcs, hsrcs, hla, Expr.denote, HVector.head, DialectDenote.denote,
        jasminDenote, opToStmts, RegProg.denotePure, List.foldl_cons, List.foldl_nil,
        evalRegStmtPure, ha]

/-! ### Lemma 5d — materialised constants (`regConst → loadImm`)

With the backend-neutral `loadImm` op, the front lowers a `regConst` to a single
`loadImm`, whose neutral semantics is the direct `set dst (BitVec.ofNat 64 n)`. So
this op-lemma is now trivial — the `movz`/`movk` bit-reconstruction (and its
`bv_decide` cost) moves down into the *ARM lowering* of `loadImm`, where it
belongs, keeping the neutral faithfulness layer free of SAT-certificate axioms. -/

/-- **The forward computation (now trivial).** `loadConstStmts dst n = [loadImm dst n]`
    sets `dst` to `BitVec.ofNat 64 n` and leaves every other register untouched. -/
theorem loadConst_env (dst : String) (n : Nat) (E : Env) :
    RegProg.denotePure (loadConstStmts dst n) E = Env.set E dst (BitVec.ofNat 64 n) := by
  simp only [loadConstStmts, RegProg.denotePure_cons, RegProg.denotePure_nil, evalRegStmtPure]

/-- **Lemma 5d — materialised constants.** Same op-lemma shape as 5a–5c: the
    flattened `regConst` block, denoted, sets the result register to the constant
    `BitVec.ofNat 64 n` ( = the `regConst` op's denotation). -/
theorem opToStmts_const_correct {Γ : Ctxt jasminDialect}
    (V : Ctxt.Valuation Γ) (n : Nat) (e : Expr jasminDialect Γ (.reg 64))
    (hop : e.op = JasminOp.regConst 64 n) :
    RegProg.denotePure (opToStmts (lvlName Γ.length) (exprSrcs Γ.length e) e.op)
        (envOf Γ.length V)
      = Env.set (envOf Γ.length V) (lvlName Γ.length) (e.denote V) := by
  obtain ⟨op, hretTy, args⟩ := e
  simp only at hop; subst hop
  rw [show opToStmts (lvlName Γ.length)
        (exprSrcs Γ.length (⟨JasminOp.regConst 64 n, hretTy, args⟩ : Expr jasminDialect Γ (.reg 64)))
        (JasminOp.regConst 64 n) = loadConstStmts (lvlName Γ.length) n from rfl,
      loadConst_env _ n _]
  congr 1

/-! ### Milestone A, lemma 6: the `Com` faithfulness theorem -/

/-- The op kinds the flattening front handles: binary ALU (5a), widening-high
    multiply (5b), immediate shifts (5c), materialised constants (5d). -/
def SupportedOp (op : JasminOp) : Prop :=
  (∃ bop, op = JasminOp.regArith bop 64 ∧
      (bop = .add ∨ bop = .sub ∨ bop = .mul ∨ bop = .and ∨ bop = .or ∨ bop = .xor)) ∨
  op = JasminOp.mulhi 64 ∨
  (∃ k, op = JasminOp.shrImm 64 k ∨ op = JasminOp.shlImm 64 k) ∨
  (∃ k, op = JasminOp.regConst 64 k)

/-! ### `SupportedOp` smart constructors + the `supported_op` tactic

Robustness layer for the golden-path `ComOK` witnesses: instead of spelling the
`SupportedOp` disjunction by hand (`Or.inl ⟨.add, rfl, Or.inl rfl⟩`, …) at every
call site, kernels use `ComOK.var (by supported_op) …`. The disjunction's *shape*
lives ONLY in these ~10 proofs, so a refactor of `SupportedOp` (e.g. the MLIR-dialect
alignment that splits `jasminDialect` into `arith`/`memref`/…) updates these, not the
hundreds of call sites across the `*GoldenPath` library. -/

theorem SupportedOp.regAdd : SupportedOp (.regArith .add 64) := Or.inl ⟨.add, rfl, Or.inl rfl⟩
theorem SupportedOp.regSub : SupportedOp (.regArith .sub 64) :=
  Or.inl ⟨.sub, rfl, Or.inr (Or.inl rfl)⟩
theorem SupportedOp.regMul : SupportedOp (.regArith .mul 64) :=
  Or.inl ⟨.mul, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
theorem SupportedOp.regAnd : SupportedOp (.regArith .and 64) :=
  Or.inl ⟨.and, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
theorem SupportedOp.regOr : SupportedOp (.regArith .or 64) :=
  Or.inl ⟨.or, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
theorem SupportedOp.regXor : SupportedOp (.regArith .xor 64) :=
  Or.inl ⟨.xor, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
theorem SupportedOp.mulhi : SupportedOp (.mulhi 64) := Or.inr (Or.inl rfl)
theorem SupportedOp.shrImm (k : Nat) : SupportedOp (.shrImm 64 k) :=
  Or.inr (Or.inr (Or.inl ⟨k, Or.inl rfl⟩))
theorem SupportedOp.shlImm (k : Nat) : SupportedOp (.shlImm 64 k) :=
  Or.inr (Or.inr (Or.inl ⟨k, Or.inr rfl⟩))
theorem SupportedOp.regConst (n : Nat) : SupportedOp (.regConst 64 n) :=
  Or.inr (Or.inr (Or.inr ⟨n, rfl⟩))

/-- Proves `SupportedOp <concrete op>` by dispatching to the smart constructors —
    the single point a `SupportedOp` refactor must keep working. -/
macro "supported_op" : tactic =>
  `(tactic| first
    | exact SupportedOp.regAdd | exact SupportedOp.regSub | exact SupportedOp.regMul
    | exact SupportedOp.regAnd | exact SupportedOp.regOr  | exact SupportedOp.regXor
    | exact SupportedOp.mulhi
    | exact SupportedOp.shrImm _ | exact SupportedOp.shlImm _ | exact SupportedOp.regConst _)

/-- **Unified op-correctness.** For any supported op, the flattened block sets the
    result register to the op's denotation — one dispatch over lemmas 5a–5d. -/
theorem opToStmts_correct {Γ : Ctxt jasminDialect} (hΓ : AllReg64 Γ)
    (V : Ctxt.Valuation Γ) (e : Expr jasminDialect Γ (.reg 64)) (hsupp : SupportedOp e.op) :
    RegProg.denotePure (opToStmts (lvlName Γ.length) (exprSrcs Γ.length e) e.op)
        (envOf Γ.length V)
      = Env.set (envOf Γ.length V) (lvlName Γ.length) (e.denote V) := by
  rcases hsupp with ⟨bop, hop, hbop⟩ | hop | ⟨k, hop⟩ | ⟨k, hop⟩
  · exact opToStmts_bin_correct hΓ V bop e hop hbop
  · exact opToStmts_mulhi_correct hΓ V e hop
  · exact opToStmts_shift_correct hΓ V k e hop
  · exact opToStmts_const_correct V k e hop

/-- The straight-line `Com` fragment the front handles: all bindings `reg 64`,
    every op `SupportedOp` (binary ALU, widening-high multiply, immediate shift,
    materialised constant). -/
inductive ComOK : {Γ : Ctxt jasminDialect} → Com jasminDialect Γ (.reg 64) → Prop where
  | ret {Γ : Ctxt jasminDialect} (v : Ctxt.Var Γ (.reg 64)) : ComOK (.ret v)
  | var {Γ : Ctxt jasminDialect} {e : Expr jasminDialect Γ (.reg 64)}
      {body : Com jasminDialect ((.reg 64) :: Γ) (.reg 64)}
      (hsupp : SupportedOp e.op) (hbody : ComOK body) : ComOK (.var e body)

/-- **Lemma 6 — the de-Bruijn faithfulness theorem.** For a supported straight-line
    `Com` over an all-`reg 64` context, the source `Com.denote` equals the neutral
    denotation of the flattened `RegProg` read at the result name. The `Com → RegProg`
    front is faithful over the full field-leaf op alphabet. -/
theorem comToReg_faithful : ∀ {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)},
    ComOK com → AllReg64 Γ → ∀ (V : Ctxt.Valuation Γ),
      Com.denote com V
        = (RegProg.denotePure (comToRegProg com Γ.length) (envOf Γ.length V))
            (comRetName com Γ.length) := by
  intro Γ com hok
  induction hok with
  | @ret Γ v =>
      intro hΓ V
      simp only [Com.denote, comToRegProg_ret, comRetName_ret, RegProg.denotePure_nil]
      exact (envOf_lookup hΓ V v).symm
  | @var Γ e body hsupp hbody ih =>
      intro hΓ V
      have hΓ' : AllReg64 ((.reg 64) :: Γ) := by
        intro u hu; rcases List.mem_cons.mp hu with h | h
        · exact h
        · exact hΓ u h
      have hlen : ((.reg 64) :: Γ).length = Γ.length + 1 := rfl
      simp only [Com.denote, comToRegProg_var, comRetName_var, RegProg.denotePure_append,
        opToStmts_correct hΓ V e hsupp, ← envOf_extend]
      rw [hlen] at ih
      exact ih hΓ' (V.extend (e.denote V))

end CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
