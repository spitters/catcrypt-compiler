/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ScalarLinNeutral
public import CatCrypt.Crypto.SecureCompilation.ScalarLinFront
public import CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Model
public import CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

/-!
# `Com → x86`: the x86-64 `ScalarTarget` instance + the end-to-end theorem

The x86 analogue of `com_arm_e2e` / `com_riscv_e2e`: a `ScalarTarget` over the
executable native-Lean x86 model (`X86Backend.Model`), and the composed
`com_x86_e2e` lifting the shared, axiom-clean `comToReg_faithful` to the x86
machine run. For a `Com` with `ComOK` over an `AllReg64` context, whose compiled
shift amounts satisfy `ShiftAmtOK`, run from a state whose registers are
`envOf Γ.length V`, the compiled x86 block read at the result register equals
`Com.denote com V` for every valuation. The x86 semantics is the `step` function
of `X86Backend.Model`.

## Why the selection is two-address (and the freshness side condition)

The AArch64/RISC-V instruction selections are 1:1 (three-address `add d a b`).
The x86 model is **two-address** (`add dst src` ⟹ `dst := dst + src`), so each
binary `RegStmt` lowers to a pair `mov dst a ; op dst b`. That sequence realises
the three-address effect **iff the destination is distinct from both sources**
(`d ∉ {a, b}`) — otherwise the leading `mov` clobbers a source. The de-Bruijn
front guarantees exactly this: the destination of a binding is `lvlName depth`
while every source is `lvlName (< depth)`, so `dst ≠ src` always on compiled
programs. We therefore plug into the **restricted** neutral lift
`compile_denote_pure_on` (as RISC-V does for its `zero`/`x0` convention), with an
`X86FaithfulStmt` predicate (`dst` fresh + no `"xzr"`), discharged automatically
by `comToRegProg_X86Faithful`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.X86Backend

/-- The x86 model state at the fixed 64-bit width (the `St` of `x86Target`). -/
abbrev XState := State 64

/-- The x86 model instruction at the fixed 64-bit width (the `Op` of `x86Target`). -/
abbrev XInstr := Instr 64

/-- The machine run of an instruction block (left-to-right `step` fold). -/
def xrun (s : XState) (ops : List XInstr) : XState := ops.foldl (fun st op => step st op) s

/-! ## 1. Instruction selection: `RegStmt → List XInstr` (two-address) -/

/-- Select the x86 instruction(s) for one statement. Binary ops lower to the
    two-address pair `mov dst a ; op dst b`; the shift-by-immediate ops to
    `mov dst a ; shift dst imm`; `mov`/constant-load to a single `mov`/immediate.
    `umulh` uses `MULX dst, dst, a, b`: the high word lands in `dst` (it is the
    second write to the same register, so it wins — exactly the `umulh`
    semantics; the low word is discarded). -/
def toX86 : RegStmt → List XInstr
  | .add d a b   => [.mov d (.reg a), .add d (.reg b)]
  | .sub d a b   => [.mov d (.reg a), .sub d (.reg b)]
  | .mul d a b   => [.mov d (.reg a), .mul d (.reg b)]
  | .and d a b   => [.mov d (.reg a), .and_ d (.reg b)]
  | .orr d a b   => [.mov d (.reg a), .or_ d (.reg b)]
  | .eor d a b   => [.mov d (.reg a), .xor_ d (.reg b)]
  | .umulh d a b => [.mulx d d (.reg a) (.reg b)]
  | .shrI d a i  => [.mov d (.reg a), .shr d (.imm i)]
  | .shlI d a i  => [.mov d (.reg a), .shl d (.imm i)]
  | .mov d a     => [.mov d (.reg a)]
  | .movz d i    => [.mov d (.imm (i % 0x10000))]
  | .movk d _ _  => [.mov d (.reg d)]
  | .loadImm d n => [.mov d (.imm n)]

/-! ## 2. The x86 `ScalarTarget` instance

`runOps`/`step` are the foldl of the executable model `step` over the selected
block, so `select_correct` is definitional. The structural fields are list folds. -/

/-- The x86 backend as a `ScalarTarget`. The source effect `step` is *defined* as
    the machine run of the selected ops, making `select_correct` a `rfl`; the real
    faithfulness content is `hstep_x86_on` (the projected machine run computes the
    neutral `evalRegStmtPure`, under the freshness side condition). -/
@[implicit_reducible]
def x86Target : ScalarTarget where
  Op := XInstr
  St := XState
  runOps := xrun
  runOps_nil _ := rfl
  runOps_append xs ys s := by simp only [xrun, List.foldl_append]
  step s stmt := xrun s (toX86 stmt)
  toOps := toX86
  select_correct _ _ := rfl

/-- Compile a whole program to an x86 instruction block. -/
def regToX86 (p : RegProg) : List XInstr := x86Target.compile p

/-! ## 3. The compile-denote theorem, as an instance -/

/-- The x86 instance of `ScalarTarget.compile_denote`: the compiled-and-run x86
    block computes the source program's denotation. -/
theorem regToX86_denote (p : RegProg) (s : XState) :
    xrun s (regToX86 p) = x86Target.denote p s :=
  x86Target.compile_denote p s

/-! ## 4. x86 plugs into the neutral semantics (on faithful statements)

The x86 model has raw (non-`xzr`-special) registers, and the two-address
selection clobbers a source if the destination aliases it. Both are captured by
`X86FaithfulStmt`; under it, the projected machine run matches `evalRegStmtPure`. -/

/-- A statement x86 faithfully realises through the two-address selection: every
    mentioned register avoids `"xzr"` (the model is raw, the neutral env is not),
    and the destination is distinct from each source (so the leading `mov` does
    not clobber a source). The de-Bruijn front always emits such statements. -/
def X86FaithfulStmt : RegStmt → Prop
  | .add d a b | .sub d a b | .mul d a b | .and d a b
  | .orr d a b | .eor d a b | .umulh d a b =>
      d ≠ "xzr" ∧ a ≠ "xzr" ∧ b ≠ "xzr" ∧ d ≠ a ∧ d ≠ b
  | .shrI d a i | .shlI d a i =>
      d ≠ "xzr" ∧ a ≠ "xzr" ∧ d ≠ a ∧ i < 2 ^ 64
  | .mov d a => d ≠ "xzr" ∧ a ≠ "xzr" ∧ d ≠ a
  | .loadImm d _ => d ≠ "xzr"
  -- `movz`/`movk` are ARM-specific constant-load primitives the front never emits
  -- (it materialises constants via the backend-neutral `loadImm`); excluded so the
  -- two-address x86 selection need not realise the ARM `movk` mask-insert.
  | .movz _ _ | .movk _ _ _ => False

/-- **x86 per-statement faithfulness.** For a faithful statement, the x86 machine
    run of the selected block, projected to the registers, equals the neutral
    `evalRegStmtPure`. This is the x86-specific step of the end-to-end theorem:
    the two-address `mov;op` realises the three-address effect when the destination
    differs from each source. -/
theorem hstep_x86_on (s : XState) (stmt : RegStmt) (h : X86FaithfulStmt stmt) :
    (x86Target.step s stmt).regs = evalRegStmtPure s.regs stmt := by
  cases stmt <;>
    simp only [x86Target, xrun, toX86, step, X86FaithfulStmt, evalRegStmtPure,
      State.set, State.setALU, State.setLoHi, State.get, Env.set, Env.get,
      mulHi, Operand.eval, addCarry, List.foldl_cons, List.foldl_nil,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at h ⊢
  -- binary ops: `mov d a ; op d b`; freshness `d ≠ b` removes the alias `if b = d`
  case add d a b => obtain ⟨hd, ha, hb, _, hdb⟩ := h
                    funext r'; by_cases hr : r' = d <;>
                      simp_all [Ne.symm hdb]
  case sub d a b => obtain ⟨hd, ha, hb, _, hdb⟩ := h
                    funext r'; by_cases hr : r' = d <;>
                      simp_all [Ne.symm hdb]
  case mul d a b => obtain ⟨hd, ha, hb, _, hdb⟩ := h
                    funext r'; by_cases hr : r' = d <;>
                      simp_all [Ne.symm hdb]
  case and d a b => obtain ⟨hd, ha, hb, _, hdb⟩ := h
                    funext r'; by_cases hr : r' = d <;>
                      simp_all [Ne.symm hdb]
  case orr d a b => obtain ⟨hd, ha, hb, _, hdb⟩ := h
                    funext r'; by_cases hr : r' = d <;>
                      simp_all [Ne.symm hdb]
  case eor d a b => obtain ⟨hd, ha, hb, _, hdb⟩ := h
                    funext r'; by_cases hr : r' = d <;>
                      simp_all [Ne.symm hdb]
  case umulh d a b => obtain ⟨hd, ha, hb, _, _⟩ := h
                      funext r'; by_cases hr : r' = d <;>
                        simp_all
  case shrI d a i => obtain ⟨hd, ha, _, hi⟩ := h
                     rw [Nat.mod_eq_of_lt hi]
                     funext r'; by_cases hr : r' = d <;> simp_all
  case shlI d a i => obtain ⟨hd, ha, _, hi⟩ := h
                     rw [Nat.mod_eq_of_lt hi]
                     funext r'; by_cases hr : r' = d <;> simp_all
  case mov d a => obtain ⟨hd, ha, _⟩ := h
                  funext r'; by_cases hr : r' = d <;> simp_all
  -- `movz`/`movk` are excluded by `X86FaithfulStmt` (`= False`), so `simp … at h`
  -- already closed them from the vacuous hypothesis; only `loadImm` remains.
  case loadImm d n => funext r'; by_cases hr : r' = d <;> simp_all

/-! ## 5. Every compiled statement is `X86Faithful`

The destination of each emitted statement is `lvlName depth`; every source is a
`lvlName j` with `j < depth` (a `Γ`-variable index, `< Γ.length = depth`). So no
name is `"xzr"` (every name is a `lvlName`) and `dst ≠ src` (`lvlName_inj` on
`depth ≠ j`). This mirrors `MultiBackendDemo.comToRegProg_RvFaithful`, adding the
destination-freshness clause the two-address lowering needs. -/

/-- Every operand name `exprSrcs` produces at depth `Γ.length` avoids `"xzr"` and
    differs from the destination `lvlName Γ.length` — sources are `Γ`-variables,
    whose level `Γ.length - 1 - idx` is strictly below `Γ.length` (`varIndex_lt`),
    so `lvlName_inj` separates them from the destination. -/
theorem exprSrcs_props {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) :
    ∀ r ∈ exprSrcs Γ.length e, r ≠ "xzr" ∧ r ≠ lvlName Γ.length := by
  have hgo : ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ r ∈ exprSrcs.go (Γ := Γ) Γ.length hv, r ≠ "xzr" ∧ r ≠ lvlName Γ.length := by
    intro tys hv
    induction hv with
    | nil => intro r hr; simp [exprSrcs.go] at hr
    | cons v rest ih =>
        intro r hr
        rw [show exprSrcs.go (Γ := Γ) Γ.length (HVector.cons v rest)
              = resolveName Γ.length v :: exprSrcs.go (Γ := Γ) Γ.length rest from rfl] at hr
        rcases List.mem_cons.mp hr with h | h
        · subst h
          refine ⟨lvlName_ne_xzr _, fun hq => ?_⟩
          have := varIndex_lt v
          exact absurd (lvlName_inj hq) (by omega)
        · exact ih r h
  exact hgo e.args

/-- The shift-count side condition the x86 model needs: an immediate shift by `i`
    matches the neutral `>>> i` only when `i < 2^64` (else the x86 operand wraps
    `i` modulo `2^64`). The Model header records this as the shift-count caveat;
    every shift the front emits is a small compile-time constant, so it holds. The
    other statement forms are unconstrained (`True`). -/
def ShiftAmtOK : RegStmt → Prop
  | .shrI _ _ i | .shlI _ _ i => i < 2 ^ 64
  | _ => True

/-- **Every statement `opToStmts` emits at depth `Γ.length` is `X86Faithful`**,
    given that its shift amounts are in range (`ShiftAmtOK`). -/
theorem opToStmts_X86Faithful {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ)
    (hsh : ∀ stmt ∈ opToStmts (lvlName Γ.length) (exprSrcs Γ.length e) e.op,
      ShiftAmtOK stmt) :
    ∀ stmt ∈ opToStmts (lvlName Γ.length) (exprSrcs Γ.length e) e.op,
      X86FaithfulStmt stmt := by
  have hsrc := exprSrcs_props e
  have hd : lvlName Γ.length ≠ "xzr" := lvlName_ne_xzr _
  intro stmt hstmt
  -- per-element facts, extracted from `hsrc` *before* any `simp` consumes it
  have srcFact : ∀ r ∈ exprSrcs Γ.length e,
      r ≠ "xzr" ∧ lvlName Γ.length ≠ r := fun r hr =>
    ⟨(hsrc r hr).1, fun hq => (hsrc r hr).2 hq.symm⟩
  -- the shift-amount fact, captured from the original membership
  have hshStmt : ShiftAmtOK stmt := hsh stmt hstmt
  cases hop : e.op with
  | regArith bop w =>
      rw [hop] at hstmt
      cases bop <;>
        (rcases hs : exprSrcs Γ.length e with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
          rw [hs] at hstmt <;>
          first
          | (have ha := srcFact a (by rw [hs]; simp); have hb := srcFact b (by rw [hs]; simp)
             simp only [opToStmts, List.mem_singleton] at hstmt
             rw [hstmt]; exact ⟨hd, ha.1, hb.1, ha.2, hb.2⟩)
          | simp_all [opToStmts])
  | mulhi w =>
      rw [hop] at hstmt
      rcases hs : exprSrcs Γ.length e with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
        rw [hs] at hstmt <;>
        first
        | (have ha := srcFact a (by rw [hs]; simp); have hb := srcFact b (by rw [hs]; simp)
           simp only [opToStmts, List.mem_singleton] at hstmt
           rw [hstmt]; exact ⟨hd, ha.1, hb.1, ha.2, hb.2⟩)
        | simp_all [opToStmts]
  | shrImm w n =>
      rw [hop] at hstmt
      rcases hs : exprSrcs Γ.length e with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;>
        rw [hs] at hstmt <;>
        first
        | (have ha := srcFact a (by rw [hs]; simp)
           simp only [opToStmts, List.mem_singleton] at hstmt
           have hn : n < 2 ^ 64 := by rw [hstmt] at hshStmt; simpa [ShiftAmtOK] using hshStmt
           rw [hstmt]; exact ⟨hd, ha.1, ha.2, hn⟩)
        | simp_all [opToStmts]
  | shlImm w n =>
      rw [hop] at hstmt
      rcases hs : exprSrcs Γ.length e with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;>
        rw [hs] at hstmt <;>
        first
        | (have ha := srcFact a (by rw [hs]; simp)
           simp only [opToStmts, List.mem_singleton] at hstmt
           have hn : n < 2 ^ 64 := by rw [hstmt] at hshStmt; simpa [ShiftAmtOK] using hshStmt
           rw [hstmt]; exact ⟨hd, ha.1, ha.2, hn⟩)
        | simp_all [opToStmts]
  | regConst w n =>
      rw [hop] at hstmt
      simp only [opToStmts, loadConstStmts, List.mem_singleton] at hstmt
      rw [hstmt]; exact hd
  | _ => rw [hop] at hstmt; simp_all [opToStmts]

/-- **Every compiled statement is `X86Faithful`** — the side condition, discharged
    for any `Com` by induction (no `ComOK` needed; unsupported ops emit nothing),
    given the compiled shift amounts are in range (`ShiftAmtOK`). -/
theorem comToRegProg_X86Faithful {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t)
    (hsh : ∀ stmt ∈ comToRegProg com Γ.length, ShiftAmtOK stmt) :
    ∀ stmt ∈ comToRegProg com Γ.length, X86FaithfulStmt stmt := by
  suffices h : ∀ {Δ : Ctxt jasminDialect} {s : JasminTy} (c : Com jasminDialect Δ s),
      (∀ stmt ∈ comToRegProg c Δ.length, ShiftAmtOK stmt) →
      ∀ stmt ∈ comToRegProg c Δ.length, X86FaithfulStmt stmt from h com hsh
  intro Δ s c
  induction c with
  | ret v =>
      intro _ stmt hstmt; simp only [comToRegProg_ret] at hstmt
      exact absurd hstmt List.not_mem_nil
  | @var Δ' tt ss e body ih =>
      intro hsh' stmt hstmt
      have hsh'' := hsh'
      rw [comToRegProg_var] at hstmt hsh''
      rcases List.mem_append.mp hstmt with h | h
      · exact opToStmts_X86Faithful e
          (fun st hst => hsh'' st (List.mem_append.mpr (Or.inl hst))) stmt h
      · exact ih (fun st hst => hsh'' st (List.mem_append.mpr (Or.inr hst))) stmt h

/-! ## 6. End-to-end: the compiled x86 block computes `Com.denote` -/

/-- **General end-to-end x86 with side condition** (mirror of `com_riscv_e2e_of`).
    For any supported `Com` over an all-`reg 64` context whose compiled statements
    x86 faithfully realises (`hf` — automatic in practice), the compiled-and-run
    x86 block, read at the result register, computes the source `Com.denote`.
    Composes the restricted lift `compile_denote_pure_on` with the shared
    axiom-clean `comToReg_faithful`. -/
theorem com_x86_e2e_of {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)}
    (hok : ComOK com) (hΓ : AllReg64 Γ) (V : Ctxt.Valuation Γ) (s : XState)
    (hs : s.regs = envOf Γ.length V)
    (hf : ∀ stmt ∈ comToRegProg com Γ.length, X86FaithfulStmt stmt) :
    ((x86Target.runOps s
        (x86Target.compile (comToRegProg com Γ.length))).regs) (comRetName com Γ.length)
      = Com.denote com V := by
  have key : (x86Target.runOps s
      (x86Target.compile (comToRegProg com Γ.length))).regs
      = RegProg.denotePure (comToRegProg com Γ.length) s.regs :=
    ScalarTarget.compile_denote_pure_on x86Target (fun s => s.regs) X86FaithfulStmt
      hstep_x86_on (comToRegProg com Γ.length) hf s
  rw [congrFun key, hs]
  exact (comToReg_faithful hok hΓ V).symm

/-- **General end-to-end x86** (full mirror of `com_arm_e2e`). The register-freshness
    faithfulness is discharged automatically by `comToRegProg_X86Faithful`; the only
    remaining side condition is the shift-count range `ShiftAmtOK`, which holds
    trivially for shift-free kernels such as `FieldEmitGoldenPath.fieldAddCom`. -/
theorem com_x86_e2e {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)}
    (hok : ComOK com) (hΓ : AllReg64 Γ) (V : Ctxt.Valuation Γ) (s : XState)
    (hs : s.regs = envOf Γ.length V)
    (hsh : ∀ stmt ∈ comToRegProg com Γ.length, ShiftAmtOK stmt) :
    ((x86Target.runOps s
        (x86Target.compile (comToRegProg com Γ.length))).regs) (comRetName com Γ.length)
      = Com.denote com V :=
  com_x86_e2e_of hok hΓ V s hs (comToRegProg_X86Faithful com hsh)

/-! ## 7. Applications -/

/-- **End-to-end x86 on `fieldAddCom`** (`v2 := v0 + v1`): the compiled x86 block,
    run from a matching state, computes the source field-add denotation. The x86
    leg of the same source the ARM/RISC-V e2e theorems discharge. -/
theorem fieldAddCom_x86_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect)) (s : XState)
    (hs : s.regs = envOf 2 V) :
    ((x86Target.runOps s
        (x86Target.compile (comToRegProg FieldEmitGoldenPath.fieldAddCom 2))).regs)
        (comRetName FieldEmitGoldenPath.fieldAddCom 2)
      = Com.denote FieldEmitGoldenPath.fieldAddCom V :=
  com_x86_e2e FieldEmitGoldenPath.fieldAddCom_ok FieldEmitGoldenPath.allReg64_two V s hs
    (by intro stmt hm
        -- The emitted statement is an `add`, for which `ShiftAmtOK` is `True`; the
        -- register names (`lvlName`, a `toString`) are not reduced.
        simp [comToRegProg, comToReg, opToStmts, FieldEmitGoldenPath.fieldAddCom] at hm
        split at hm
        · rw [List.mem_singleton] at hm
          subst hm
          exact trivial
        · simp at hm)

end CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo
