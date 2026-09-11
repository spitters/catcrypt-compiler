/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
import all CatCrypt.Crypto.SecureCompilation.X86Backend.ComLegalityToGather

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ComLegalityToGather

/-!
# D4 (typed-`Com` step), completed: the supported-op set lowers under `lowerLinstrExt2`

The prior step (`ComLegalityToGather.lean`) reconciled the `:64` width tag and
proved the per-op `Com → gather` bridge for the **single** op whose export was
blocked *solely* by the tag — the materialised constant `regConst`. It surfaced,
honestly, the two further blockers for the rest of the legal set:

* **arity** — `regArith` / `mulhi` export *two* sources `[s0, s1]`, but the POC
  optimized lowering `LoweringExtended.lowerLinstrExt`'s ALU arm matches a single
  source; and
* **alphabet** — `mulhi` / `shrImm` / `shlImm` export the mnemonics `"MULXHI"` /
  `"SHR:<n>"` / `"SHL:<n>"`, none of which `lowerAluJ` covers.

This file completes the bridge for the **reduction-tractable** majority of the
legal set. `LoweringExtended.lean` now carries (added there purely additively —
the POC arms and their boolean mirror `linstrRSupported` are byte-identical) the
**supported-op superset** lowering `lowerLinstrExt2`, with the three new arms the
prior step named:

1. a width-tag strip before the ALU dispatch (so `"ADD:64"` / `"MOV:64"` reach
   `lowerAluJ`);
2. a **two-source** ALU arm (`op dst, [s0, s1] ↦ [mov dst s0; op dst s1]`) — the
   load-bearing change, without which no `regArith` export lowers; and
3. the `MULXHI` (high-word multiply) and `SHR:<n>` / `SHL:<n>` (immediate shift)
   arms.

`lowerLinstrExt2` is a strict superset of the POC `lowerLinstrExt`: it lowers the
constant-offset `LOAD` / `STORE` (`lowerLinstrExt2_load` / `lowerLinstrExt2_store`,
delegating to `lowerLinstrExt`) and every single-source bare-ALU shape
(`lowerLinstrExt2_single_isSome`), in addition to the new supported-op forms.

## What is bridged — and the honest residual

The per-op bridge `lowerLinstrExt2_isSome_*` is proved for the three families
whose export mnemonic is a **closed** string (so the `stripWidthTag` /
`lowerAluJ` dispatch reduces):

* `regArith bop 64` (the load-bearing two-source ALU) — `bop ∈ {add,…,xor}`;
* `mulhi 64` (the `"MULXHI:64"` high-word multiply); and
* `regConst 64 n` (the `"MOV:64"` materialised constant).

The two **immediate-shift** families `shrImm 64 n` / `shlImm 64 n` export the
mnemonic `withWidthTag 64 ("SHR:" ++ toString n)` — a string whose content
depends on the symbolic count `n`. Lean 4.29's `String` operations
(`splitOn` / `startsWith` / `endsWith`, all `Slice`/UTF-8-backed) do **not**
reduce over `_ ++ toString n` (there is no `String.toNat?`/`splitOn`-over-append
roundtrip lemma in the toolchain), so the `parseShiftMnem`-gated `isSome` of the
shift arm cannot be discharged by kernel reduction for a symbolic `n`. The shift
*arms are present* in `lowerLinstrExt2` (so the lowering table is complete — the
shift mnemonics no longer fall to `_ => none`); only the symbolic-`n` `isSome`
*proof* is out of reach at this layer. We therefore phrase the `Com`-wide gate
over the reduction-tractable sublattice `comAllSupportedRed` (a subset of the
canonical `comAllSupported`), exactly as the prior step phrased its gate over the
`regConst`-only `comAllCleanlyLowers`.

## The gather story (over the extended lowering)

`gatherJBlock` (`OptimizedComToElf.lean`) is the POC straight-line lowerer; it
folds `lowerLinstrExtL`, so it only ever lowers the POC fragment. Extending *it*
in place would change its emit/KAT bytes and break the proven mirror gate, so
this file defines the parallel `gatherJBlock2` over `lowerLinstrExt2L` and
re-proves the exact gate `blockSupported2_iff_gatherJBlock2_isSome` (a direct
instance of the prior file's `mapM_isSome_iff_all`).

## The `Lret` terminator (honest)

`comToBody` ends every exported body with the control-flow terminator `Lret`,
and `lowerLinstrExt2L .Lret = none` (the superset still does not lower control
flow — `gatherJBlock2` is a *straight-line* lowerer). So `gatherJBlock2` of a
*full* exported body is `none` regardless of op legality — exactly the terminator
blocker the prior step recorded. The `Com`-level result is therefore phrased as
the invariant *every emitted instruction lowers via `lowerLinstrExt2L` **or** is
the terminal `Lret`* (`comToBody_lower_or_ret`); the gather success is stated for
the straight-line image (the body with its `Lret` terminator dropped).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ComLegalityToGatherFull

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn (SupportedOp)
open CatCrypt.Crypto.SecureCompilation.Dialects
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfLegality
open CatCrypt.Crypto.SecureCompilation.X86Backend.ComLegalityToGather

/-! ## 1. `lowerLinstrExt2` is a strict superset of the POC `lowerLinstrExt` -/




/-- `lowerLinstrExt2` delegates the constant-offset `LOAD` arm to `lowerLinstrExt`
    verbatim (it is the first arm). -/
theorem lowerLinstrExt2_load (dst base : String) (off : Nat) :
    (lowerLinstrExt2 (.Lopn [.reg dst] "LOAD" [.arr base off])).isSome = true := by
  simp only [lowerLinstrExt2, lowerLinstrExt]; rfl

/-- **Superset witness (memory shapes).** `lowerLinstrExt2` lowers the
    constant-offset `STORE` the POC `lowerLinstrExt` lowered (the dedicated `STORE`
    arm — placed before the generic two-source ALU arm — delegates verbatim). -/
theorem lowerLinstrExt2_store (dst base : String) (off : Nat) (val : LOperand) :
    (lowerLinstrExt2 (.Lopn [.reg dst] "STORE" [.arr base off, val])).isSome = true := by
  simp only [lowerLinstrExt2, lowerLinstrExt]; rfl

/-- The single-source arm of `lowerLinstrExt2` lowers a non-`LOAD`, non-shift
    mnemonic whose tag-stripped form is in the `lowerAluJ` table. A single source
    `[src]` already rules out the two-source / `MULXHI` / `STORE` arms (they need a
    two-element source list); `hne` rules out the `LOAD` arm, so the matcher
    reaches the single-source ALU dispatch, which `halu` makes `some`. -/
theorem lowerLinstrExt2_single_isSome (dst opn : String) (src : LOperand)
    (hnar : ∀ b o, src ≠ .arr b o)
    (hsh : parseShiftMnem opn = none)
    (halu : isAluMnemonic (stripWidthTag opn) = true) :
    (lowerLinstrExt2 (.Lopn [.reg dst] opn [src])).isSome = true := by
  obtain ⟨i, hi⟩ :=
    Option.isSome_iff_exists.mp ((isAluMnemonic_iff_isSome dst (stripWidthTag opn)
      (lowerJOperand src)).mp halu)
  -- A single non-`.arr` source rules out the LOAD/STORE/`MULXHI`/two-source arms
  -- (LOAD needs a `.arr` source; STORE/`MULXHI`/two-source need a two-element list),
  -- so the single-source ALU arm fires.
  cases src with
  | reg name => simp only [lowerLinstrExt2, hsh, hi]; rfl
  | imm v => simp only [lowerLinstrExt2, hsh, hi]; rfl
  | arrIdx b idx s => simp only [lowerLinstrExt2, hsh, hi]; rfl
  | arr b o => exact absurd rfl (hnar b o)

/-! ## 2. The per-op bridge for the reduction-tractable supported families

For each closed-mnemonic supported op we feed `opToLinstrR`'s actual export shape
(at the op's signature arity) into `lowerLinstrExt2`; each lowers by reduction. -/

/-- The two-source ALU arm lowers exactly when the tag-stripped mnemonic is in the
    `lowerAluJ` table. (`lowerAluJ2`'s `isSome` is the inner `lowerAluJ`'s, via
    `isAluMnemonic`.) -/
theorem lowerAluJ2_isSome (dst opn : String) (o0 o1 : Jasmin.JOperand)
    (h : isAluMnemonic (stripWidthTag opn) = true) :
    (lowerAluJ2 dst opn o0 o1).isSome = true := by
  simp only [lowerAluJ2, Option.isSome_map]
  exact (isAluMnemonic_iff_isSome dst (stripWidthTag opn) o1).mp h

/-- `regArith bop 64` (`bop` a supported binop) exports `op dst, [s0, s1]` — the
    two-source ALU shape — and lowers (the load-bearing arm). The export reduces
    (by `rfl`) to `lowerLinstrExt2`'s two-source arm `lowerAluJ2 dst "BOP:64" …`;
    the tag-stripped mnemonic `"BOP"` is in the `lowerAluJ` table. -/
theorem lowerLinstrExt2_isSome_regArith (bop : JasminBinOp) (dst : String)
    (s0 s1 : LOperand) (hbop : isSupportedBinOp bop = true) :
    (lowerLinstrExt2 (opToLinstrR (.regArith bop 64) dst [s0, s1])).isSome = true := by
  cases bop <;>
    first
      | exact lowerAluJ2_isSome dst _ _ _ (by decide +kernel)
      | exact absurd hbop (by decide)

/-- `mulhi 64` exports `MULXHI:64 dst, [s0, s1]` and lowers. -/
theorem lowerLinstrExt2_isSome_mulhi (dst : String) (s0 s1 : LOperand) :
    (lowerLinstrExt2 (opToLinstrR (.mulhi 64) dst [s0, s1])).isSome = true := by
  simp [opToLinstrR, withWidthTag, lowerLinstrExt2, lowerMulHiJ, lowerJOperand]

/-- `regConst 64 n` exports `MOV:64 dst, [#n]` (ignoring `srcs`) and lowers — the
    single-source `MOV:64` is not a shift (`parseShiftMnem = none`) and its
    tag-stripped mnemonic `"MOV"` is in the `lowerAluJ` table. -/
theorem lowerLinstrExt2_isSome_regConst (n : Nat) (dst : String)
    (srcs : List LOperand) :
    (lowerLinstrExt2 (opToLinstrR (.regConst 64 n) dst srcs)).isSome = true := by
  show (lowerLinstrExt2 (.Lopn [.reg dst] "MOV:64" [.imm n])).isSome = true
  exact lowerLinstrExt2_single_isSome dst "MOV:64" (.imm n) (by rintro b o ⟨⟩)
    (by decide +kernel) (by decide +kernel)

/-! ## 3. The reduction-tractable supported sublattice

`opSupportedRed` is the boolean predicate cutting the supported set down to the
three closed-mnemonic families (`regArith`/`mulhi`/`regConst` at width 64). It
refines the canonical legality mirror `isSupportedOp` (`isSupportedOp_of_opSupportedRed`),
hence the canonical `SupportedOp` set. -/

/-- The reduction-tractable supported ops: width-64 `regArith` (supported binop),
    `mulhi`, and `regConst`. (`shrImm`/`shlImm` are supported but their
    symbolic-`n` mnemonic blocks a reduction proof — see the module header.) -/
def opSupportedRed : JasminOp → Bool
  | .regArith bop 64 => isSupportedBinOp bop
  | .mulhi 64        => true
  | .regConst 64 _   => true
  | _                => false

/-- `opSupportedRed` refines the canonical boolean legality mirror. -/
theorem isSupportedOp_of_opSupportedRed (op : JasminOp)
    (h : opSupportedRed op = true) : isSupportedOp op = true := by
  unfold opSupportedRed at h
  split at h <;> simp_all [isSupportedOp]

/-- `opSupportedRed` refines the canonical `SupportedOp` legal set. -/
theorem supportedOp_of_opSupportedRed (op : JasminOp)
    (h : opSupportedRed op = true) : SupportedOp op := by
  rw [← isSupportedOp_iff]; exact isSupportedOp_of_opSupportedRed op h

/-! ## 4. The per-instruction bridge over the actual SSA export

For a reduction-tractable supported op `e.op`, the front's export
`opToLinstrR e.op dst (exprArgs … e)` lowers via `lowerLinstrExt2`. We split on
`e.op`'s constructor, pin its arity from the dialect signature by destructuring
the typed argument vector `e.args`, and feed the §2 per-op lemmas. -/

/-- `opToLinstrR` followed by `lowerLinstrExt2` lowers every reduction-tractable
    supported op, on its actual SSA export shape. We destructure the typed argument
    vector `e.args`: a supported `op` pins the dialect signature (`[reg w, reg w]`
    for the binary `regArith`/`mulhi`, `[]` for the nullary `regConst`), so
    `exprArgs` reduces to the exact arity each §2 lemma needs. -/
theorem lowerLinstrExt2_isSome_of_supportedRed
    {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (curDepth nArgs : Nat) (argNames : Nat → String) (imm : ImmSlotMap)
    (e : Expr jasminDialect Γ τ) (dst : String)
    (hsup : opSupportedRed e.op = true) :
    (lowerLinstrExt2 (opToLinstrR e.op dst (exprArgs curDepth nArgs argNames imm e))).isSome
      = true := by
  obtain ⟨op, hret, args⟩ := e
  simp only at hsup ⊢
  -- Case on `op`; on each supported family destructure `args` to its arity and
  -- feed the §2 per-op lemma; the residual closes `hsup : false = true`.
  match op, hret, args, hsup with
  | .regArith bop 64, hret, .cons a (.cons b .nil), hsup =>
      rw [show exprArgs curDepth nArgs argNames imm
            (⟨.regArith bop 64, hret, .cons a (.cons b .nil)⟩ : Expr jasminDialect Γ τ)
          = [resolveVar curDepth nArgs argNames imm a, resolveVar curDepth nArgs argNames imm b]
        from rfl]
      exact lowerLinstrExt2_isSome_regArith bop dst _ _ hsup
  | .mulhi 64, hret, .cons a (.cons b .nil), _ =>
      rw [show exprArgs curDepth nArgs argNames imm
            (⟨.mulhi 64, hret, .cons a (.cons b .nil)⟩ : Expr jasminDialect Γ τ)
          = [resolveVar curDepth nArgs argNames imm a, resolveVar curDepth nArgs argNames imm b]
        from rfl]
      exact lowerLinstrExt2_isSome_mulhi dst _ _
  | .regConst 64 n, _, _, _ =>
      exact lowerLinstrExt2_isSome_regConst n dst _

/-! ## 5. The straight-line gather over `lowerLinstrExt2`

`gatherJBlock2` is the parallel of `OptimizedComToElf.gatherJBlock`, folding the
supported-op superset `lowerLinstrExt2L`. Its `isSome` is gated, exactly, by
`blockSupported2` (every instruction lowers) — a direct instance of the prior
file's `mapM_isSome_iff_all`. -/

/-- Straight-line gather over the supported-op superset lowering. -/
def gatherJBlock2 (body : List Linstr) : Option (List (Jasmin.JInstr 64)) :=
  (body.mapM lowerLinstrExt2L).map List.flatten

/-- Block-wide legality for the superset lowering: every instruction lowers. -/
def blockSupported2 (body : List Linstr) : Bool :=
  body.all (fun i => (lowerLinstrExt2L i).isSome)

/-- **The gate.** `blockSupported2` decides, exactly, whether `gatherJBlock2`
    succeeds. -/
theorem blockSupported2_iff_gatherJBlock2_isSome (body : List Linstr) :
    blockSupported2 body = true ↔ (gatherJBlock2 body).isSome = true := by
  unfold blockSupported2 gatherJBlock2
  rw [Option.isSome_map, mapM_isSome_iff_all]

/-- Legality ⇒ the superset gather succeeds. -/
theorem gatherJBlock2_isSome_of_blockSupported2 (body : List Linstr)
    (h : blockSupported2 body = true) : (gatherJBlock2 body).isSome = true :=
  (blockSupported2_iff_gatherJBlock2_isSome body).mp h

/-! ## 6. Lifting to a typed-`Com`: the reduction-tractable legality walk

`comAllSupportedRed` is the `Com`-wide walk over `opSupportedRed` — the
reduction-tractable sublattice of the canonical `comAllSupported`. We prove it
refines `comAllSupported`, and that the front's straight-line export of such a
`Com` lowers up to the terminal `Lret`. -/

/-- The `Com`-wide reduction-tractable legality walk. The `ret` leaf binds no op. -/
def comAllSupportedRed : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body => opSupportedRed e.op && comAllSupportedRed body

/-- **Refinement into the canonical legal set.** A `comAllSupportedRed` `Com` is,
    in particular, `comAllSupported`. -/
theorem comAllSupported_of_comAllSupportedRed {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t)
    (h : comAllSupportedRed c = true) : comAllSupported c = true := by
  induction c with
  | ret v => rfl
  | var e body ih =>
    simp only [comAllSupportedRed, Bool.and_eq_true] at h
    simp only [comAllSupported_var, Bool.and_eq_true]
    exact ⟨isSupportedOp_of_opSupportedRed e.op h.1, ih h.2⟩

/-- Whether a `Linstr` is the control-flow terminator `Lret`. -/
def isLret (i : Linstr) : Bool := match i.li_i with | .Lret => true | _ => false

/-- **The Com-level legality invariant.** For a `comAllSupportedRed` `Com`, *every*
    instruction the front emits (`comToBody`) is either lowered by
    `lowerLinstrExt2L` or is the terminal `Lret`. The `Lret` disjunct is
    irreducible at this layer (`gatherJBlock2` is straight-line and
    `lowerLinstrExt2L .Lret = none`), so the terminator is a separate control-flow
    concern. Modulo it, the typed-`Com` legality decides that every emitted op
    lowers. -/
theorem comToBody_lower_or_ret (nArgs : Nat) (argNames : Nat → String)
    (imm : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : Com jasminDialect Γ t) →
    (depth : Nat) → comAllSupportedRed c = true →
    (comToBody nArgs argNames imm c depth).all
      (fun i => (lowerLinstrExt2L i).isSome || isLret i) = true
  | _, _, .ret _, _, _ => by
      simp [comToBody, isLret]
  | _, _, .var e body, depth, h => by
      simp only [comAllSupportedRed, Bool.and_eq_true] at h
      simp only [comToBody, List.all_cons, Bool.and_eq_true, Bool.or_eq_true]
      refine ⟨Or.inl ?_, ?_⟩
      · show (lowerLinstrExt2L _).isSome = true
        unfold lowerLinstrExt2L
        exact lowerLinstrExt2_isSome_of_supportedRed depth nArgs argNames imm e
          (regName depth) h.1
      · exact comToBody_lower_or_ret nArgs argNames imm body (depth + 1) h.2

/-- **Straight-line gather success.** If every instruction of a body lowers
    (`blockSupported2`) — the straight-line image of a `comAllSupportedRed` export,
    its `Lret` terminator dropped — then `gatherJBlock2` of it succeeds. Composing
    with `comToBody_lower_or_ret`: `comAllSupportedRed c` gates that the
    straight-line portion of `c`'s export lowers, hence gathers under the extended
    lowering. -/
theorem gatherJBlock2_isSome_of_straightLine (body : List Linstr)
    (h : body.all (fun i => (lowerLinstrExt2L i).isSome) = true) :
    (gatherJBlock2 body).isSome = true :=
  gatherJBlock2_isSome_of_blockSupported2 body h

end CatCrypt.Crypto.SecureCompilation.X86Backend.ComLegalityToGatherFull
