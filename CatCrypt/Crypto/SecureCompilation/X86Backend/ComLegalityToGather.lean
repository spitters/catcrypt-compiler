/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfLegality
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.Dialects.ComLegality

/-!
# D4 (typed-`Com` step): bridging `ComLegality` to `gatherJBlock` success

This file is the **typed-`Com → gather`** step of the MLIR dialect-alignment
restructure's **D4** phase. The prior step (`OptimizedComToElfLegality.lean`)
turned the implicit "`gatherJBlock` returns `none` on an uncovered op" guard
into an *explicit, decidable* `Linstr`-level predicate `blockSupported`, with the
headline gate `blockSupported_iff_gather_isSome`. It flagged the remaining gap:
bridging the typed-`Com` legality predicate `Dialects.ComLegality.comAllSupported`
/ `ComSupported` to that `Linstr` gate needs the exporter-level reconciliation of
the mnemonic table, blocked by the `:64` width tag.

This file does that reconciliation as far as the definitions allow, and reports
honestly where the definitions block the rest.

## The reconciliation: a tag-stripping normalization

`JasminLprogExport.opToLinstrR` emits **width-tagged** mnemonics for 64-bit ops
(`withWidthTag 64 "ADD" = "ADD:64"`, `... "MOV" = "MOV:64"`), whereas
`LoweringExtended.lowerAluJ` matches the **bare** `"ADD"/.../"MOV"`. We define
`normLinstrR` — the obvious tag-stripping normalization (apply `stripWidthTag` to
the `Lopn` mnemonic, via the exporter's own `stripWidthTag`) — and `normBody`
lifting it over a block. Composing with the prior file's
`blockSupported_iff_gather_isSome`, the success of the optimized lowering over a
*normalized* export is gated, exactly, by `blockSupported` of the normalized
block (`normBody_blockSupported_gate`). This is the seam at which the tag
reconciliation plugs in: `gatherJBlock` consumes the normalized (bare-mnemonic)
block.

## What the tag-strip closes — and what it does NOT (honest)

Stripping `:64` is necessary but, per the actual definitions, **not sufficient**
for the whole supported set. Probing each `isSupportedOp` op's *actual* export
(`opToLinstrR op dst srcs`) against `lowerLinstrExt` after normalization:

| supported op | normalized export | lowers? | residual blocker |
|---|---|---|---|
| `regConst 64 n` | `Lopn [reg dst] "MOV" [imm n]` | **yes** | none — the tag was the only blocker |
| `regArith bop 64` | `Lopn [reg dst] BOP [s0,s1]` | no | **arity**: 2 sources; `lowerLinstrExt`'s ALU arm matches a *single* source `[src]` (the two-address `op dst, src` form), the SSA exporter emits both sources explicitly |
| `mulhi 64` | `Lopn [reg dst] "MULXHI" [s0,s1]` | no | **arity + alphabet**: 2 sources *and* `"MULXHI"` has no `lowerAluJ` arm |
| `shrImm 64 n` | `Lopn [reg dst] ("SHR:"++n) [src]` | no | **alphabet**: `"SHR:<n>"` has no `lowerAluJ` arm (bare `"SHR"` exists, but the immediate-shift export carries the count in the mnemonic) |
| `shlImm 64 n` | `Lopn [reg dst] ("SHL:"++n) [src]` | no | **alphabet**: `"SHL:<n>"` has no `lowerAluJ` arm |

So the clean, tag-only-blocked subset of the legal set is exactly the
**materialised-constant** op `regConst` (`opCleanlyLowers`). For it we prove the
per-op bridge `opCleanlyLowers op → linstrRSupported (normLinstrR (opToLinstrR op
…))` (`linstrRSupported_normLinstrR_export`), and that it refines the canonical
`ComLegality` set (`supportedOp_of_opCleanlyLowers`,
`comAllSupported_of_comAllCleanlyLowers`).

The prior step's docstring named only the `:64` tag and the
`mulhi`/`shrImm`/`shlImm` alphabet. This file additionally surfaces two further
findings:

* the **arity** blocker for the dominant `regArith` ALU ops — independent of the
  tag, so no tag reconciliation *alone* reaches the ALU fragment; and
* the **terminator** blocker: `comToBody` ends every exported body with an
  `Lret`, and `lowerLinstrExtL .Lret = none`, so `gatherJBlock` of a *full*
  exported body is `none` regardless of op legality. `gatherJBlock` is a
  straight-line lowerer; the control-flow terminator is a separate concern. The
  Com-level result here is therefore phrased as the invariant *every emitted
  instruction is either normalized-legal or the terminal `Lret`*
  (`comToBody_legal_or_ret`).

## The exact live-file changes needed for the full `ComSupported → gather` result

This file touches no existing file. To extend the bridge to the whole legal set,
the **optimized lowering's mnemonic table** (`LoweringExtended.lowerLinstrExt` /
`lowerAluJ`) — or, equivalently, the exporter on the optimized path — would need:

1. **Accept the `:64`-tagged mnemonics.** In `lowerLinstrExt`, strip the width
   tag before the ALU dispatch (`lowerAluJ dst (stripWidthTag opn) …`), or add
   tagged aliases. (`normLinstrR` here realises the strip externally instead.)
2. **A two-source ALU arm.** Add `| .Lopn [.reg dst] opn [s0, s1] => …` mapping
   to the two-address `op dst, s1` (with `dst := s0` already established by the
   regalloc/SSA convention), so the explicit-two-source SSA export of `regArith`
   lowers. This is the load-bearing change: without it no `regArith` export
   lowers, tag or no tag.
3. **`SHR:<n>` / `SHL:<n>` / `MULXHI` arms** in `lowerAluJ` (the immediate-shift
   and widening-high-multiply mnemonics the exporter emits), to cover
   `shrImm`/`shlImm`/`mulhi`.

With (1)–(3) in place, the per-op bridge generalises from `regConst` to every
`isSupportedOp` op, and `comAllSupported c = true → (gatherJBlock (normalized
straight-line export of c)).isSome = true` closes for the whole legal set. Until
then, the verified gate holds for the constant subset and for any
externally-normalized block via `normBody_blockSupported_gate` below.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ComLegalityToGather

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn (SupportedOp)
open CatCrypt.Crypto.SecureCompilation.Dialects
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfLegality

/-! ## 1. The tag-stripping normalization

`normLinstrR` strips the `":64"` width tag from an `Lopn` mnemonic (via the
exporter's own `stripWidthTag`), reconciling the width-tagged mnemonics the ABI
exporter emits with the bare mnemonics `lowerAluJ` matches. Non-`Lopn`
constructors are left untouched. -/

/-- Tag-strip the mnemonic of an `Lopn` (identity on other constructors). -/
def normLinstrR : LinstrR → LinstrR
  | .Lopn dsts opn srcs => .Lopn dsts (stripWidthTag opn) srcs
  | i => i

/-- Tag-strip a full `Linstr` (preserving its position tag). -/
def normLinstr (i : Linstr) : Linstr := ⟨i.li_ii, normLinstrR i.li_i⟩

/-- Tag-strip every instruction of a block. -/
def normBody (body : List Linstr) : List Linstr := body.map normLinstr

@[simp] theorem normLinstr_li_i (i : Linstr) :
    (normLinstr i).li_i = normLinstrR i.li_i := rfl

/-! ## 2. The normalized-block gate (composition with the prior step)

For *any* block, the optimized lowering's gather over the **normalized** block is
gated, exactly, by `blockSupported` of the normalized block — a direct instance
of the prior file's `blockSupported_iff_gather_isSome`. -/

/-- **Normalized-block legality gate.** `blockSupported (normBody body)` decides,
    exactly, whether `gatherJBlock` succeeds on the normalized block. -/
theorem normBody_blockSupported_gate (body : List Linstr) :
    blockSupported (normBody body) = true ↔ (gatherJBlock (normBody body)).isSome = true :=
  blockSupported_iff_gather_isSome (normBody body)

/-- Legality of the normalized block ⇒ the optimized gather succeeds on it. -/
theorem gather_isSome_of_normBody_blockSupported (body : List Linstr)
    (h : blockSupported (normBody body) = true) :
    (gatherJBlock (normBody body)).isSome = true :=
  (normBody_blockSupported_gate body).mp h

/-! ## 3. The clean tag-only subset of the legal set: `regConst`

`opToLinstrR (regConst w n) dst srcs = Lopn [reg dst] (withWidthTag w "MOV")
[imm n]` — a *single-source* immediate MOV, regardless of `srcs`. After
tag-stripping at `w = 64`, the mnemonic is the bare `"MOV"`, which `lowerAluJ`
covers. So the materialised-constant op is the (only) op whose actual export is
blocked solely by the `:64` tag. -/

/-- The clean subset predicate: supported ops whose *normalized* export lowers
    via `lowerLinstrExt`. By the table in the module header this is exactly the
    width-64 materialised constants. -/
def opCleanlyLowers : JasminOp → Bool
  | .regConst 64 _ => true
  | _ => false

/-- `stripWidthTag` removes the `:64` tag from the materialised-constant
    mnemonic, recovering the bare `"MOV"` `lowerAluJ` covers. (`decide +kernel`
    forces the `String.endsWith` / `String.ofList` reduction the default kernel
    `rfl` stalls on.) -/
theorem stripWidthTag_MOV : stripWidthTag ("MOV" ++ ":64") = "MOV" := by decide +kernel

/-- `opCleanlyLowers` refines the boolean legality mirror: every cleanly-lowering
    op passes `isSupportedOp` (it is a `regConst 64 _`). -/
theorem isSupportedOp_of_opCleanlyLowers (op : JasminOp)
    (h : opCleanlyLowers op = true) : isSupportedOp op = true := by
  unfold opCleanlyLowers at h
  split at h
  · rfl
  all_goals simp at h

/-- `opCleanlyLowers` refines the canonical legal set: every cleanly-lowering op
    is `SupportedOp`. -/
theorem supportedOp_of_opCleanlyLowers (op : JasminOp)
    (h : opCleanlyLowers op = true) : SupportedOp op := by
  rw [← isSupportedOp_iff]; exact isSupportedOp_of_opCleanlyLowers op h

/-- **The per-op clean bridge.** For a cleanly-lowering supported op (a width-64
    materialised constant), the *normalized* export is in the `lowerLinstrExt`
    fragment — i.e. it lowers. The `:64` tag was the only blocker, and
    `normLinstrR` removes it. -/
theorem linstrRSupported_normLinstrR_export (op : JasminOp) (dst : String)
    (srcs : List LOperand) (h : opCleanlyLowers op = true) :
    linstrRSupported (normLinstrR (opToLinstrR op dst srcs)) = true := by
  unfold opCleanlyLowers at h
  split at h
  · -- op = `regConst 64 n`: export is `Lopn [reg dst] "MOV:64" [imm n]`.
    simp only [opToLinstrR, withWidthTag, if_pos, normLinstrR, stripWidthTag_MOV]
    -- The single `.imm` source rules out the LOAD/STORE arms; `split` resolves
    -- the mnemonic match (`"MOV"` vs `"LOAD"`/`"STORE"`), then `isAluMnemonic`.
    unfold linstrRSupported
    split <;> simp_all [isAluMnemonic]
  all_goals simp at h

/-! ## 4. Lifting to a typed-`Com`: the clean-subset legality walk

`comAllCleanlyLowers` is the `Com`-wide walk over `opCleanlyLowers` — the clean,
tag-only-blocked sublattice of the canonical `comAllSupported`. We prove (a) it
refines `comAllSupported` (so it is genuinely a subset of the canonical legal
set), and (b) the front's straight-line export of such a `Com` is normalized-legal
*up to the terminal `Lret`*. -/

/-- The `Com`-wide clean-subset legality walk: every let-bound op cleanly lowers
    (i.e. is a width-64 materialised constant). The `ret` leaf binds no op. -/
def comAllCleanlyLowers : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body => opCleanlyLowers e.op && comAllCleanlyLowers body

/-- **Refinement into the canonical legal set.** A cleanly-lowering `Com` is, in
    particular, `comAllSupported` — i.e. `comAllCleanlyLowers` is a subset of the
    canonical `ComLegality` predicate. -/
theorem comAllSupported_of_comAllCleanlyLowers {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t)
    (h : comAllCleanlyLowers c = true) : comAllSupported c = true := by
  induction c with
  | ret v => rfl
  | var e body ih =>
    simp only [comAllCleanlyLowers, Bool.and_eq_true] at h
    simp only [comAllSupported_var, Bool.and_eq_true]
    exact ⟨isSupportedOp_of_opCleanlyLowers e.op h.1, ih h.2⟩

/-- Whether a `Linstr` is the control-flow terminator `Lret`. -/
def isLret (i : Linstr) : Bool := match i.li_i with | .Lret => true | _ => false

/-- **The Com-level legality invariant.** For a cleanly-lowering `Com`, *every*
    instruction the front emits (`comToBody`) is either normalized-legal (lowers
    via `lowerLinstrExtL`) or the terminal `Lret`. The `Lret` disjunct is
    irreducible at this layer: `gatherJBlock` is a straight-line lowerer and
    `lowerLinstrExtL .Lret = none` independently of legality, so the terminator
    is a separate (control-flow) concern — see the module header. Modulo it, the
    typed-`Com` clean-subset legality decides that every emitted op lowers. -/
theorem comToBody_legal_or_ret (nArgs : Nat) (argNames : Nat → String)
    (imm : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : Com jasminDialect Γ t) →
    (depth : Nat) → comAllCleanlyLowers c = true →
    (comToBody nArgs argNames imm c depth).all
      (fun i => linstrSupported (normLinstr i) || isLret i) = true
  | _, _, .ret _, _, _ => by
      simp [comToBody, isLret]
  | _, _, .var e body, depth, h => by
      simp only [comAllCleanlyLowers, Bool.and_eq_true] at h
      simp only [comToBody, List.all_cons, Bool.and_eq_true, Bool.or_eq_true]
      refine ⟨Or.inl ?_, ?_⟩
      · show linstrSupported (normLinstr _) = true
        unfold linstrSupported normLinstr
        exact linstrRSupported_normLinstrR_export e.op (regName depth) _ h.1
      · exact comToBody_legal_or_ret nArgs argNames imm body (depth + 1) h.2

end CatCrypt.Crypto.SecureCompilation.X86Backend.ComLegalityToGather
