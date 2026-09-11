/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf
public import CatCrypt.Crypto.SecureCompilation.Dialects.ComLegality

/-!
# D4 (first step): the verified legality target for the `OptimizedComToElf` collapse

The MLIR dialect-alignment restructure's **D4** phase wants to collapse the
two-IR backend so the `OptimizedComToElf` bridge becomes THE canonical lowering,
with the implicit "`gatherJBlock` returns `none` on an uncovered instruction"
guard replaced by a **real partial-conversion legality target**: an *illegal* op
produces a diagnostic, not a silent drop.

This file is the first concrete D4 step. It makes the lowering's success
**provably gated by an explicit, decidable legality predicate** — so the collapse
can carry legality as a *precondition* (and, dually, an illegal op as a witnessed
failure to diagnose) rather than leaning on the implicit `none`-on-drop behaviour
of `OptimizedComToElf.gatherJBlock`.

## The connection point (why this is at the `Linstr` level — Option B)

`gatherJBlock` consumes a `List Linstr` and lowers each instruction through
`LoweringExtended.lowerLinstrExtL`. That fragment is keyed on **string
mnemonics** (`"ADD"/"SUB"/.../"MOV"` plus const-offset `"LOAD"/"STORE"`), i.e.
the linearised `LinstrR.Lopn` shape.

`Dialects.ComLegality`'s `comAllSupported` / `isSupportedOp` are the **typed-`Com`**
legality predicate of the *flattening front* (`ScalarLinDeBruijn.SupportedOp` over
`JasminOp`: `regArith`/`mulhi`/`shrImm`/`shlImm`/`regConst` at width 64). These
are a different IR and a different alphabet from `lowerLinstrExtL`'s. Crucially,
the `Com → List Linstr` exporter `JasminLprogExport.opToLinstrR` emits a
**width-tagged** mnemonic (`withWidthTag 64 "ADD" = "ADD:64"`) for the 64-bit ops,
whereas `lowerLinstrExtL` matches the **bare** `"ADD"`. So there is *no* direct
composition `comAllSupported c → gatherJBlock (export c) ≠ none`: the two legal
sets don't line up at the byte-mnemonic level, and `gatherJBlock` is fed by the
ABI exporter, not by the flattening front.

The honest, tractable first D4 step is therefore at the granularity `gatherJBlock`
actually inspects — the `Linstr` block. We:

1. define `linstrSupported : Linstr → Bool` (resp. `LinstrR`), an **explicit,
   decidable** mirror of "`lowerLinstrExtL` lowers this instruction", and prove
   `linstrSupported_iff_isSome : linstrSupported i = true ↔ (lowerLinstrExtL i).isSome`
   — the *per-op legality ⇔ lowerable* equivalence;
2. lift it block-wise to `blockSupported : List Linstr → Bool` and prove the
   headline gate
   `blockSupported_iff_gather_isSome :
      blockSupported body = true ↔ (gatherJBlock body).isSome`
   — i.e. **the explicit legality predicate decides whether the optimized lowering
   succeeds**, exactly: every instruction legal ⇔ the gather is `some`, and one
   illegal instruction ⇔ the gather is `none` (the would-be diagnostic point);
3. expose the two collapse-facing directions:
   `gather_isSome_of_blockSupported` (legality ⇒ no silent drop — the D4 target as
   a precondition) and `not_blockSupported_of_gather_none` (a dropped gather is
   *witnessed* by an explicit illegal instruction, the seam where a partial
   conversion raises a diagnostic instead of returning `none`).

## The gap to a typed-`Com` gate (honest)

The full chain `comAllSupported c = true → (gatherJBlock (exported-body c)).isSome`
is **not** closed here, because the two legal sets differ as described above
(width tag; flattening-front alphabet vs. linear-export mnemonics; and the
const-offset `LOAD`/`STORE` arms of `lowerLinstrExtL` have *no* `JasminOp`
counterpart in `SupportedOp`). Bridging them needs an exporter-level lemma
`opToLinstrR (supported op) ⇒ linstrSupported`, which in turn needs the
mnemonic tables (`binOpName` + `withWidthTag`) reconciled with `lowerAluJ`'s table
(notably the `:64` tag). That reconciliation — making `lowerLinstrExtL` accept the
width-tagged mnemonics the ABI exporter emits, or routing the optimized path
through the flattening front instead of the ABI exporter — is the *next* D4 step;
it is flagged in the report, not silently assumed.

What IS delivered: the implicit `none`-on-illegal guard of `gatherJBlock` is now
**an explicit, proven, decidable predicate** (`blockSupported`) that gates success
exactly, with both collapse-facing directions proved.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfLegality

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf

/-! ## 1. An explicit, decidable legality predicate for the `lowerLinstrExtL` fragment

`linstrRSupported` is the boolean mirror of "`lowerLinstrExt` lowers this
`LinstrR`": the const-offset `LOAD`/`STORE` arms and the nine-mnemonic ALU/`MOV`
table (`lowerAluJ`). It is decidable and total — the **explicit** form of the
coverage guard `lowerLinstrExt` realises implicitly via its `_ => none` arm. -/

/-- The ALU/`MOV` mnemonics `lowerAluJ` covers — the boolean mirror of its
    `some`-returning arms. -/
def isAluMnemonic (opn : String) : Bool :=
  opn == "ADD" || opn == "SUB" || opn == "MUL" || opn == "AND"
    || opn == "OR" || opn == "XOR" || opn == "SHL" || opn == "SHR" || opn == "MOV"

/-- `lowerAluJ` returns `some` exactly on the nine ALU/`MOV` mnemonics. -/
theorem isAluMnemonic_iff_isSome (dst opn : String) (s : JOperand) :
    isAluMnemonic opn = true ↔ (lowerAluJ dst opn s).isSome = true := by
  constructor
  · intro h
    simp only [isAluMnemonic, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (((((((h|h)|h)|h)|h)|h)|h)|h)|h <;> subst h <;> rfl
  · intro h
    -- a non-ALU mnemonic makes `lowerAluJ` `none`, contradicting `isSome`
    by_contra hcon
    unfold lowerAluJ at h
    split at h <;> simp_all [isAluMnemonic]

/-- `Bool`-level form of `isAluMnemonic_iff_isSome`: the two booleans agree. The
    `simp`-friendly closer for the ALU arm of `linstrRSupported_iff_isSome`. -/
theorem isAluMnemonic_eq_isSome (dst opn : String) (s : JOperand) :
    isAluMnemonic opn = (lowerAluJ dst opn s).isSome := by
  rw [Bool.eq_iff_iff, isAluMnemonic_iff_isSome]

/-- The decidable legality predicate for a `LinstrR`: `true` iff `lowerLinstrExt`
    lowers it. Mirrors `lowerLinstrExt`'s pattern match: the const-offset
    `LOAD`/`STORE` arms (always lower) and the ALU/`MOV` arm (`isAluMnemonic`). -/
def linstrRSupported : LinstrR → Bool
  | .Lopn [.reg _] "LOAD" [.arr _ _] => true
  | .Lopn [.reg _] "STORE" [.arr _ _, _] => true
  | .Lopn [.reg _] opn [_] => isAluMnemonic opn
  | _ => false

/-- Legality of a full `Linstr` (drops the position tag), mirroring
    `lowerLinstrExtL`. -/
def linstrSupported (i : Linstr) : Bool := linstrRSupported i.li_i

/-! ## 2. Per-op legality ⇔ lowerable (the explicit gate, one instruction)

`linstrRSupported` decides `(lowerLinstrExt ·).isSome` exactly. This is the
explicit, proven realisation of the "`lowerLinstrExt` returns `none` on every
shape outside its coverage" guard. -/

/-- **Per-`LinstrR` legality gate.** `linstrRSupported i = true` iff
    `lowerLinstrExt i` lowers (`isSome`). The const-offset `LOAD`/`STORE` arms and
    each ALU/`MOV` mnemonic lower; everything else is `none`. -/
theorem linstrRSupported_iff_isSome (i : LinstrR) :
    linstrRSupported i = true ↔ (lowerLinstrExt i).isSome = true := by
  -- Case-split along `lowerLinstrExt`'s own pattern arms. The LOAD/STORE arms make
  -- both sides `true`; the ALU arm reduces to `isAluMnemonic_eq_isSome`; the
  -- fallthrough makes both sides `false`. `fun_cases` keeps the two matches in
  -- lockstep, avoiding the contradictory cross-product `split` would produce.
  fun_cases lowerLinstrExt i <;>
    simp_all [linstrRSupported, Option.isSome_map]
  -- the single residual is the ALU arm: `isAluMnemonic opn = (lowerAluJ ..).isSome`
  exact isAluMnemonic_eq_isSome _ _ _

/-- **Per-`Linstr` legality gate.** `linstrSupported i = true` iff
    `lowerLinstrExtL i` lowers (`isSome`). -/
theorem linstrSupported_iff_isSome (i : Linstr) :
    linstrSupported i = true ↔ (lowerLinstrExtL i).isSome = true :=
  linstrRSupported_iff_isSome i.li_i

/-! ## 3. The block-wide gate: legality ⇔ `gatherJBlock` succeeds

Lifting the per-instruction gate over the body via `List.mapM`: every
instruction legal ⇔ the whole gather is `some`. This is the headline D4 target —
the implicit `none`-on-illegal guard of `gatherJBlock` is now an EXPLICIT, proven,
decidable predicate that gates success exactly. -/

/-- The block-wide legality predicate: every instruction of the body is in the
    `lowerLinstrExtL` fragment. -/
def blockSupported (body : List Linstr) : Bool := body.all linstrSupported

/-- The `mapM`-over-`Option` lifting: a `List.mapM f` is `some` iff every element
    maps to `some`. Proved by structural induction (no mathlib lemma fits the
    `Option` monad shape directly). -/
theorem mapM_isSome_iff_all {α β : Type} (f : α → Option β) (l : List α) :
    (l.mapM f).isSome = true ↔ l.all (fun a => (f a).isSome) = true := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.mapM_cons]
    cases hfa : f a with
    | none => simp [hfa]
    | some b =>
      cases has : as.mapM f with
      | none =>
        have : ¬ (as.mapM f).isSome = true := by simp [has]
        rw [ih] at this
        simp_all
      | some bs => simp_all

/-- **The D4 legality target (block-wide).** The explicit, decidable legality
    predicate `blockSupported` decides whether the optimized lowering's gather
    succeeds, EXACTLY: every instruction legal ⇔ `gatherJBlock body` is `some`.
    This replaces the implicit "`gatherJBlock` returns `none` on an uncovered op"
    with a proven predicate gating success. -/
theorem blockSupported_iff_gather_isSome (body : List Linstr) :
    blockSupported body = true ↔ (gatherJBlock body).isSome = true := by
  unfold blockSupported gatherJBlock
  rw [Option.isSome_map, mapM_isSome_iff_all]
  -- Both sides are `body.all _`; they agree pointwise by the per-instruction gate.
  rw [show (body.all linstrSupported)
        = (body.all (fun a => (lowerLinstrExtL a).isSome)) from
      List.all_congr rfl (fun i => by rw [Bool.eq_iff_iff, linstrSupported_iff_isSome])]

/-! ## 4. The two collapse-facing directions

`gather_isSome_of_blockSupported` is the D4 target as a **precondition**: legality
⇒ no silent drop. `not_blockSupported_of_gather_none` is its contrapositive: a
dropped gather is **witnessed** by an explicit illegal instruction — the seam
where a partial conversion raises a diagnostic instead of silently returning
`none`. -/

/-- **Legality ⇒ no silent drop.** If every instruction is legal, the optimized
    lowering's gather succeeds. The D4 collapse can carry `blockSupported body`
    as a precondition rather than relying on the implicit `none`-on-drop. -/
theorem gather_isSome_of_blockSupported (body : List Linstr)
    (h : blockSupported body = true) : (gatherJBlock body).isSome = true :=
  (blockSupported_iff_gather_isSome body).mp h

/-- The optimized block also succeeds when the body is legal (the pipeline is
    total over `gatherJBlock`'s output). -/
theorem optimizedJBlock_isSome_of_blockSupported (body : List Linstr)
    (h : blockSupported body = true) : (optimizedJBlock body).isSome = true := by
  unfold optimizedJBlock
  rw [Option.isSome_map]
  exact gather_isSome_of_blockSupported body h

/-- **A dropped gather is witnessed.** If the gather returns `none`, the body is
    NOT block-legal — i.e. there is (at least) one illegal instruction. This is
    the diagnostic seam: instead of a silent `none`, the partial conversion has an
    explicit, decidable witness of *why* the lowering is rejected. -/
theorem not_blockSupported_of_gather_none (body : List Linstr)
    (h : gatherJBlock body = none) : blockSupported body = false := by
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  have := gather_isSome_of_blockSupported body hcon
  rw [h] at this
  simp at this

/-! ## 5. The demo body is block-legal (consistency with `OptimizedComToElf`)

`OptimizedComToElf.demoBody` is the worked straight-line LOAD/ADD/MOV/STORE body
that `gatherJBlock` lowers. Its `blockSupported` predicate is `true`, and the gate
recovers `gatherJBlock`'s success on it — the explicit predicate agrees with the
existing `demoBody_gather` fact. -/

/-- The demo body passes the explicit legality predicate. -/
theorem demoBody_blockSupported : blockSupported demoBody = true := rfl

/-- The legality gate recovers `gatherJBlock`'s success on the demo body. -/
theorem demoBody_gather_isSome_via_legality :
    (gatherJBlock demoBody).isSome = true :=
  gather_isSome_of_blockSupported demoBody demoBody_blockSupported

end CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfLegality
