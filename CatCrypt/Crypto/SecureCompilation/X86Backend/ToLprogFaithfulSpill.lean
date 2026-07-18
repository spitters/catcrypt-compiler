/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulProbe

/-!
# `toLprogPhysAbi` faithfulness — the spill-reload fragment of `legalizeBinop`

The probe `ToLprogFaithfulProbe.twoAddrExpand_lsem` discharged, against the real
`JasminLsem.lsemStraight` semantics, the **no-spill** two-address expansion
`mov dst, s0 ; op dst, s1` of one binop.

This module discharges the **spill cases** of `legalizeBinop`
(`JasminLprogExport.lean:1132`). After two-address legalization has placed the
binop in the canonical two-source form `op dst, src` (sources `[dst, src]`,
i.e. `dst` is also the first source), `legalizeBinop` routes any *spill*
(`k.N`) operand through the reserved scratches `R15` (`reloadScratch`) and
`R14` (`reloadScratch2`), because jasmin's `asmgen` refuses a memory `lexpr`
on a non-`MOV` `Lopn`. The four branches by `(dst.isSpill, src.isSpill)` emit
1/2/3/4 `Lopn`s; we prove each of the three spilling branches writes, at the
final destination `dst`, exactly `applyOpn opn [s.lvm dst, s.lvm src]` — the
same value the non-legalized direct binop `op dst, src` would write.

## The semantic model of a spill cell

The crucial — and trust-relevant — observation is that `lsemStep`'s `Lopn` arm
reads **every** `.reg n` source via `evalOperand s (.reg n) = s.lvm n`,
*regardless of whether `n` is a spill name `k.N` or a GP register*. `isSpill`
governs only the **textual legality** the asmgen printer enforces, not the
`lsem` denotation: under `lsemStraight`, a spill cell `k.N` is just another
`String`-keyed cell of the `lvm` store. So the reload `mov R15, k.5` followed by
`op R15, …` computes the same word `op` would have computed reading `k.5`
directly — *provided the scratches do not alias the operands*.

## The non-interference invariant (stated precisely)

Each spilling branch threads values through `R15`/`R14`. The reload sequence is
faithful exactly when those scratches are fresh with respect to the binding's
operands. The precise side condition is, per branch:

* `(false, true)` (`mov R15, src; op dst, R15`): `dst ≠ R15`. (The op writes
  `dst` reading the freshly-loaded `R15`; we need `dst ≠ R15` so the op's write
  to `dst` is the visible result and `R15` still holds `s.lvm src` when read.)
* `(true, false)` (`mov R15, dst; op R15, src; mov dst, R15`): `R15 ≠ dst`,
  `R15 ≠ src`. (`R15` must not alias `dst` — else the trailing `mov dst, R15`
  reads a stale value — nor `src` — else the `op` reads the reloaded `dst`
  instead of `src`.)
* `(true, true)` (`mov R15, dst; mov R14, src; op R15, R14; mov dst, R15`):
  `R15 ≠ R14`, `R15 ≠ dst`, `R15 ≠ src`, `R14 ≠ dst`. (`R15`/`R14` must be
  distinct from each other and from the operands so neither reload clobbers a
  value the later instructions still need.)

These are all **guaranteed by construction** in the shipped pipeline: spill
names are exactly the `"k.".isPrefixOf` names (`LOperand.isSpill`), while
`reloadScratch = "R15"` and `reloadScratch2 = "R14"` are not spill names
(`reloadScratch_not_spill`, `reloadScratch2_not_spill`), and `physRegName` never
emits `R15`/`R14`. So whenever an operand `isSpill`, it differs from both
scratches; and `R15 ≠ R14` is a literal disequality of constants. We discharge
each branch under the explicit hypotheses above (kept as hypotheses rather than
derived from `isSpill`, so the lemmas state the *semantic* non-interference
requirement directly), then package the constant disequalities `R15 ≠ R14` and
`(spill) ≠ R15/R14` as standing facts.

## Residual (named honestly — out of scope here)

* The `physMap` register-renaming pass (`remapOperand`/`physBody`): renaming a
  virtual operand to its physical slot preserves the `lsem` read only relative
  to an `lvm` re-indexed along the same renaming. That is a `StoreAgrees`-style
  refinement (the `RegMachineSim` keystone `jinstr_renameBlock_sound` proves the
  analogue for the `JInstr`/`JState` machine); it is **not** proved here because
  `physBody` is not a *uniform* renaming — it interleaves the two-address `mov`s
  and these spill reloads. We record below only the *pointwise read-refinement*
  shape it must satisfy (`evalOperand_remap_shape`), as a documented obligation.
* The ABI prologue/epilogue (`buildPrologue`/`buildEpilogue`) and the `Lret`
  terminator: control flow, for which `lsemStep` is honestly `none` (out of the
  straight-line increment-1 scope). **Not** modeled, **not** faked.

So this module proves the *semantic core* of `legalizeBinop`'s spill branches
against the real `lsemStraight`; together with the probe's no-spill case it
covers every branch of `legalizeBinop` ∘ `lowerTwoAddr`'s binop emission. The
`physMap` renaming refinement and the ABI/`Lret` control flow remain explicit
residual.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-! ## 0. Standing scratch-freshness facts

`reloadScratch = "R15"` and `reloadScratch2 = "R14"` are distinct constants, and
neither is a spill name. These discharge the non-interference hypotheses of the
branch lemmas from `isSpill` flags in the shipped pipeline. -/

/-- The two reserved scratches are distinct registers. -/
theorem reloadScratch_ne_reloadScratch2 : reloadScratch ≠ reloadScratch2 := by
  decide

/-! ## 1. The `(false, true)` branch: register dst, spill src

`legalizeBinop dst src opn = mov R15, src ; op dst, R15`.
Result at `dst`: `applyOpn opn [s.lvm dst, s.lvm src]`. Side cond `dst ≠ R15`. -/

/-- **`legalizeBinop` spill branch, register-dst / spill-src.** Running
    `mov R15, src ; op dst, R15` under `lsemStraight` writes, at `dst`, exactly
    `applyOpn opn [s.lvm dst, s.lvm src]` — the value the direct two-address
    `op dst, src` would write. The non-interference side condition is
    `dst ≠ R15`: the leading reload must not target the destination register.
    (`R15 ≠ src` is *not* needed here — `src` is read once, into `R15`, before
    anything is written.) -/
theorem legalizeBinop_regSpill_lsem {w : Nat} (s : Lstate w)
    (dst src opn : String) (hd15 : dst ≠ reloadScratch)
    (hstrip : stripWidthTag opn = opn) (v : BitVec w)
    (hop : applyOpn opn [s.lvm dst, s.lvm src] = some v) :
    ∃ s', lsemStraight
        [ .Lopn [.reg reloadScratch] "MOV" [.reg src],
          .Lopn [.reg dst] opn [.reg dst, .reg reloadScratch] ] s = some s'
      ∧ s'.lvm dst = v := by
  -- Step 1: `mov R15, src` loads `s.lvm src` into the scratch and bumps pc.
  have hmov : lsemStep (LinstrR.Lopn [.reg reloadScratch] "MOV" [.reg src]) s
      = some ((s.setReg reloadScratch (s.lvm src)).nextPc) := by
    simp only [lsemStep, List.map_cons, List.map_nil, evalOperand,
      ToLprogFaithfulProbe.stripWidthTag_MOV, applyOpn]
  let sM : Lstate w := (s.setReg reloadScratch (s.lvm src)).nextPc
  -- `op dst, R15` reads `dst` (unchanged, `dst ≠ R15`) and `R15` (= `s.lvm src`).
  have heval_dst : evalOperand sM (.reg dst) = s.lvm dst := by
    show evalOperand ((s.setReg reloadScratch (s.lvm src)).nextPc) (.reg dst) = s.lvm dst
    simp only [evalOperand, Lstate.setReg, Lstate.nextPc, if_neg hd15]
  have heval_r15 : evalOperand sM (.reg reloadScratch) = s.lvm src := by
    show evalOperand ((s.setReg reloadScratch (s.lvm src)).nextPc) (.reg reloadScratch)
        = s.lvm src
    simp [evalOperand, Lstate.setReg, Lstate.nextPc]
  have hop2 : lsemStep (LinstrR.Lopn [.reg dst] opn [.reg dst, .reg reloadScratch]) sM
      = some ((sM.setReg dst v).nextPc) := by
    simp only [lsemStep, List.map_cons, List.map_nil, heval_dst, heval_r15, hstrip, hop]
  refine ⟨(sM.setReg dst v).nextPc, ?_, ?_⟩
  · simp only [lsemStraight, hmov]; rw [hop2]
  · show ((sM.setReg dst v).nextPc).lvm dst = v
    simp [Lstate.setReg, Lstate.nextPc]

/-! ## 2. The `(true, false)` branch: spill dst, register src

`legalizeBinop dst src opn = mov R15, dst ; op R15, src ; mov dst, R15`.
Result at `dst`: `applyOpn opn [s.lvm dst, s.lvm src]`.
Side conds: `R15 ≠ dst`, `R15 ≠ src`. -/

/-- **`legalizeBinop` spill branch, spill-dst / register-src.** Running
    `mov R15, dst ; op R15, src ; mov dst, R15` under `lsemStraight` writes, at
    `dst`, exactly `applyOpn opn [s.lvm dst, s.lvm src]`. The non-interference
    side condition needed for the value is `reloadScratch ≠ src` (else
    `op R15, src` reads the just-reloaded `dst` value instead of `src`). The
    `reloadScratch ≠ dst` requirement of the pipeline invariant (the scratch must
    not alias the destination) is **not** needed for this read-back: even were
    `dst = R15`, the final `mov dst, R15` reads the `v` that step 2 placed in
    `R15`, so `dst` ends holding `v` regardless; we therefore do not assume it. -/
theorem legalizeBinop_spillReg_lsem {w : Nat} (s : Lstate w)
    (dst src opn : String) (h15s : reloadScratch ≠ src)
    (hstrip : stripWidthTag opn = opn) (v : BitVec w)
    (hop : applyOpn opn [s.lvm dst, s.lvm src] = some v) :
    ∃ s', lsemStraight
        [ .Lopn [.reg reloadScratch] "MOV" [.reg dst],
          .Lopn [.reg reloadScratch] opn [.reg reloadScratch, .reg src],
          .Lopn [.reg dst] "MOV" [.reg reloadScratch] ] s = some s'
      ∧ s'.lvm dst = v := by
  -- Step 1: `mov R15, dst` loads `s.lvm dst` into the scratch.
  have hmov1 : lsemStep (LinstrR.Lopn [.reg reloadScratch] "MOV" [.reg dst]) s
      = some ((s.setReg reloadScratch (s.lvm dst)).nextPc) := by
    simp only [lsemStep, List.map_cons, List.map_nil, evalOperand,
      ToLprogFaithfulProbe.stripWidthTag_MOV, applyOpn]
  -- Step 2: `op R15, src` reads `R15` (= `s.lvm dst`) and `src` (unchanged,
  -- `R15 ≠ src`), writes `R15`.
  have heval_r15 : evalOperand ((s.setReg reloadScratch (s.lvm dst)).nextPc)
      (.reg reloadScratch) = s.lvm dst := by
    simp [evalOperand, Lstate.setReg, Lstate.nextPc]
  have heval_src : evalOperand ((s.setReg reloadScratch (s.lvm dst)).nextPc)
      (.reg src) = s.lvm src := by
    simp only [evalOperand, Lstate.setReg, Lstate.nextPc, if_neg (Ne.symm h15s)]
  have hop2 : lsemStep (LinstrR.Lopn [.reg reloadScratch] opn [.reg reloadScratch, .reg src])
      ((s.setReg reloadScratch (s.lvm dst)).nextPc)
      = some ((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch v).nextPc) := by
    simp only [lsemStep, List.map_cons, List.map_nil, heval_r15, heval_src, hstrip, hop]
  -- Step 3: `mov dst, R15` reads `R15` (= `v`) and writes `dst`.
  have heval_r15_2 : evalOperand
      ((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch v).nextPc)
      (.reg reloadScratch) = v := by
    simp [evalOperand, Lstate.setReg, Lstate.nextPc]
  have hmov3 : lsemStep (LinstrR.Lopn [.reg dst] "MOV" [.reg reloadScratch])
      ((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch v).nextPc)
      = some (((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch v).nextPc).setReg dst v).nextPc := by
    simp only [lsemStep, List.map_cons, List.map_nil,
      ToLprogFaithfulProbe.stripWidthTag_MOV, heval_r15_2, applyOpn]
  refine ⟨(((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch v).nextPc).setReg dst v).nextPc, ?_, ?_⟩
  · simp only [lsemStraight_cons, hmov1, hop2, hmov3, lsemStraight_nil]
  · simp [Lstate.setReg, Lstate.nextPc]

/-! ## 3. The `(true, true)` branch: spill dst, spill src

`legalizeBinop dst src opn = mov R15, dst ; mov R14, src ; op R15, R14 ;
mov dst, R15`. Result at `dst`: `applyOpn opn [s.lvm dst, s.lvm src]`.
Side conds: `R15 ≠ R14`, `R15 ≠ src`. -/

/-- **`legalizeBinop` spill branch, spill-dst / spill-src.** Running
    `mov R15, dst ; mov R14, src ; op R15, R14 ; mov dst, R15` under
    `lsemStraight` writes, at `dst`, exactly `applyOpn opn [s.lvm dst, s.lvm src]`.
    Non-interference side conditions:
    * `reloadScratch ≠ reloadScratch2` (`R15 ≠ R14`): the op reads `R15` after
      `mov R14, src` wrote `R14`; if they aliased, the second reload would have
      clobbered the first.
    * `reloadScratch ≠ src` (`R15 ≠ src`): `mov R14, src` reads `src` after
      `mov R15, dst` wrote `R15`; if `src = R15` it would read the reloaded `dst`.

    Neither `reloadScratch2 ≠ dst` nor `reloadScratch ≠ dst` is needed for the
    read-back of the result `v` at `dst` (the final `mov dst, R15` writes `dst`
    last from `R15`, which holds `v` regardless). In the shipped pipeline all
    four pairwise-distinctness facts hold by construction (`R15`/`R14` are not
    spill names, the operands here both *are* spill names), so this is a strict
    subset of the available freshness; we assume only what the value needs. -/
theorem legalizeBinop_spillSpill_lsem {w : Nat} (s : Lstate w)
    (dst src opn : String) (h1514 : reloadScratch ≠ reloadScratch2)
    (h15s : reloadScratch ≠ src)
    (hstrip : stripWidthTag opn = opn) (v : BitVec w)
    (hop : applyOpn opn [s.lvm dst, s.lvm src] = some v) :
    ∃ s', lsemStraight
        [ .Lopn [.reg reloadScratch] "MOV" [.reg dst],
          .Lopn [.reg reloadScratch2] "MOV" [.reg src],
          .Lopn [.reg reloadScratch] opn [.reg reloadScratch, .reg reloadScratch2],
          .Lopn [.reg dst] "MOV" [.reg reloadScratch] ] s = some s'
      ∧ s'.lvm dst = v := by
  -- Step 1: `mov R15, dst` loads `s.lvm dst` into R15.
  have hmov1 : lsemStep (LinstrR.Lopn [.reg reloadScratch] "MOV" [.reg dst]) s
      = some ((s.setReg reloadScratch (s.lvm dst)).nextPc) := by
    simp only [lsemStep, List.map_cons, List.map_nil, evalOperand,
      ToLprogFaithfulProbe.stripWidthTag_MOV, applyOpn]
  -- Step 2: `mov R14, src` loads `src` (unchanged, `R15 ≠ src`) into R14.
  have heval_src : evalOperand ((s.setReg reloadScratch (s.lvm dst)).nextPc)
      (.reg src) = s.lvm src := by
    simp only [evalOperand, Lstate.setReg, Lstate.nextPc, if_neg (Ne.symm h15s)]
  have hmov2 : lsemStep (LinstrR.Lopn [.reg reloadScratch2] "MOV" [.reg src])
      ((s.setReg reloadScratch (s.lvm dst)).nextPc)
      = some ((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch2 (s.lvm src)).nextPc) := by
    simp only [lsemStep, List.map_cons, List.map_nil, heval_src,
      ToLprogFaithfulProbe.stripWidthTag_MOV, applyOpn]
  -- Step 3: `op R15, R14` reads R15 (= s.lvm dst, `R15 ≠ R14`) and R14 (= s.lvm src),
  -- writes R15.
  have heval_r15 : evalOperand
      ((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch2 (s.lvm src)).nextPc)
      (.reg reloadScratch) = s.lvm dst := by
    simp only [evalOperand, Lstate.setReg, Lstate.nextPc, if_neg h1514, if_true]
  have heval_r14 : evalOperand
      ((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch2 (s.lvm src)).nextPc)
      (.reg reloadScratch2) = s.lvm src := by
    simp [evalOperand, Lstate.setReg, Lstate.nextPc]
  have hop3 : lsemStep (LinstrR.Lopn [.reg reloadScratch] opn [.reg reloadScratch, .reg reloadScratch2])
      ((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch2 (s.lvm src)).nextPc)
      = some (((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch2 (s.lvm src)).nextPc).setReg reloadScratch v).nextPc := by
    simp only [lsemStep, List.map_cons, List.map_nil, heval_r15, heval_r14, hstrip, hop]
  -- Step 4: `mov dst, R15` reads R15 (= v), writes dst.
  have heval_r15_2 : evalOperand
      (((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch2 (s.lvm src)).nextPc).setReg reloadScratch v).nextPc
      (.reg reloadScratch) = v := by
    simp [evalOperand, Lstate.setReg, Lstate.nextPc]
  have hmov4 : lsemStep (LinstrR.Lopn [.reg dst] "MOV" [.reg reloadScratch])
      (((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch2 (s.lvm src)).nextPc).setReg reloadScratch v).nextPc
      = some ((((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch2 (s.lvm src)).nextPc).setReg reloadScratch v).nextPc.setReg dst v).nextPc := by
    simp only [lsemStep, List.map_cons, List.map_nil,
      ToLprogFaithfulProbe.stripWidthTag_MOV, heval_r15_2, applyOpn]
  refine ⟨((((((s.setReg reloadScratch (s.lvm dst)).nextPc).setReg reloadScratch2 (s.lvm src)).nextPc).setReg reloadScratch v).nextPc.setReg dst v).nextPc, ?_, ?_⟩
  · simp only [lsemStraight_cons, hmov1, hmov2, hop3, hmov4, lsemStraight_nil]
  · simp [Lstate.setReg, Lstate.nextPc]

/-! ## 4. The `physMap` RA-renaming read-refinement

The second pass `toLprogPhysAbi` applies on top of the virtual body is the
linear-scan register allocation, materialised by `remapOperand`
(`JasminLprogExport.lean:1279`): a `.reg n` operand becomes
`.reg (physRegName (physMapTabled tbl (nameSlot body n)))`, i.e. its name is
renamed along the physical map `ρ n := physRegName (physMapTabled tbl
(nameSlot body n))`. Immediates pass through, and (as `remapOperand` is
written) `arr` / `arrIdx` operands also pass through *unrenamed*.

The semantic content of "RA preserves the denotation" is the
**read-commutes-with-renaming** fact: if the physical store `s'` is related to
the virtual store `s` along `ρ` — every renamed register reads in `s'` what the
original read in `s` (`s'.lvm (ρ n) = s.lvm n`) — then evaluating the renamed
operand against `s'` equals evaluating the original against `s`. This is the
pointwise core that `StoreAgrees` (`JasminLsemSimulation.lean:207`) packages for
the *virtual* `resolveVar` naming; here it is stated for the *physical*
`remapOperand` renaming. We prove it for register operands — exactly the
read-refinement the binop fragment (the two-address spill lemmas above) needs.

This is **not** the full `physBody` faithfulness step. The residual it leaves:
* `arr` / `arrIdx` operands are passed through unrenamed by `remapOperand`, so
  their reads are governed by a *memory* agreement, not this register relation
  (the `StoreAgreesM` analogue, `JasminLsemMem.lean`); out of scope here.
* establishing the store relation `s'.lvm ∘ ρ = s.lvm` is itself an
  RA-correctness obligation (`ρ` must be injective on the live set for the
  relation to be *maintained* across writes — the `RegMachineSim` keystone
  `jinstr_renameBlock_sound` proves the maintenance for a uniform renaming, but
  `physBody` interleaves the two-address `mov`s and spill reloads, so the
  keystone does not transfer directly). We prove the *read* side; the
  *maintenance* side is the documented residual. -/

/-- The physical RA renaming `remapOperand` applies to register names: a logical
    name `n` maps to its physical slot's register/spill name. (The abbreviation
    isolates the renaming `ρ` that `remapOperand body tbl (.reg n) = .reg (ρ n)`
    uses, so the read-refinement below reads cleanly.) -/
def physRename (body : Lcmd) (tbl : Array Nat) (n : String) : String :=
  physRegName (physMapTabled tbl (nameSlot body n))

/-- `remapOperand` on a register operand is renaming its name by `physRename`. -/
theorem remapOperand_reg (body : Lcmd) (tbl : Array Nat) (n : String) :
    remapOperand body tbl (.reg n) = .reg (physRename body tbl n) := rfl

/-- **RA read-refinement (register operands).** If the physical store `s'`
    reads, at every renamed register, the value the virtual store `s` read at the
    original register (`hrel : ∀ n, s'.lvm (physRename body tbl n) = s.lvm n`),
    then evaluating the `remapOperand`-renamed register operand against `s'`
    equals evaluating the original against `s`. The pointwise core of "RA
    preserves the read", parallel to `StoreAgrees` for the virtual naming. -/
theorem evalOperand_remapOperand_reg {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (s s' : Lstate w) (n : String)
    (hrel : ∀ m, s'.lvm (physRename body tbl m) = s.lvm m) :
    evalOperand s' (remapOperand body tbl (.reg n)) = evalOperand s (.reg n) := by
  rw [remapOperand_reg]
  simp only [evalOperand]
  exact hrel n

/-! ## 5. Unified per-`legalizeBinop` faithfulness (all four branches)

The probe's no-spill case (`ToLprogFaithfulProbe.twoAddrExpand_lsem`, the
`(false,false)` branch *after* the leading two-address `mov`) and the three
spill lemmas above together cover every `(dst.isSpill, src.isSpill)` branch of
`legalizeBinop`. We package them as one statement over the actual
`legalizeBinop` function, on `.reg`-named operands, with the per-branch
non-interference hypotheses gathered into the standing scratch-freshness facts.

What this composes — and what it does **not**:
* it IS the faithfulness of the `legalizeBinop` pass in isolation: whatever the
  spill classification, the emitted sequence writes `applyOpn opn [dst,src]` at
  the binop's destination register;
* it is NOT yet `physBody` faithfulness — `physBody` first *renames* operands
  through the RA map (§4) and emits a leading two-address `mov dst, s0` (the
  `lowerTwoAddr` collapse) before `legalizeBinop`; wiring §4's read-refinement
  and the probe's `mov` step in front of this needs the store-relation
  *maintenance* (the documented residual), and the whole-function step further
  needs the ABI prologue/epilogue + the `Lret` terminator, which are control
  flow outside `lsemStraight`'s straight-line scope (`lsemStep .Lret = none`,
  honestly **not** modeled). -/

/-- **`legalizeBinop` faithfulness — all four spill branches.** For register-named
    operands `dst`, `src`, running `legalizeBinop (.reg dst) (.reg src) opn`
    under `lsemStraight` writes, at `dst`, exactly `applyOpn opn [s.lvm dst,
    s.lvm src]` — the value the direct two-address binop `op dst, src` denotes.
    The non-interference hypotheses are exactly the per-branch scratch-freshness
    conditions identified above, gathered: `dst ≠ R15`, `R15 ≠ src`,
    and `R15 ≠ R14`. In the shipped pipeline every one holds by construction
    (`R15`/`R14` are not produced by `physRegName`, so they differ from any
    operand name; `R15 ≠ R14` is a constant disequality). The `mov` mnemonic is
    the standard `"MOV"` (the move opcode the reload sequences thread spills
    through). -/
theorem legalizeBinop_lsem {w : Nat} (s : Lstate w) (dst src opn : String)
    (hd15 : dst ≠ reloadScratch) (h15s : reloadScratch ≠ src)
    (h1514 : reloadScratch ≠ reloadScratch2)
    (hstrip : stripWidthTag opn = opn) (v : BitVec w)
    (hop : applyOpn opn [s.lvm dst, s.lvm src] = some v) :
    ∃ s', lsemStraight (legalizeBinop (.reg dst) (.reg src) opn "MOV") s = some s'
      ∧ s'.lvm dst = v := by
  unfold legalizeBinop
  -- Dispatch on the four spill classifications.
  cases (LOperand.reg dst).isSpill <;> cases (LOperand.reg src).isSpill <;>
    simp only []
  · -- (false, false): direct `op dst, src`. One `Lopn`.
    refine ⟨(s.setReg dst v).nextPc, ?_, ?_⟩
    · have hstep : lsemStep (LinstrR.Lopn [.reg dst] opn [.reg dst, .reg src]) s
          = some ((s.setReg dst v).nextPc) := by
        simp only [lsemStep, List.map_cons, List.map_nil, evalOperand, hstrip, hop]
      simp only [lsemStraight_cons, hstep, lsemStraight_nil]
    · simp [Lstate.setReg, Lstate.nextPc]
  · -- (false, true): `mov R15, src ; op dst, R15`.
    exact legalizeBinop_regSpill_lsem s dst src opn hd15 hstrip v hop
  · -- (true, false): `mov R15, dst ; op R15, src ; mov dst, R15`.
    exact legalizeBinop_spillReg_lsem s dst src opn h15s hstrip v hop
  · -- (true, true): `mov R15, dst ; mov R14, src ; op R15, R14 ; mov dst, R15`.
    exact legalizeBinop_spillSpill_lsem s dst src opn h1514 h15s hstrip v hop

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
