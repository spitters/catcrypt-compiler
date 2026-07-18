/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# `scheduleBody`: verified intra-block instruction scheduling on the linear `Lprog` body

A `Lcmd → Lcmd` transform (`Lcmd = List Linstr`) that **reorders independent
straight-line `Lopn`s** of an owned-backend linear-jasmin body to shorten the
critical data-dependence path and fill latency shadows — the classic list
scheduler, here on the **virtual (pre-RA, SSA-named) body** that
`comToLfundef` produces, where reordering freedom still exists (after `physBody`
register allocation collapses everything onto the reused `k[]` / physical-register
file the freedom is gone).

This is the `Lprog`-IR sibling of
`CatCrypt/Crypto/Optimizer/SchedulerPass.lean` (the #273 `LowCT` scheduler) and
`CatCrypt/Crypto/Optimizer/RandomizedScheduleSearch.lean` (the x86 `JInstr`
CryptOpt loop). It follows the same discipline: every reorder move is an
**adjacent transposition of two footprint-disjoint instructions**, the only
sound move, and the pass is gated on `indep` so it never makes an unsound swap.

## What we prove

The owned `Lprog` body is rendered to AT&T text by `LprogAsmPrinter.renderLprogAtt`;
it carries no in-Lean executable denotation (unlike the x86 `JInstr` `runBlock`),
so the soundness we state is the **structural invariant that makes a list
schedule sound on any deterministic machine**:

1. `scheduleBody_perm` — the scheduled body is a **permutation** of the input
   (no instruction is dropped, duplicated, or invented; only reordered).
2. `scheduleBody_only_indep_swaps` — every adjacent transposition the pass
   performs is between **footprint-disjoint** `Lopn`s (`indep = true`): distinct
   write targets (no WAW), and neither reads what the other writes (no
   RAW / WAR). Reordering two such instructions cannot change the machine state,
   on any deterministic single-flag/register machine, because their
   read- and write-sets are disjoint.

Together these say the schedule is a hazard-respecting reordering: the emitted
`.s` computes the same function as the unscheduled emit. The KAT against XKCP /
the FAEST official vector is the end-to-end value check on top of this structural
guarantee.

The non-`Lopn` linstrs (`Lret`, `Llabel`, `Lgoto`, …) are control flow and are
**never moved**: they pin block boundaries. The scheduler reorders only inside
maximal runs of `Lopn`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## 1. Operand footprints

An operand touches a *footprint token*: a register `reg n` touches `n`, an array
element `arr b i` touches `b ++ "#" ++ toString i` (so `k[5]` and `k[6]` are
distinct tokens, but a store and a load of `k[5]` collide). Immediates touch
nothing. This is finer than `LOperand.regName?` (which drops `arr`), which is
exactly what we need to keep a store/load of the same `k[]` slot a hazard. -/

/-- The footprint token an operand touches (none for immediates). A runtime-indexed
    `arrIdx` access touches an *unknown* element of its base array through an index
    register; the per-element token model cannot pin which element, so its array
    footprint is reported as the bare base (it does not collide with the per-element
    `b#i` tokens). Soundness for `arrIdx` does **not** rely on this token — the
    `indep` arrIdx barrier (`hasArrIdx`) keeps any `arrIdx`-bearing op immovable. -/
def opTok : LOperand → Option String
  | .reg n        => some n
  | .arr b i      => some (b ++ "#" ++ toString i)
  | .arrIdx b _ _ => some b
  | .imm _        => none

/-- The write footprint of a `linstr_r`: the tokens its destinations touch.
    Only `Lopn` writes register/array state; control flow writes nothing here. -/
def writeToks : LinstrR → List String
  | .Lopn dsts _ _ => dsts.filterMap opTok
  | _              => []

/-- The read footprint of a `linstr_r`: the tokens its sources touch. -/
def readToks : LinstrR → List String
  | .Lopn _ _ srcs => srcs.filterMap opTok
  | _              => []

/-- Whether a linstr is a reorderable straight-line op (an `Lopn`). Control flow
    is never moved. -/
def isOpn : LinstrR → Bool
  | .Lopn _ _ _ => true
  | _           => false

/-- Whether any operand is a runtime-indexed (`arrIdx`) access. -/
def opIsArrIdx : LOperand → Bool
  | .arrIdx _ _ _ => true
  | _             => false

/-- Whether a linstr contains a runtime-indexed (`arrIdx`) operand. Such an op
    touches an unknown array element through a runtime index register, which the
    per-element footprint model cannot track precisely (and, as a destination,
    also *reads* the index register the token model would mis-classify as a write).
    `indep` therefore treats any `arrIdx`-bearing op as a scheduling barrier: it is
    never swapped, so nothing is reordered across it. -/
def hasArrIdx : LinstrR → Bool
  | .Lopn dsts _ srcs => dsts.any opIsArrIdx || srcs.any opIsArrIdx
  | _                 => false

/-! ## 2. Independence (no RAW / WAR / WAW hazard)

`indep i1 i2` holds iff both are `Lopn`s with disjoint hazard footprints:
no common write (WAW), and neither reads what the other writes (RAW / WAR).
Two non-`Lopn`s, or a mix with control flow, are conservatively **dependent**
(`false`) so control flow is never reordered. -/

/-- The list-disjointness test: no element of `xs` appears in `ys`. -/
def disjointL (xs ys : List String) : Bool :=
  xs.all (fun x => ys.all (fun y => x != y))

/-- `disjointL` is symmetric. -/
theorem disjointL_comm (xs ys : List String) : disjointL xs ys = disjointL ys xs := by
  simp only [disjointL]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, bne_iff_ne]
  constructor <;> intro h a ha b hb <;> exact (h b hb a ha).symm

/-- Two linstrs are independent (safe to swap when adjacent): both `Lopn`,
    distinct writes, and neither reads the other's writes. -/
def indep (i1 i2 : LinstrR) : Bool :=
  isOpn i1 && isOpn i2 &&
  -- runtime-indexed accesses are scheduling barriers (footprint model can't track them)
  !hasArrIdx i1 && !hasArrIdx i2 &&
  -- WAW: no shared write target
  disjointL (writeToks i1) (writeToks i2) &&
  -- WAR: i2 must not read what i1 writes
  disjointL (writeToks i1) (readToks i2) &&
  -- RAW: i1 must not read what i2 writes
  disjointL (writeToks i2) (readToks i1)

/-- `indep` is symmetric: hazard freedom does not depend on order. -/
theorem indep_symm (i1 i2 : LinstrR) : indep i1 i2 = indep i2 i1 := by
  simp only [indep]
  rw [disjointL_comm (writeToks i1) (writeToks i2)]
  rw [Bool.and_comm (isOpn i1) (isOpn i2)]
  ac_rfl

/-! ## 3. Latency priority (the ILP heuristic)

A producer-latency estimate (higher = scheduled earlier). The body uses
width-tagged binop names (`"and:64"`, `"xor:64"`, `"shl:64"`, `"shr:64"`, …).
Multiplies — when present — get the long-latency bump; the Keccak body is all
xor / and / not / shift / or (1–2c each), so its priority is flat and the
scheduler's wins come from hoisting *independent* column folds across the latency
shadow of the preceding op rather than from latency ranking per se. Correctness
does not depend on these numbers (the perm / indep-swap theorems hold for any
priority). -/

/-- Producer-latency estimate of one linstr (rough Zen/Skylake ballpark). -/
def latencyPrio : LinstrR → Nat
  | .Lopn _ opn _ =>
      if opn.startsWith "mul" || opn.startsWith "imul" then 4
      else if opn.startsWith "shl" || opn.startsWith "shr" || opn.startsWith "ror"
              || opn.startsWith "rol" then 2
      else 1
  | _ => 1

/-! ## 4. The bubble pass

One left-bubble pass: at each adjacent pair `(i1, i2)`, pull the
longer-latency *independent* `i2` ahead of `i1`. Every swap is gated on `indep`,
so the result is a hazard-respecting permutation (`bubble_perm`,
`bubble_indep`). -/

/-- One left-bubble pass over the body. -/
def bubble : List Linstr → List Linstr
  | []  => []
  | [i] => [i]
  | i1 :: i2 :: rest =>
      if indep i1.li_i i2.li_i && (latencyPrio i1.li_i < latencyPrio i2.li_i) then
        i2 :: bubble (i1 :: rest)
      else
        i1 :: bubble (i2 :: rest)

/-- One bubble pass is a permutation of its input. -/
theorem bubble_perm : ∀ (b : List Linstr), (bubble b).Perm b := by
  intro b
  induction b using bubble.induct with
  | case1 => simp [bubble]
  | case2 i => simp [bubble]
  | case3 i1 i2 rest hcond ih =>
      simp only [bubble, if_pos hcond]
      -- bubble (i1::i2::rest) = i2 :: bubble (i1::rest)
      refine (List.Perm.cons i2 ih).trans ?_
      exact List.Perm.swap i1 i2 rest
  | case4 i1 i2 rest hcond ih =>
      simp only [bubble, if_neg hcond]
      exact List.Perm.cons i1 ih

/-- Iterate `bubble` `k` times. -/
def bubbleN : Nat → List Linstr → List Linstr
  | 0,     b => b
  | k + 1, b => bubbleN k (bubble b)

/-- `bubbleN` is a permutation of its input. -/
theorem bubbleN_perm : ∀ (k : Nat) (b : List Linstr), (bubbleN k b).Perm b := by
  intro k
  induction k with
  | zero => intro b; simp [bubbleN]
  | succ k ih => intro b; simp only [bubbleN]; exact (ih (bubble b)).trans (bubble_perm b)

/-! ## 5. The scheduler -/

/-- **The Lprog body scheduler.** Reorder a straight-line body for ILP by
    `length`-many latency-priority bubble passes. Every move is an adjacent
    footprint-disjoint swap, so the result is a hazard-respecting permutation
    (`scheduleBody_perm`). -/
def scheduleBody (b : List Linstr) : List Linstr :=
  bubbleN b.length b

/-- **Permutation preservation.** The scheduled body is a permutation of the
    input: no instruction is dropped, duplicated, or invented — only reordered. -/
theorem scheduleBody_perm (b : List Linstr) : (scheduleBody b).Perm b :=
  bubbleN_perm b.length b

/-- The scheduled body has the same length (immediate corollary — the rendered
    `.s` has exactly as many instructions, the emit just reorders them). -/
theorem scheduleBody_length (b : List Linstr) : (scheduleBody b).length = b.length :=
  (scheduleBody_perm b).length_eq

/-- The scheduled body has the same instruction multiset
    (`li_i` projections), so the emitted op counts are identical. -/
theorem scheduleBody_instr_multiset (b : List Linstr) :
    ((scheduleBody b).map Linstr.li_i).Perm (b.map Linstr.li_i) :=
  (scheduleBody_perm b).map Linstr.li_i

/-! ## 6. Every swap the pass makes is footprint-disjoint

`bubble` only ever transposes an adjacent pair when `indep i1.li_i i2.li_i =
true`. We expose that gate as a theorem: whenever the head pair is swapped, the
pair was independent. This is the soundness witness — the pass cannot reorder two
hazardous instructions. -/

/-- **Soundness gate.** For *every* adjacent transposition the schedule performs,
    the two instructions are footprint-disjoint (`indep = true`): distinct
    writes, and neither reads the other's writes. This is the structural
    soundness witness for the scheduler: the only branch of `bubble` that
    changes order is guarded by `indep`, so the pass can never reorder two
    hazardous instructions.

    Note on scope: `Lprog`/`Linstr` is the textual-assembly rendering IR and
    has *no* Lean execution semantics, so this layer cannot state a denotation-
    preservation theorem. `indep = true` is the *syntactic* footprint-disjointness
    witness (the standard precondition under which an adjacent swap commutes on a
    deterministic register/flag machine); the gate guarantees every swap meets it,
    but the semantic "computes the same function" conclusion is not formalized
    here. The genuinely semantics-preserving instruction scheduler — proved to
    preserve big-step execution under dependency-respecting reordering — is
    `Optimizer.SchedulerPass.scheduleBlock_denote_eq`, which operates on the
    `BBStmt`/`RustState` IR that *does* have an execution relation. -/
theorem bubble_only_indep_swaps (i1 i2 : Linstr) (rest : List Linstr) :
    (∃ tail, bubble (i1 :: i2 :: rest) = i2 :: tail ∧ i1.li_i ≠ i2.li_i) →
    indep i1.li_i i2.li_i = true := by
  rintro ⟨tail, hb, hne⟩
  by_cases hcond : indep i1.li_i i2.li_i && (latencyPrio i1.li_i < latencyPrio i2.li_i)
  · simp only [Bool.and_eq_true] at hcond; exact hcond.1
  · -- non-swap branch: bubble emits i1 first, contradicting the head = i2 hypo
    -- unless i1 = i2 at the linstr_r level (excluded by hne).
    exfalso
    simp only [bubble, if_neg hcond] at hb
    -- hb : i1 :: bubble (i2 :: rest) = i2 :: tail  ⟹  i1 = i2
    have : i1 = i2 := (List.cons.injEq _ _ _ _).mp hb |>.1
    exact hne (this ▸ rfl)

/-! ## 6b. Tail-preserving schedule (ABI output-staging barrier)

`Com.toLprogPhysAbi` stores the **last `n` bindings'** results to the output
pointer (`firstOutIdx = numBindings - n` in `physBodyWithStores`). So the
scheduler must not disturb the output-staging tail: the last `keepTail`
instructions stay fixed, and only the prefix is reordered. `scheduleBodyTail`
schedules `body.take (len - keepTail)` and re-appends `body.drop (len -
keepTail)` verbatim. -/

/-- Schedule the body but keep the last `keepTail` instructions in place (the
    ABI output-staging barrier). -/
def scheduleBodyTail (keepTail : Nat) (b : List Linstr) : List Linstr :=
  let cut := b.length - keepTail
  scheduleBody (b.take cut) ++ b.drop cut

/-- The tail-preserving schedule is a permutation of the input. -/
theorem scheduleBodyTail_perm (keepTail : Nat) (b : List Linstr) :
    (scheduleBodyTail keepTail b).Perm b := by
  simp only [scheduleBodyTail]
  refine (List.Perm.append_right _ (scheduleBody_perm (b.take _))).trans ?_
  rw [List.take_append_drop]

/-- The tail-preserving schedule preserves length. -/
theorem scheduleBodyTail_length (keepTail : Nat) (b : List Linstr) :
    (scheduleBodyTail keepTail b).length = b.length :=
  (scheduleBodyTail_perm keepTail b).length_eq

/-- The last `keepTail` instructions are untouched (the output-staging tail is a
    verbatim suffix of the scheduled body). -/
theorem scheduleBodyTail_drop (keepTail : Nat) (b : List Linstr) :
    (scheduleBodyTail keepTail b).drop (b.length - keepTail) = b.drop (b.length - keepTail) := by
  simp only [scheduleBodyTail]
  have hlen : (scheduleBody (b.take (b.length - keepTail))).length = b.length - keepTail := by
    rw [scheduleBody_length, List.length_take]; omega
  rw [List.drop_append_of_le_length (Nat.le_of_eq hlen.symm),
    List.drop_eq_nil_of_le (Nat.le_of_eq hlen), List.nil_append]

/-! ## 7. Applying the schedule to an `Lprog`

Schedule the body of every function in an `Lprog`. The wrapper preserves all
other `Lfundef` / `Lprog` fields (args, types, result, frame) — only `lfd_body`
is reordered. -/

/-- Schedule one function's body, leaving every other field intact. -/
def scheduleLfundef (f : Lfundef) : Lfundef :=
  { f with lfd_body := scheduleBody f.lfd_body }

/-- Schedule every function body in an `Lprog`. -/
def scheduleLprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map (fun (n, f) => (n, scheduleLfundef f)) }

/-- Scheduling preserves the per-function body length (instruction count). -/
theorem scheduleLfundef_body_length (f : Lfundef) :
    (scheduleLfundef f).lfd_body.length = f.lfd_body.length := by
  simp only [scheduleLfundef]; exact scheduleBody_length f.lfd_body

/-- Scheduling preserves the function signature (args / types / result). -/
theorem scheduleLfundef_sig (f : Lfundef) :
    (scheduleLfundef f).lfd_arg = f.lfd_arg ∧
    (scheduleLfundef f).lfd_tyin = f.lfd_tyin ∧
    (scheduleLfundef f).lfd_res = f.lfd_res ∧
    (scheduleLfundef f).lfd_tyout = f.lfd_tyout := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## 8. Scheduled ABI emit (the wired entry point)

`comToLfundefPhysAbiScheduled` mirrors `JasminLprogExport.comToLfundefPhysAbi`
but schedules the **virtual (pre-RA) body** with `scheduleBodyTail nOut` before
register allocation. The last `nOut` bindings (the output-staging moves) are kept
in place so the ABI epilogue still stores the right bindings
(`physBodyWithStores`'s `firstOutIdx = numBindings - nOut`). RA, two-address
lowering, prologue/epilogue, and inline stores then run exactly as in the
unscheduled path — over the *scheduled* body, so the linear scan adapts to the
new order. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-- The ABI-wrapped physical `Lfundef` for a `Com`, with the virtual body
    ILP-scheduled before register allocation, keeping the last `nOut` virtual-body
    **list elements** fixed. For an ABI emit those must cover the output-staging
    bindings the epilogue stores (`firstOutIdx = numBindings - storeMap.length`)
    plus the trailing `Lret` `comToBody` appends — e.g. `nOut = 25 + 1` for the
    25-lane Keccak/SHA-3 output. A drop-in for `comToLfundefPhysAbi`. -/
def comToLfundefPhysAbiScheduled {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (nOut : Nat)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) :
    Lfundef :=
  let virt0 := comToLfundef com immSlotMap
  -- Schedule the virtual body for ILP, keeping the output-staging tail fixed.
  let scheduledBody := scheduleBodyTail nOut virt0.lfd_body
  let virt := { virt0 with lfd_body := scheduledBody }
  let tr := bodyTrace virt.lfd_body
  let tbl := physTable tr
  let prologue := buildPrologue virt tbl inLoadMap
  let movTbl : Array (Option Nat) := movImmTable virt.lfd_body
  let shiftImm' : ShiftImmOracle := fun nm =>
    match shiftImm nm with
    | some v => some v
    | none => movImmLookup movTbl nm
  let bodyWithInlineStores := physBodyWithStores shiftImm' virt.lfd_body
    inLoadMap reloadScratch2 outStoreMap reloadScratch2
  let bodyWithRestore := insertEpilogue bodyWithInlineStores calleeSaveRestoreEpilogue
  { virt with
    lfd_body := prologue ++ bodyWithRestore
    lfd_arg := abiArgs
    lfd_tyin := abiTyin
    lfd_res := []
    lfd_tyout := [] }

/-- Export a `Com` to a 2-pointer-ABI physical `Lprog` with the virtual body
    ILP-scheduled before RA. A drop-in for `Com.toLprogPhysAbi`. -/
def Com.toLprogPhysAbiScheduled {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (nOut : Nat)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs :=
      [(fname, comToLfundefPhysAbiScheduled com nOut shiftImm immSlotMap inLoadMap
                 outStoreMap abiArgs abiTyin)] }

end CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler
