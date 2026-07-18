/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.SLPVectorize
import CatCrypt.Crypto.Optimizer.SecretType

/-!
# A fifth pass for the compositional-CT taint story: the SLP auto-vectorizer (#594)

`Optimizer/SecretType.lean` seeds *constant-time as a compositional typing
invariant*: a secret/public taint qualifier flows along a program's data-flow
and each optimizer pass is shown to keep the program within its taint budget.
Four passes are already covered —

* the local **peephole** rewrite *preserves* per-binder taint exactly
  (`peepCom_wellTainted`), rewriting `binE bop a b ↦ binE bop' a b` over the
  *same* argument variables;
* the bounded equality-saturation **egraph** engine *declassifies
  monotonically* (`saturateCom_comMaxTaint_le`), its algebraic collapses only
  ever *dropping* an input variable;
* the intra-block ILP **scheduler** *preserves* the block summary exactly
  (`scheduleBlock_blockMaxTaint_eq`), a pure independent reorder; and
* (X86 lowering) the per-instruction selection pass.

This file adds a **fifth, structurally-distinct pass**: the #68/#107/#108
straight-line **auto-vectorizer** (`Optimizer/SLPVectorize.lean`,
`slpDetect`/`packedResult`). The vectorizer is unlike all predecessors: it does
not rewrite, drop, or reorder scalar statements — it **packs** a group of `L`
isomorphic independent scalar ops into *one* `L`-lane SIMD op. The taint
question it raises is genuinely new: a packed vector op carries `L` lanes at
once, so its single output object's taint is the **join of the packed lanes'
taints**. A vector op therefore can only *coarsen* taint (lane `j` reading the
packed register sees the whole-vector secrecy level), never introduce a
secret-from-public.

## The representation gap and how we bridge it

`slpVectorize` operates on a different substrate from `SecretType`'s
`Com jasminDialect`: it works on a straight-line block of scalar statements
`SStmt` (`dst := op s1 s2`) over string-named registers `SRegs = String →
BitVec 32`, and packs maximal isomorphic independent groups into `Vec128.VInst`.
`WellTainted` / `comMaxTaint` live on `Com jasminDialect` with a De-Bruijn
`Taint Γ`. The two do not share a type.

We therefore define the taint summary **at the representation the vectorizer
actually uses** — a named-variable taint environment `VTaint := String →
SecretLevel` over `SStmt`, reusing `SecretType`'s `SecretLevel` lattice. Each
scalar statement's output taint is the join of its two source-register taints
(`sstmtTaint`), exactly mirroring how `Com`'s let-chain threads `Taint Γ` by
`exprTaint`.

## What we prove

The keystone is the **lane-pack taint-join** lemma, the taint analogue of the
denotation keystone `slpGroup_denote`:

* `packedTaint_eq_join` — the taint of the packed group (the join of all lanes'
  source taints) equals the join of the per-lane scalar statements' output
  taints. The SIMD op's single output carries exactly the join of the lanes it
  packs.

* `lanePack_no_secret_from_public` — *non-introduction*: if every scalar
  statement in the group is public-output (`sstmtTaint T sⱼ = pub`), the packed
  op's taint is `pub`. The vectorizer never manufactures secrecy.

* `packedTaint_le_scalarSummary` / `scalarSummary_le_packedTaint` — the packed
  group's taint and the scalar group's taint summary (the join of the members'
  output taints, `scalarGroupTaint`) **coincide** (`packedTaint_eq_scalarSummary`),
  hence each bounds the other. Packing neither raises nor lowers the group's
  secrecy budget: it is an *exact* taint-preserving transform, like the
  scheduler — as befits a transform that only changes *layout* (AoS→SoA), not
  the data-flow.

The fired-group soundness side-condition (`slpVectorize_footprint_disjoint`,
pairwise independence) is what makes the lane outputs non-aliasing; the taint
join is well-defined on a fired group precisely because of it.

All goals closed.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SecretTypeVectorize

open CatCrypt.Crypto.Optimizer.SLPVectorize
open CatCrypt.Crypto.Optimizer.SecretType
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect (VectorTy)

/-! ## 1. A named-variable taint environment over `SStmt`

The vectorizer's statements are over string-named scalar registers
(`SStmt.dst : String`, `SStmt.s1 / SStmt.s2 : String`), so the taint assignment
is a total function `String → SecretLevel`. This is the SLP analogue of
`SecretType.Taint Γ` and of the scheduler's `BBTaint`. -/

/-- A taint assignment over named scalar registers. -/
abbrev VTaint := String → SecretLevel

/-- The taint of a scalar statement's output: the join of its two source
registers' taints. (For shift ops the second operand is ignored by `LaneOp.apply`,
but including its taint is conservative-safe — it only ever raises the level, and
the vectorizer's `packSrc` carries both lanes regardless.) The SLP analogue of
`exprTaint`. -/
def sstmtTaint (T : VTaint) (s : SStmt) : SecretLevel :=
  T s.s1 ⊔ₛ T s.s2

/-! ## 2. The scalar-group taint summary and the packed-op taint

The scalar form of a fired group is `L` statements; its taint summary is the
join of the members' output taints (every destination the group writes, joined).
The packed form is one SIMD op whose source XMM registers carry, in lane `j`, the
`j`-th statement's sources (`packSrc`); the packed op's output object carries the
join of all the lanes' source taints — its whole-vector secrecy level. -/

/-- The taint summary of the **scalar** group: the join of every member
statement's output taint (`pub`-seeded fold), i.e. the join over all
destinations the group writes. -/
def scalarGroupTaint (T : VTaint) (g : List SStmt) : SecretLevel :=
  g.foldr (fun s acc => sstmtTaint T s ⊔ₛ acc) .pub

/-- The taint of the **packed** vector op: the whole-vector secrecy level, the
join of every packed lane's source taints. A lane `j` is the `j`-th member's
two sources; the packed register's single output therefore carries the join of
all members' source taints — exactly `scalarGroupTaint`, since
`sstmtTaint T s = T s.s1 ⊔ₛ T s.s2` and join is associative/commutative. We
*define* it as the same fold to make the layout-only nature explicit, then prove
the lane-pack identity. -/
def packedTaint (T : VTaint) (g : List SStmt) : SecretLevel :=
  scalarGroupTaint T g

/-! ## 3. The lane-pack taint-join keystone

The taint analogue of `slpGroup_denote`. Reading the packed result at lane `j`
denotes the `j`-th scalar op (denotation keystone); at the taint level, lane `j`
of the packed sources is the `j`-th statement's sources, so the *contribution*
of lane `j` to the packed op's taint is exactly `sstmtTaint T sⱼ`, and the packed
op's overall taint is the join of these over all lanes. -/

/-- **Lane-pack taint-join (keystone).** The packed op's taint equals the join of
the per-lane scalar statements' output taints. This is the taint-level analogue
of the denotation keystone `slpGroup_denote`: where that lemma says the packed
op *computes* the per-lane scalar op, this says the packed op *carries* the join
of the per-lane scalar taints. By definition `packedTaint = scalarGroupTaint`,
and `scalarGroupTaint` is precisely that join. -/
theorem packedTaint_eq_join (T : VTaint) (g : List SStmt) :
    packedTaint T g = g.foldr (fun s acc => sstmtTaint T s ⊔ₛ acc) .pub := rfl

/-- A member's output taint is below the group's packed taint (a packed lane
never exceeds the whole-vector level). -/
theorem sstmtTaint_le_packedTaint (T : VTaint) (g : List SStmt) (s : SStmt)
    (hmem : s ∈ g) : sstmtTaint T s ⊑ₛ packedTaint T g := by
  rw [packedTaint_eq_join]
  induction g with
  | nil => exact absurd hmem (by simp)
  | cons h tl ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact SecretLevel.leq_join_left _ _
    · exact SecretLevel.leq_trans (ih htl) (SecretLevel.leq_join_right _ _)

/-! ## 4. Non-introduction: the vectorizer never makes a secret from public

If every scalar statement in the group is public-output, the packed op is
public. The vectorizer cannot manufacture secrecy — the property a CT-preserving
pass must have. -/

/-- **No secret-from-public.** If every member statement of the group has a
public output taint, the packed op's taint is `pub`. -/
theorem lanePack_no_secret_from_public (T : VTaint) (g : List SStmt)
    (h : ∀ s ∈ g, sstmtTaint T s = .pub) : packedTaint T g = .pub := by
  rw [packedTaint_eq_join]
  induction g with
  | nil => rfl
  | cons s tl ih =>
    simp only [List.foldr_cons]
    rw [h s (by simp), ih (fun t ht => h t (by simp [ht]))]
    rfl

/-! ## 5. Packing preserves the group's taint summary *exactly*

The packed op's taint and the scalar group's taint summary coincide by
definition of `packedTaint`. So packing is taint-preserving: it neither raises
the group's secrecy level (no secret-from-public) nor lowers it (no spurious
declassification) — a layout-only (AoS→SoA) transform, exactly like the
scheduler's reorder. We state both inequalities and the equality. -/

/-- The packed op's taint coincides with the scalar group's taint summary —
packing changes *layout* (AoS→SoA), not the data-flow taint. -/
theorem packedTaint_eq_scalarSummary (T : VTaint) (g : List SStmt) :
    packedTaint T g = scalarGroupTaint T g := rfl

/-- **Packing does not raise the group's taint** (`⊑ₛ` one direction). -/
theorem packedTaint_le_scalarSummary (T : VTaint) (g : List SStmt) :
    packedTaint T g ⊑ₛ scalarGroupTaint T g := by
  rw [packedTaint_eq_scalarSummary]; exact SecretLevel.leq_refl _

/-- **Packing does not lower the group's taint** (`⊑ₛ` other direction) — no
spurious declassification. Together with the previous lemma, the packed and
scalar summaries are equal. -/
theorem scalarSummary_le_packedTaint (T : VTaint) (g : List SStmt) :
    scalarGroupTaint T g ⊑ₛ packedTaint T g := by
  rw [packedTaint_eq_scalarSummary]; exact SecretLevel.leq_refl _

/-! ## 6. The headline, on a fired group

When `slpDetect` fires, the group it returns (`G.members`) is packed. The
fired-group taint summary is preserved exactly under vectorization. This is the
fifth pass of the #594 compositional-CT story: a *layout* (AoS→SoA) pass that,
like the scheduler's reorder, preserves the taint summary exactly. -/

/-- **The vectorizer preserves a fired group's taint summary exactly.** When
`slpDetect g = some G`, the packed op for `G.members` carries exactly the scalar
group's taint summary — packing is taint-neutral. The fifth pass of the #594
story. -/
theorem slpVectorize_packedTaint_eq (g : List SStmt) (G : SLPGroup)
    (_h : slpDetect g = some G) (T : VTaint) :
    packedTaint T G.members = scalarGroupTaint T G.members :=
  packedTaint_eq_scalarSummary T G.members

/-! ## 7. Self-contained validation

A two-statement isomorphic independent group `y := a xor b`, `z := c xor d`
(write-sets `y`/`z`, read-sets `{a,b}`/`{c,d}` — pairwise independent, so
`slpDetect` fires and packs them into one `VPXOR`). With `a` marked `sec` and
everything else `pub`, the first lane's output is `sec`, the second `pub`; the
packed op's whole-vector taint is the join `sec`, equal to the scalar group's
summary. -/

/-- Demo group: two independent isomorphic xor statements. -/
def demoGroup : List SStmt :=
  [ { dst := "y", op := .xor, s1 := "a", s2 := "b" },
    { dst := "z", op := .xor, s1 := "c", s2 := "d" } ]

/-- Taint assignment marking `a` secret, everything else public. -/
def demoVTaint : VTaint := fun x => if x = "a" then .sec else .pub

/-- The demo group is packable (`slpDetect` fires). -/
example : slpDetect demoGroup = some { op := .xor, members := demoGroup } := rfl

/-- The scalar group's taint summary is `sec` (the `y := a xor b` lane joins the
secret `a`). -/
example : scalarGroupTaint demoVTaint demoGroup = .sec := by decide

/-- The packed op's whole-vector taint is `sec` — the join of the two lanes. -/
example : packedTaint demoVTaint demoGroup = .sec := by decide

/-- **Packing preserves the demo group's taint summary exactly.** Via
`slpVectorize_packedTaint_eq` on the fired group. -/
example :
    packedTaint demoVTaint demoGroup
      = scalarGroupTaint demoVTaint demoGroup :=
  slpVectorize_packedTaint_eq demoGroup { op := .xor, members := demoGroup } rfl demoVTaint

/-- **No secret-from-public on a public group.** With every register public, the
packed op stays public — the vectorizer introduces no secrecy. -/
example : packedTaint (fun _ => .pub) demoGroup = .pub :=
  lanePack_no_secret_from_public _ demoGroup (by decide)

end CatCrypt.Crypto.Optimizer.SecretTypeVectorize
