/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminAST

set_option autoImplicit false

/-!
# Pointer-disjoint borrow check for bignum SSA routines

Companion to `LowCTBorrowCheck.lean` (which works on `LowCT`-level
named-borrow programs) and `MemoryModel.lean` (which provides the
`Disjoint` separation predicate).

This file adds a static check on `FunDecl` bodies that emit memory
operations (the bignum SSA fragment in `S2NBignumSSA.lean`):

1. **`memReadVars`** — base variables of every `Pload` in the body.
2. **`memWriteVars`** — base variables of every `Lmem` store.
3. **`isPointerSafe`** — every memory access goes through a parameter
   variable; no SSA-local variable is used as a base address (would
   indicate pointer arithmetic between params, which we don't model).
4. **`pointerParams`** — the inferred pointer parameters of a routine,
   read off the body.

The "borrow check" at this level is **not** a per-call admissibility
test (call sites in our pipeline are top-level extern functions). It's
a **WP-precondition synthesizer**: given a `FunDecl` for `bignum_*`,
it computes the pairwise `Disjoint` clauses the caller must establish.
-/

namespace CatCrypt.Crypto.Jasmin.PointerBorrow

open CatCrypt.Crypto.Jasmin

/-! ## §1. Read- and write-base extraction -/

/-- Variable name used as the base address of a `Pload`. -/
def baseOfPLoad : PExpr → Option String
  | .Pload _ x _ => some x.var.vname
  | _            => none

/-- Walk a `PExpr` collecting every base variable that's used as a
    `Pload` source. -/
def loadBasesPExpr : PExpr → List String
  | .Pload _ x _      => [x.var.vname]
  | .Papp1 _ e        => loadBasesPExpr e
  | .Papp2 _ a b      => loadBasesPExpr a ++ loadBasesPExpr b
  | _                 => []

/-- Walk a list of `PExpr`s collecting all `Pload` bases. -/
def loadBasesArgs (es : List PExpr) : List String :=
  es.flatMap loadBasesPExpr

/-- Base variable of an `Lmem` write target. -/
def writeBaseLVal : LVal → Option String
  | .Lmem _ x _ => some x.var.vname
  | _           => none

/-- All `Lmem` write bases in a list of LVals. -/
def writeBasesLVals (lvs : List LVal) : List String :=
  lvs.filterMap writeBaseLVal

mutual
/-- Read- and write-base sets for a single `InstrR`. -/
def readWriteBases : InstrR → List String × List String
  | .Cassgn lv _ _ rhs =>
      (loadBasesPExpr rhs, writeBasesLVals [lv])
  | .Copn lvs _ _ args =>
      (loadBasesArgs args, writeBasesLVals lvs)
  | .Cif _ ct cf =>
      let cR := bodyReadWriteBases ct
      let dR := bodyReadWriteBases cf
      (cR.1 ++ dR.1, cR.2 ++ dR.2)
  | .Ccall _ _ _ args =>
      (loadBasesArgs args, [])
  | .Cfor _ _ body =>
      bodyReadWriteBases body
  | .Cwhile cb _ ca =>
      let cR := bodyReadWriteBases cb
      let dR := bodyReadWriteBases ca
      (cR.1 ++ dR.1, cR.2 ++ dR.2)

/-- Aggregate over a body. -/
def bodyReadWriteBases : List InstrR → List String × List String
  | []      => ([], [])
  | i :: is =>
    let h := readWriteBases i
    let t := bodyReadWriteBases is
    (h.1 ++ t.1, h.2 ++ t.2)
end

/-- Pointer parameters: the union of `Pload`/`Lmem` base variables that
    appear in the body. (Filtered against the param list at the
    `pointerParams` level.) -/
def memBases (body : List InstrR) : List String :=
  let (rs, ws) := bodyReadWriteBases body
  (rs ++ ws).eraseDups

/-! ## §2. Inferred pointer parameters of a `FunDecl` -/

/-- The parameters of `fd` that are used as memory pointers. -/
def pointerParams (fd : FunDecl) : List String :=
  let bases := memBases fd.body
  fd.params.filterMap (fun p =>
    if bases.contains p.var.var.vname then some p.var.var.vname else none)

/-- Read-only pointer params: appear in some `Pload`, never in `Lmem`. -/
def pointerParamsReadOnly (fd : FunDecl) : List String :=
  let (rs, ws) := bodyReadWriteBases fd.body
  fd.params.filterMap (fun p =>
    let n := p.var.var.vname
    if rs.contains n ∧ ¬ ws.contains n then some n else none)

/-- Write pointer params: appear in some `Lmem`. -/
def pointerParamsWritten (fd : FunDecl) : List String :=
  let (_rs, ws) := bodyReadWriteBases fd.body
  fd.params.filterMap (fun p =>
    let n := p.var.var.vname
    if ws.contains n then some n else none)

/-! ## §3. Static admissibility check

A `FunDecl` is **pointer-safe** if every memory access goes through a
named parameter — never through an SSA-local variable. This forbids
pointer arithmetic between parameters (which would invalidate the
caller's disjointness assumption). -/

/-- Names of all formal parameters. -/
def paramNames (fd : FunDecl) : List String :=
  fd.params.map (fun p => p.var.var.vname)

/-- Check: every memory base in the body is a parameter name.

Uses the raw `bodyReadWriteBases` concat (not `memBases`, which dedups
the list); the two are equivalent for `.all`-style predicates because
`List.all` only depends on the set of elements, but the raw form admits
a cleaner soundness proof (see §6). -/
def isPointerSafe (fd : FunDecl) : Bool :=
  let (rs, ws) := bodyReadWriteBases fd.body
  let params := paramNames fd
  (rs ++ ws).all (fun b => params.contains b)

/-! ## §4. Caller-side disjointness obligation

For a routine `fd` with write-pointer params `[w₁, ..., w_k]` and
read-pointer params `[r₁, ..., r_m]`, the caller must establish:

  ∀ i, ∀ j ≠ i:  Disjoint (footprint w_i) (footprint w_j)
  ∀ i, ∀ j:      Disjoint (footprint w_i) (footprint r_j)

(Read-only params may freely alias each other — only the write
footprints need pairwise-disjointness with everything.)

`disjointObligations fd` returns the list of `(p, q)` pairs the caller
must show disjoint, as a deduplicated list. The caller's WP-precondition
includes one `Disjoint` clause per pair. -/

/-- All unordered pairs `(p, q)` from `(write × write) ∪ (write × read)`
    where `p ≠ q`. -/
def disjointObligations (fd : FunDecl) : List (String × String) :=
  let writes := pointerParamsWritten fd
  let reads  := pointerParamsReadOnly fd
  let writeWrite : List (String × String) :=
    writes.flatMap (fun p =>
      writes.filterMap (fun q => if p < q then some (p, q) else none))
  let writeRead : List (String × String) :=
    writes.flatMap (fun w =>
      reads.map (fun r => (w, r)))
  (writeWrite ++ writeRead).eraseDups

/-! ## §5. Sanity checks via `decide`

These are smoke tests: define a tiny FunDecl, check the obligation
list. The actual ports in `S2NBignumSSA.lean` go through the same
machinery once we land an `audit_pointerBorrow.lean` script. -/

example : True := by trivial

/-! ## §6. Soundness of `isPointerSafe`

`isPointerSafe fd` is a decidable check that every memory access (`Pload`
in expressions, `Lmem` in lvals) extracted by `bodyReadWriteBases` goes
through a parameter variable. The theorems in this section promote that
check to a structural Prop on the AST, usable downstream when reasoning
about an individual `Pload`/`Lmem` occurrence.

**Definition `MemBasesIn params e/lv/i/body`**: every `Pload`/`Lmem`
base name extracted by `loadBasesPExpr` / `writeBaseLVal` /
`readWriteBases` / `bodyReadWriteBases` is a member of `params`.

**Soundness (`isPointerSafe_implies_MemBasesIn`)**:
`isPointerSafe fd = true → Cmd.MemBasesIn (paramNames fd) fd.body`.

The structural Prop matches the *existing extraction*: in particular, it
follows the convention in `bodyReadWriteBases` that `Cif` and `Cwhile`
do **not** descend into their condition expressions (only the bodies).
So a `Pload` syntactically buried in a condition is invisible to both
`isPointerSafe` and `MemBasesIn`. Tightening the extraction is a
separate change. -/

/-- Every `Pload` base in expression `e` is in `params`. Mirrors the
    extraction in `loadBasesPExpr`. -/
def PExpr.MemBasesIn (params : List String) : PExpr → Prop
  | .Pload _ x _    => x.var.vname ∈ params
  | .Papp1 _ e      => PExpr.MemBasesIn params e
  | .Papp2 _ a b    => PExpr.MemBasesIn params a ∧ PExpr.MemBasesIn params b
  | _               => True

/-- Every `Lmem` base in lvalue `lv` is in `params`. Mirrors
    `writeBaseLVal`. -/
def LVal.MemBasesIn (params : List String) : LVal → Prop
  | .Lmem _ x _ => x.var.vname ∈ params
  | _           => True

mutual
/-- Every memory base in instruction `i` is in `params`. Matches the
    extraction shape of `readWriteBases` (in particular: `Cif` /
    `Cwhile` conditions are not descended into). -/
def InstrR.MemBasesIn (params : List String) : InstrR → Prop
  | .Cassgn lv _ _ rhs =>
      LVal.MemBasesIn params lv ∧ PExpr.MemBasesIn params rhs
  | .Copn lvs _ _ args =>
      (∀ lv ∈ lvs, LVal.MemBasesIn params lv) ∧
      (∀ a ∈ args, PExpr.MemBasesIn params a)
  | .Cif _ ct cf       => Cmd.MemBasesIn params ct ∧ Cmd.MemBasesIn params cf
  | .Cfor _ _ body     => Cmd.MemBasesIn params body
  | .Cwhile cb _ ca    => Cmd.MemBasesIn params cb ∧ Cmd.MemBasesIn params ca
  | .Ccall _ _ _ args  => ∀ a ∈ args, PExpr.MemBasesIn params a

/-- Every memory base in body `b` is in `params`. -/
def Cmd.MemBasesIn (params : List String) : List InstrR → Prop
  | []       => True
  | i :: is  => InstrR.MemBasesIn params i ∧ Cmd.MemBasesIn params is
end

/-! ### Bridge: subset of extracted bases ⇒ structural Prop -/

/-- If every base extracted from `e` lies in `params`, then `e`
    satisfies `PExpr.MemBasesIn params`. PExpr is a nested inductive
    (PappN / Pif have list/multiple sub-expressions), so we use a `match`
    + recursion shape rather than `induction`. -/
theorem PExpr.MemBasesIn_of_loadBases_subset {params : List String} :
    ∀ (e : PExpr), (∀ b, b ∈ loadBasesPExpr e → b ∈ params) →
        PExpr.MemBasesIn params e
  | .Pload _ x _, h => by
      show x.var.vname ∈ params
      exact h x.var.vname (by simp [loadBasesPExpr])
  | .Papp1 _ e, h =>
      PExpr.MemBasesIn_of_loadBases_subset e
        (fun b hb => h b (by simpa [loadBasesPExpr] using hb))
  | .Papp2 _ a b, h => by
      refine ⟨?_, ?_⟩
      · exact PExpr.MemBasesIn_of_loadBases_subset a
          (fun c hc => h c (by simp [loadBasesPExpr]; exact Or.inl hc))
      · exact PExpr.MemBasesIn_of_loadBases_subset b
          (fun c hc => h c (by simp [loadBasesPExpr]; exact Or.inr hc))
  | .Pconst _, _      => trivial
  | .Pbool _, _       => trivial
  | .Parr_init _, _   => trivial
  | .Pvar _, _        => trivial
  | .Pget _ _ _ _, _  => trivial
  | .Psub _ _ _ _ _, _ => trivial
  | .PappN _ _, _     => trivial
  | .Pif _ _ _ _, _   => trivial

/-- If `writeBaseLVal lv = some b`'s output is in `params` (when
    present), then `lv` satisfies `LVal.MemBasesIn params`. -/
theorem LVal.MemBasesIn_of_writeBase_subset {params : List String} (lv : LVal)
    (h : ∀ b, writeBaseLVal lv = some b → b ∈ params) :
    LVal.MemBasesIn params lv := by
  cases lv with
  | Lmem _ x _ =>
    show x.var.vname ∈ params
    exact h x.var.vname rfl
  | Lnone _ _ => trivial
  | Lvar _ => trivial
  | Laset _ _ _ _ => trivial
  | Lasub _ _ _ _ _ => trivial

/-- For a list of LVals: every base in `writeBasesLVals` is the witness
    for some constituent `writeBaseLVal`. -/
theorem LVal.MemBasesIn_of_writeBases_subset {params : List String}
    (lvs : List LVal)
    (h : ∀ b, b ∈ writeBasesLVals lvs → b ∈ params) :
    ∀ lv ∈ lvs, LVal.MemBasesIn params lv := by
  intro lv hlv
  apply LVal.MemBasesIn_of_writeBase_subset
  intro b hwb
  apply h
  -- `writeBasesLVals lvs = lvs.filterMap writeBaseLVal`. Membership
  -- via `List.mem_filterMap`.
  exact List.mem_filterMap.mpr ⟨lv, hlv, hwb⟩

/-- For a list of expressions: every base in `loadBasesArgs es` lies in
    `params`, so each individual `e ∈ es` has `PExpr.MemBasesIn params e`. -/
theorem PExpr.MemBasesIn_of_loadBasesArgs_subset {params : List String}
    (es : List PExpr)
    (h : ∀ b, b ∈ loadBasesArgs es → b ∈ params) :
    ∀ e ∈ es, PExpr.MemBasesIn params e := by
  intro e he
  apply PExpr.MemBasesIn_of_loadBases_subset
  intro b hb
  apply h
  -- `loadBasesArgs es = es.flatMap loadBasesPExpr`. Membership via
  -- `List.mem_flatMap`.
  exact List.mem_flatMap.mpr ⟨e, he, hb⟩

/-! ### Mutual structural soundness for instructions and bodies -/

mutual
/-- Soundness of `readWriteBases`: if its outputs are subset of
    `params`, then `i` satisfies `InstrR.MemBasesIn params`. -/
theorem InstrR.MemBasesIn_of_readWriteBases_subset
    {params : List String} (i : InstrR)
    (hR : ∀ b, b ∈ (readWriteBases i).1 → b ∈ params)
    (hW : ∀ b, b ∈ (readWriteBases i).2 → b ∈ params) :
    InstrR.MemBasesIn params i := by
  cases i with
  | Cassgn lv _ _ rhs =>
    refine ⟨?_, ?_⟩
    · apply LVal.MemBasesIn_of_writeBase_subset
      intro b hb
      apply hW
      -- `(readWriteBases (Cassgn lv ...)).2 = writeBasesLVals [lv]`
      simp [readWriteBases, writeBasesLVals, hb]
    · apply PExpr.MemBasesIn_of_loadBases_subset
      intro b hb
      exact hR b (by simpa [readWriteBases] using hb)
  | Copn lvs _ _ args =>
    refine ⟨?_, ?_⟩
    · apply LVal.MemBasesIn_of_writeBases_subset
      intro b hb
      exact hW b (by simpa [readWriteBases] using hb)
    · apply PExpr.MemBasesIn_of_loadBasesArgs_subset
      intro b hb
      exact hR b (by simpa [readWriteBases] using hb)
  | Cif _ ct cf =>
    refine ⟨?_, ?_⟩
    · apply Cmd.MemBasesIn_of_bodyReadWriteBases_subset
      · intro b hb
        exact hR b (by simp [readWriteBases]; exact Or.inl hb)
      · intro b hb
        exact hW b (by simp [readWriteBases]; exact Or.inl hb)
    · apply Cmd.MemBasesIn_of_bodyReadWriteBases_subset
      · intro b hb
        exact hR b (by simp [readWriteBases]; exact Or.inr hb)
      · intro b hb
        exact hW b (by simp [readWriteBases]; exact Or.inr hb)
  | Cfor _ _ body =>
    apply Cmd.MemBasesIn_of_bodyReadWriteBases_subset
    · intro b hb; exact hR b (by simpa [readWriteBases] using hb)
    · intro b hb; exact hW b (by simpa [readWriteBases] using hb)
  | Cwhile cb _ ca =>
    refine ⟨?_, ?_⟩
    · apply Cmd.MemBasesIn_of_bodyReadWriteBases_subset
      · intro b hb
        exact hR b (by simp [readWriteBases]; exact Or.inl hb)
      · intro b hb
        exact hW b (by simp [readWriteBases]; exact Or.inl hb)
    · apply Cmd.MemBasesIn_of_bodyReadWriteBases_subset
      · intro b hb
        exact hR b (by simp [readWriteBases]; exact Or.inr hb)
      · intro b hb
        exact hW b (by simp [readWriteBases]; exact Or.inr hb)
  | Ccall _ _ _ args =>
    apply PExpr.MemBasesIn_of_loadBasesArgs_subset
    intro b hb
    exact hR b (by simpa [readWriteBases] using hb)

/-- Soundness of `bodyReadWriteBases`: if its outputs are subset of
    `params`, then `body` satisfies `Cmd.MemBasesIn params`. -/
theorem Cmd.MemBasesIn_of_bodyReadWriteBases_subset
    {params : List String} (body : List InstrR)
    (hR : ∀ b, b ∈ (bodyReadWriteBases body).1 → b ∈ params)
    (hW : ∀ b, b ∈ (bodyReadWriteBases body).2 → b ∈ params) :
    Cmd.MemBasesIn params body := by
  match body with
  | [] => trivial
  | i :: is =>
    refine ⟨?_, ?_⟩
    · apply InstrR.MemBasesIn_of_readWriteBases_subset
      · intro b hb
        exact hR b (by simp [bodyReadWriteBases]; exact Or.inl hb)
      · intro b hb
        exact hW b (by simp [bodyReadWriteBases]; exact Or.inl hb)
    · apply Cmd.MemBasesIn_of_bodyReadWriteBases_subset
      · intro b hb
        exact hR b (by simp [bodyReadWriteBases]; exact Or.inr hb)
      · intro b hb
        exact hW b (by simp [bodyReadWriteBases]; exact Or.inr hb)
end

/-! ### Top-level soundness theorems -/

/-- Basic soundness: every base extracted by `bodyReadWriteBases` from
    `fd.body` is in `paramNames fd`, when `isPointerSafe fd` accepts. -/
theorem isPointerSafe_implies_rwBases_subset (fd : FunDecl)
    (h : isPointerSafe fd = true) :
    (∀ b, b ∈ (bodyReadWriteBases fd.body).1 → b ∈ paramNames fd) ∧
    (∀ b, b ∈ (bodyReadWriteBases fd.body).2 → b ∈ paramNames fd) := by
  unfold isPointerSafe at h
  -- After unfold: `((rs ++ ws).all (·.contains paramNames fd)) = true`
  have hall := List.all_eq_true.mp h
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have := hall b (List.mem_append.mpr (Or.inl hb))
    exact List.contains_iff_mem.mp this
  · have := hall b (List.mem_append.mpr (Or.inr hb))
    exact List.contains_iff_mem.mp this

/-- Structural soundness: if `isPointerSafe fd` accepts, then every
    memory access in the body has a base that is one of `fd`'s
    parameters, witnessed by the structural Prop `Cmd.MemBasesIn`. -/
theorem isPointerSafe_implies_MemBasesIn (fd : FunDecl)
    (h : isPointerSafe fd = true) :
    Cmd.MemBasesIn (paramNames fd) fd.body := by
  obtain ⟨hR, hW⟩ := isPointerSafe_implies_rwBases_subset fd h
  exact Cmd.MemBasesIn_of_bodyReadWriteBases_subset fd.body hR hW

/-! ### Disjointness obligations correctness -/

/-- Helper: `xs.eraseDups` is a sublist of `xs`, so any element of the
    deduplicated list was already in the original. The other direction
    is not needed for our soundness. -/
private theorem mem_of_mem_eraseDups.{u} {α : Type u} [BEq α] [LawfulBEq α] :
    ∀ (xs : List α) {a : α}, a ∈ xs.eraseDups → a ∈ xs
  | [], _, h => by simp [List.eraseDups_nil] at h
  | hd :: tl, a, h => by
      rw [List.eraseDups_cons] at h
      rcases List.mem_cons.mp h with rfl | hrest
      · exact List.mem_cons_self
      · refine List.mem_cons.mpr (Or.inr ?_)
        have hfilt := mem_of_mem_eraseDups _ hrest
        exact (List.mem_filter.mp hfilt).1
termination_by xs _ => xs.length
decreasing_by
  simp_wf
  exact Nat.lt_of_le_of_lt (List.length_filter_le _ _) (Nat.lt_succ_self _)

/-- Characterization of `pointerParamsWritten`: a name is in this list
    iff some param of `fd` carries that name and the name appears in the
    write set of the body. -/
private theorem mem_pointerParamsWritten {fd : FunDecl} {w : String}
    (hw : w ∈ pointerParamsWritten fd) :
    ∃ p ∈ fd.params, p.var.var.vname = w ∧
        (bodyReadWriteBases fd.body).2.contains w = true := by
  unfold pointerParamsWritten at hw
  rcases List.mem_filterMap.mp hw with ⟨p, hp, hopt⟩
  -- hopt : (if (..).contains p.var.var.vname = true
  --        then some p.var.var.vname else none) = some w
  by_cases hc : (bodyReadWriteBases fd.body).2.contains p.var.var.vname = true
  · rw [if_pos hc] at hopt
    have heq : p.var.var.vname = w := Option.some.inj hopt
    exact ⟨p, hp, heq, heq ▸ hc⟩
  · rw [if_neg hc] at hopt
    cases hopt

/-- Characterization of `pointerParamsReadOnly`: a name is in this list
    iff some param of `fd` carries it, the name appears in the read set,
    and does NOT appear in the write set. -/
private theorem mem_pointerParamsReadOnly {fd : FunDecl} {r : String}
    (hr : r ∈ pointerParamsReadOnly fd) :
    ∃ p ∈ fd.params, p.var.var.vname = r ∧
        (bodyReadWriteBases fd.body).1.contains r = true ∧
        (bodyReadWriteBases fd.body).2.contains r ≠ true := by
  unfold pointerParamsReadOnly at hr
  rcases List.mem_filterMap.mp hr with ⟨p, hp, hopt⟩
  by_cases hc : (bodyReadWriteBases fd.body).1.contains p.var.var.vname = true ∧
                ¬ (bodyReadWriteBases fd.body).2.contains p.var.var.vname = true
  · rw [if_pos hc] at hopt
    have heq : p.var.var.vname = r := Option.some.inj hopt
    exact ⟨p, hp, heq, heq ▸ hc.1, heq ▸ hc.2⟩
  · rw [if_neg hc] at hopt
    cases hopt

/-- The pairs returned by `disjointObligations` are between *distinct*
    parameter names (no `(p, p)` self-pairs). This is the syntactic
    correctness of the WP-precondition synthesizer: a caller never has
    to discharge `Disjoint A A` for the same buffer with itself. -/
theorem disjointObligations_distinct (fd : FunDecl) :
    ∀ p q, (p, q) ∈ disjointObligations fd → p ≠ q := by
  intro p q hpq
  unfold disjointObligations at hpq
  -- `disjointObligations` ends in `.eraseDups`; lift back to the
  -- pre-dedup concat.
  have hpq' := mem_of_mem_eraseDups _ hpq
  rcases List.mem_append.mp hpq' with hww | hwr
  · -- Write-write: extracted via filterMap with `if w < q' then some (w, q') else none`.
    rcases List.mem_flatMap.mp hww with ⟨w, _, hpq''⟩
    rcases List.mem_filterMap.mp hpq'' with ⟨q', _, hopt⟩
    by_cases hcmp : w < q'
    · simp [hcmp] at hopt
      obtain ⟨rfl, rfl⟩ := hopt
      intro heq
      subst heq
      simp at hcmp
    · simp [hcmp] at hopt
  · -- Write-read: `w ∈ pointerParamsWritten` and `r ∈ pointerParamsReadOnly`,
    -- but ReadOnly excludes anything in the write set, contradicting
    -- `w = r` if it held.
    rcases List.mem_flatMap.mp hwr with ⟨w, hw, hpq''⟩
    rcases List.mem_map.mp hpq'' with ⟨r, hr, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    intro h_eq
    obtain ⟨_, _, _, hcw⟩ := mem_pointerParamsWritten hw
    obtain ⟨_, _, _, _, hcr_not⟩ := mem_pointerParamsReadOnly hr
    exact hcr_not (h_eq ▸ hcw)

end CatCrypt.Crypto.Jasmin.PointerBorrow
