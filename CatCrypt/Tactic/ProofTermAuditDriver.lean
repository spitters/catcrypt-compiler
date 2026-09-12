/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto
import CatCrypt.Tactic.ProofTermAudit

/-!
# `proofaudit` — batch proof-term shell detector (driver)

The `lake exe proofaudit` executable. It loads the full `CatCrypt.Crypto`
environment, enumerates every security theorem (declarations whose name
ends in a canonical UC/security suffix), runs the machine-checked
`ProofTermAudit.tagsFor` tagger on each, and prints a report.

Two kinds of finding are surfaced (cf. INCREMENT 1 of #220):

* **Potential undocumented shell** — the proof term carries a shell tag
  (`vacuous_body` / `returns_assumption` / `trivial_constructor`) **and**
  the docstring does NOT carry an honest `(composition plumbing)` /
  `sdist_self` marker. The body is content-free but nothing in the
  docstring admits it.

* **Docstring/body mismatch** — the docstring lacks a trivial-lift tag
  (so it implicitly claims a substantive result) yet the body is
  `vacuous_body` / `returns_assumption`. This is the
  `feedback_no_genuine_reduction` failure mode, now machine-checked.

A theorem tagged `(composition plumbing)` / `sdist_self` whose
body is a trivial lift is **not** flagged — it is correctly documented.

Exit code is always 0: this increment *reports*, it does not gate (the
task forbids mass-rewrites). The textual report is consumed by
`scripts/audit_security.lean`, which echoes it under a dedicated section.

Run directly: `lake exe proofaudit`
-/

open Lean Meta CatCrypt.Tactic.ProofTermAudit

namespace CatCrypt.Tactic.ProofTermAudit.Driver

/-- Canonical security-theorem name suffixes to audit. -/
def securitySuffixes : Array String := #[
  "_uc_secure", "_e2e_uc_secure", "_uc_emulates", "_emulates",
  "_ki_security", "_uc_bound", "UCEmulates",
  -- Widened coverage: name-suffixed security theorems the earlier set missed.
  "_eufcma", "_unforge", "_security", "_uc_security",
  "_quantum_uc", "_binding", "_cca_security", "_ind_cpa",
  -- Further widening: the bare `_secure` / `_sound` / `_privacy` families
  -- (an `_eufcma`/`_secure`-named theorem was never inspected before).
  "_secure", "_sound", "_privacy",
  -- Hidden-substate concurrent-UC capstones (`UCEmulatesConcurrentStatefulHidden`).
  "_genuine_uc"
]

/-- Honest trivial-lift docstring markers (the "this is a lift" admission). -/
def honestLiftMarkers : Array String := #[
  "composition plumbing", "sdist_self",
  "concurrent UC via ITreeN", "concurrent UC via Kantorovich",
  "concurrent UC application"
]

/-- Does `name` end with one of the audited security suffixes? -/
def isSecurityName (name : Name) : Bool :=
  let s := name.toString
  securitySuffixes.any (fun suf => s.endsWith suf)

/-- Does `doc` carry an honest trivial-lift marker? -/
def docIsHonestLift (doc : String) : Bool :=
  honestLiftMarkers.any (fun m => (doc.splitOn m).length > 1)

/-- Strict reflexivity proof heads — those proving `x ≤ x` / `x = x`. A proof of
    `∃ ε, ε ≤ bound` discharged by one of these has taken the witness to be the
    bound itself (`⟨bound, le_refl _⟩` / `⟨0, rfl⟩`), so the existential proves
    nothing about the bound.

    Deliberately EXCLUDES `le_of_eq` / `Eq.le` / `ge_of_eq`: these prove `a ≤ b`
    from a possibly-substantive `a = b` (e.g. the perfect-UC-at-0 lift
    `⟨A, le_of_eq (sdist_self _)⟩`, which shows the advantage is exactly 0 because
    the real and ideal worlds coincide — a correct result, tagged as a
    composition lift). Only a `w ≤ w` / `w = w` reflexivity witnesses nothing.

    Written as a membership test rather than a `||` chain: this module's import
    closure reaches Iris, whose `Iris.Instances.Data` gives `||` the meaning of
    `Disjoint.disjoint`, so a boolean disjunction here elaborates against that
    class and fails to synthesize `Disjoint Name`. -/
def isReflexiveBoundHead (n : Name) : Bool :=
  [``le_refl, ``le_rfl, ``Eq.refl, ``rfl,
   ``Nat.le_refl, ``Nat.le.refl, ``Preorder.le_refl].contains n

/-- Is `n`'s proof term an existential witnessed by a value whose accompanying
    proof is pure reflexivity — `∃ ε, ε ≤ bound := ⟨bound, le_refl _⟩` (or
    `⟨0, rfl⟩`) — i.e. the witness IS the bound, discharging the existential by
    reflexivity and proving nothing?

    The core `trivial_constructor` tag misses this whenever the witness is a
    *binder* (the bound is a parameter): a binder flows into the constructor
    argument, so `countUsedBinders ≠ 0` and the tag does not fire. This detector
    keys on the second (proof) argument of `Exists.intro` being a reflexivity
    head instead. -/
def isExistsWitnessVacuous (n : Name) : MetaM Bool := do
  let env ← getEnv
  let some ci := env.find? n | return false
  let some val := ci.value? | return false
  let (_, body0) := stripLambdas val
  let body := body0.headBeta
  match body.getAppFn.constName? with
  | some cn =>
    if cn == ``Exists.intro then
      -- `Exists.intro {α} {p} (w) (h)` — the proof `h` is the last argument.
      match body.getAppArgs.back? with
      | some pf =>
        match pf.headBeta.getAppFn.constName? with
        | some pn => return isReflexiveBoundHead pn
        | none => return false
      | none => return false
    else return false
  | none => return false

/-- A single finding row. -/
structure Finding where
  name : Name
  tags : Array Tag
  /-- `true` ⇒ the docstring itself admits a trivial lift -/
  honest : Bool
  hasDoc : Bool
  deriving Inhabited

/-- Classify a finding for the report. -/
inductive Verdict where
  /-- statement type is itself vacuous (`custom_hypothesis_in_type`) while
      claiming a security result — no docstring tag can excuse this -/
  | vacuousStatement
  | undocumentedShell
  | docstringBodyMismatch
  | honestlyTaggedLift
  | clean
  deriving BEq

def Finding.verdict (f : Finding) : Verdict :=
  let shellTags := Tag.shellTags f.tags
  let typeVacuous := f.tags.contains Tag.customHypothesisInType
  if shellTags.isEmpty && !typeVacuous then
    .clean
  -- A vacuous statement (conclusion `True` / identity-implication type) with
  -- a content-free body is the worst case: it claims to be a security
  -- theorem (matched a security suffix) but proves nothing. The honest-lift
  -- docstring tag does NOT excuse it — the *type* says nothing.
  else if typeVacuous && !shellTags.isEmpty then
    .vacuousStatement
  else if shellTags.isEmpty then
    -- type-vacuous but body uses content (rare); treat as clean
    .clean
  else if f.honest then
    .honestlyTaggedLift
  else if !f.hasDoc then
    -- no docstring at all + content-free body
    .docstringBodyMismatch
  else
    .undocumentedShell

/-- Collect all audited security theorems in the environment, paired with
    their tags + docstring honesty. -/
def collectFindings : MetaM (Array Finding) := do
  let env ← getEnv
  let mut out : Array Finding := #[]
  for (nm, ci) in env.constants.toList do
    -- skip auto-generated / internal names and non-theorems
    if nm.isInternal then continue
    if !isSecurityName nm then continue
    -- only theorems / defs with an inspectable value
    match ci with
    | .thmInfo _ | .defnInfo _ =>
      let tags ← tagsFor nm
      let doc := (← findDocString? env nm).getD ""
      out := out.push {
        name := nm
        tags := tags
        honest := docIsHonestLift doc
        hasDoc := doc.length > 0
      }
    | _ => continue
  return out

/-- Render the report to stdout. Returns the counts
    `(vacuousStatement, undocumentedShell, mismatch, existsWitness)`. -/
def report : MetaM (Nat × Nat × Nat × Nat) := do
  let findings ← collectFindings
  let sorted := findings.qsort (fun a b => a.name.toString < b.name.toString)
  let mut vacuous : Array Finding := #[]
  let mut undoc : Array Finding := #[]
  let mut mismatch : Array Finding := #[]
  let mut honest : Array Finding := #[]
  let mut existsWit : Array Name := #[]
  let mut clean := 0
  for f in sorted do
    if (← isExistsWitnessVacuous f.name) then
      existsWit := existsWit.push f.name
    match f.verdict with
    | .vacuousStatement => vacuous := vacuous.push f
    | .undocumentedShell => undoc := undoc.push f
    | .docstringBodyMismatch => mismatch := mismatch.push f
    | .honestlyTaggedLift => honest := honest.push f
    | .clean => clean := clean + 1
  IO.println "═══════════════════════════════════════════"
  IO.println "  Proof-Term Shell Detector (machine-checked)"
  IO.println "═══════════════════════════════════════════"
  IO.println s!"  Security theorems audited:      {sorted.size}"
  IO.println s!"  Clean (substantive / non-shell): {clean}"
  IO.println s!"  Self-declared trivial lifts:    {honest.size}"
  IO.println s!"  Vacuous statements (True-typed): {vacuous.size}"
  IO.println s!"  Potential undocumented shells:  {undoc.size}"
  IO.println s!"  Docstring/body mismatches:      {mismatch.size}"
  IO.println s!"  Existential-witness vacuities:  {existsWit.size}"
  if vacuous.size > 0 then
    IO.println ""
    IO.println "  ❗❗ Vacuous statements (security-named, but type proves nothing):"
    for f in vacuous do
      IO.println s!"      {f.name}"
      IO.println s!"        tags: {String.intercalate ", " (f.tags.toList.map Tag.toString)}"
  if undoc.size > 0 then
    IO.println ""
    IO.println "  ⚠  Potential undocumented shells (content-free body, no honest tag):"
    for f in undoc do
      IO.println s!"      {f.name}"
      IO.println s!"        tags: {String.intercalate ", " (f.tags.toList.map Tag.toString)}"
  if mismatch.size > 0 then
    IO.println ""
    IO.println "  ❗ Docstring/body mismatches (implies substantive, but body is trivial):"
    for f in mismatch do
      IO.println s!"      {f.name}"
      IO.println s!"        tags: {String.intercalate ", " (f.tags.toList.map Tag.toString)}"
  if existsWit.size > 0 then
    IO.println ""
    IO.println "  ❗ Existential-witness vacuities (∃ ε, ε ≤ bound discharged by reflexivity):"
    for nm in existsWit do
      IO.println s!"      {nm}"
  if honest.size > 0 then
    IO.println ""
    IO.println "  ✓ Self-declared trivial lifts (correctly documented, not flagged):"
    for f in honest do
      IO.println s!"      {f.name}  [{String.intercalate ", " ((Tag.shellTags f.tags).toList.map Tag.toString)}]"
  return (vacuous.size, undoc.size, mismatch.size, existsWit.size)

end CatCrypt.Tactic.ProofTermAudit.Driver

open CatCrypt.Tactic.ProofTermAudit.Driver in
/-- Entry point for `lake exe proofaudit`. Always exits 0 (report-only;
    INCREMENT 1 does not gate). -/
unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  -- `importModules (loadExts := true)` requires initializer execution.
  Lean.enableInitializersExecution
  let env ← Lean.importModules
    #[{ module := `CatCrypt.Crypto }, { module := `CatCrypt.Tactic.ProofTermAudit }]
    {} (loadExts := true)
  -- Unlimited heartbeats: the tagger inspects whole-environment proof
  -- terms; some crypto declarations are large and would blow the default
  -- 200k limit during constant lookup. The tagger itself does no `whnf`.
  let coreCtx : Lean.Core.Context := {
    fileName := "<proofaudit>", fileMap := default
    maxHeartbeats := 0 }
  let coreState : Lean.Core.State := { env := env }
  let metaAction : Lean.Meta.MetaM (Nat × Nat × Nat × Nat) := report
  let coreAction : Lean.CoreM (Nat × Nat × Nat × Nat) := metaAction.run'
  let ((vacuous, shell, mismatch, existsWit), _) ← coreAction.toIO coreCtx coreState
  IO.println ""
  IO.println s!"  proofaudit summary: {vacuous} vacuous statement(s), \
{shell} undocumented shell(s), {mismatch} mismatch(es), \
{existsWit} existential-witness vacuit(ies)."
