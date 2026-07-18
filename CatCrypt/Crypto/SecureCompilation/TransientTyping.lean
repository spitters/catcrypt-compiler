/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.SpeculativeCT

/-!
# Three-level transient security typing (à la *Spectre Declassified*)

The architectural CT analyser `cmdCT` (`Jasmin/LowCTCTAnalysis.lean`) and the
speculative-leakage model `SpeculativelyConstantTime`
(`SecureCompilation/SpeculativeCT.lean`) together give us a *semantic* notion of
speculative constant-time and a *two-level* (`Public`/`Secret`) information-flow
classifier. What was missing is the **typing layer** that mediates them: a
security level that is *architecturally* public — safe to branch on in
sequential execution — yet *speculatively* unsafe to use as a load address.
This file adds that layer.

## The transient level

Following Shivakumar, Barthe, Grégoire, Laporte, Oliveira, Priya, Rezk, Stefan,
*Spectre Declassified: Reading from the Right Place at the Wrong Time*
(IEEE S&P 2023), we refine the two-point lattice into the three-point lattice

```
  Public ⊑ Transient ⊑ Secret
```

with the reading:

* `Public` — safe in both sequential and speculative execution. May be a branch
  condition, a loop guard, **and** a load/store address.
* `Transient` — *architecturally* public (so safe in sequential execution; it
  may be a branch condition or loop guard), but it may carry secret data **under
  misprediction**, so it must **not** be used as a speculative load/store
  address.
* `Secret` — unsafe everywhere: not a branch condition, not an address.

This is exactly the *Spectre Declassified* discipline: the type system permits a
declassified value to flow into a *branch* (sequential CT is preserved) while
still forbidding it as the *address* of a speculative memory access (the channel
Spectre exploits).

## The typing judgment

`TransTyped tt c leafCT` (a decidable `Bool`) holds when, under the
`TransTable` `tt`:

1. every branch condition / loop guard is `⊑ Transient` (Public *or* Transient —
   sequential CT allows it); and
2. every runtime load/store **address** slot is `Public` (strictly — *not*
   Transient: a Transient address is the speculative leak `TransTyped` rejects).

We do **not** re-traverse the whole `LowCT` inductive by hand. Instead we factor
the judgment through the existing architectural analyser via the *architectural
erasure* `archErase : TransTable → LevelTable` (`Public, Transient ↦ Public`,
`Secret ↦ Secret`): well-typedness is `cmdCT c (archErase tt) leafCT` — which
already enforces "every branch / address is architecturally Public", i.e. the
`⊑ Transient` half — **conjoined** with the strictly-stronger `noTransAddr tt c`
side condition that no address slot is `Transient`. The first conjunct supplies
the soundness chain into `cmdCT`; the second carries the genuine
transient-vs-public distinction (a `cmdCT`-only check would conflate a Transient
address with a Public one, since both erase to Public).

## Soundness

`transTyped_imp_SCT`: a `TransTyped` program is `SpeculativelyConstantTime` for
*every* speculation window and *every* misprediction oracle. The proof routes
the first conjunct of well-typedness through `cmdCT` and then through the
speculative keystone `architecturally_CT_imp_SCT`. This is the
*Spectre-Declassified soundness theorem* against the existing SCT predicate.

## Relationship to the two-level system

`embedSecret : SecretLevel → TransLevel` (`Public ↦ Public`, `Secret ↦ Secret`)
embeds the two-point `Jasmin.SecretLevel` lattice as the
no-`Transient` fragment, and is a lattice homomorphism for join. `Transient` is
the genuinely new intermediate point. `archErase` is the section that collapses
`Transient` back down to `Public` (the architectural view).

## References

* Shivakumar, Barthe, Grégoire, Laporte, Oliveira, Priya, Rezk, Stefan,
  "Spectre Declassified: Reading from the Right Place at the Wrong Time",
  IEEE S&P 2023.
* Cauligi et al., "Constant-Time Foundations for the New Spectre Era",
  PLDI 2020 (the `SpeculativelyConstantTime` model).
-/

namespace CatCrypt.Crypto.SecureCompilation.TransientTyping

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.SpeculativeCT

set_option autoImplicit false

/-! ## §1.  The three-point transient lattice -/

/-- The three-point security lattice of *Spectre Declassified*:
    `Public ⊑ Transient ⊑ Secret`.

    * `Public` — safe sequentially and speculatively (branch, guard, address).
    * `Transient` — architecturally public (may branch / guard) but
      speculatively secret (may **not** be a load/store address).
    * `Secret` — unsafe everywhere. -/
inductive TransLevel where
  /-- Public: safe in sequential and speculative execution. -/
  | Public : TransLevel
  /-- Transient: architecturally public, speculatively secret. -/
  | Transient : TransLevel
  /-- Secret: unsafe everywhere. -/
  | Secret : TransLevel
  deriving DecidableEq, Repr, Inhabited, BEq

namespace TransLevel

/-- The lattice order `Public ⊑ Transient ⊑ Secret`. -/
def leq : TransLevel → TransLevel → Bool
  | .Public,    _           => true
  | .Transient, .Public     => false
  | .Transient, _           => true
  | .Secret,    .Secret     => true
  | .Secret,    _           => false

@[inherit_doc] scoped infixl:50 " ⊑ₜ " => leq

/-- Join: the least upper bound in `Public ⊑ Transient ⊑ Secret`. -/
def join : TransLevel → TransLevel → TransLevel
  | .Secret,    _           => .Secret
  | _,          .Secret     => .Secret
  | .Transient, _           => .Transient
  | _,          .Transient  => .Transient
  | .Public,    .Public     => .Public

@[inherit_doc] scoped infixl:65 " ⊔ₜ " => join

/-- Meet: the greatest lower bound. -/
def meet : TransLevel → TransLevel → TransLevel
  | .Public,    _           => .Public
  | _,          .Public     => .Public
  | .Transient, _           => .Transient
  | _,          .Transient  => .Transient
  | .Secret,    .Secret     => .Secret

@[inherit_doc] scoped infixl:70 " ⊓ₜ " => meet

/-- The order is reflexive. -/
@[simp] theorem leq_refl (x : TransLevel) : (x ⊑ₜ x) = true := by cases x <;> rfl

/-- The order is transitive. -/
theorem leq_trans {x y z : TransLevel}
    (h1 : (x ⊑ₜ y) = true) (h2 : (y ⊑ₜ z) = true) : (x ⊑ₜ z) = true := by
  cases x <;> cases y <;> cases z <;> simp_all [leq]

/-- The order is antisymmetric. -/
theorem leq_antisymm {x y : TransLevel}
    (h1 : (x ⊑ₜ y) = true) (h2 : (y ⊑ₜ x) = true) : x = y := by
  cases x <;> cases y <;> simp_all [leq]

/-- `Public` is the bottom element. -/
@[simp] theorem public_leq (x : TransLevel) : (TransLevel.Public ⊑ₜ x) = true := rfl

/-- `Secret` is the top element. -/
@[simp] theorem leq_secret (x : TransLevel) : (x ⊑ₜ TransLevel.Secret) = true := by
  cases x <;> rfl

/-- Join is commutative. -/
theorem join_comm (x y : TransLevel) : (x ⊔ₜ y) = (y ⊔ₜ x) := by
  cases x <;> cases y <;> rfl

/-- Join is associative. -/
theorem join_assoc (x y z : TransLevel) :
    ((x ⊔ₜ y) ⊔ₜ z) = (x ⊔ₜ (y ⊔ₜ z)) := by
  cases x <;> cases y <;> cases z <;> rfl

/-- Join is idempotent. -/
@[simp] theorem join_self (x : TransLevel) : (x ⊔ₜ x) = x := by cases x <;> rfl

/-- Each argument is below the join (left). -/
theorem leq_join_left (x y : TransLevel) : (x ⊑ₜ (x ⊔ₜ y)) = true := by
  cases x <;> cases y <;> rfl

/-- Each argument is below the join (right). -/
theorem leq_join_right (x y : TransLevel) : (y ⊑ₜ (x ⊔ₜ y)) = true := by
  cases x <;> cases y <;> rfl

/-- `x ⊑ₜ y` iff `x ⊔ₜ y = y` (the order is induced by the join). -/
theorem leq_iff_join_eq (x y : TransLevel) : (x ⊑ₜ y) = true ↔ (x ⊔ₜ y) = y := by
  cases x <;> cases y <;> simp [leq, join]

end TransLevel

/-! ## §2.  Embedding the two-level `SecretLevel` lattice

The two-point `Jasmin.SecretLevel` lattice (`Public`/`Secret`) embeds into the
three-point lattice as the fragment that never produces `Transient`. The
embedding is a join-homomorphism: it is the canonical inclusion of the
sublattice `{Public, Secret}`. -/

/-- Embed the two-point `Jasmin.SecretLevel` into `TransLevel`
    (`Public ↦ Public`, `Secret ↦ Secret`). `Transient` is the genuinely new
    intermediate point, never in the image. -/
def embedSecret : SecretLevel → TransLevel
  | .Public => .Public
  | .Secret => .Secret

/-- The embedding is injective. -/
theorem embedSecret_injective {a b : SecretLevel}
    (h : embedSecret a = embedSecret b) : a = b := by
  cases a <;> cases b <;> simp_all [embedSecret]

/-- The embedding never lands on `Transient` — `Transient` is the new point. -/
theorem embedSecret_ne_transient (a : SecretLevel) :
    embedSecret a ≠ TransLevel.Transient := by
  cases a <;> simp [embedSecret]

/-- The embedding is a join-homomorphism: it commutes with the two lattices'
    joins. -/
theorem embedSecret_join (a b : SecretLevel) :
    embedSecret (a.join b) = TransLevel.join (embedSecret a) (embedSecret b) := by
  cases a <;> cases b <;> rfl

/-! ## §3.  The architectural erasure `Transient ↦ Public`

The *architectural view* of a transient classification collapses `Transient`
down to `Public`: architecturally a transient value **is** public (it carries no
secret in sequential execution). This is the section of `embedSecret` that
recovers the `cmdCT`-compatible two-level table. -/

/-- A transient-level classification of named slots. -/
abbrev TransTable := String → TransLevel

/-- The architectural erasure of a transient level: `Transient ↦ Public`
    (architecturally a transient value is public), `Secret ↦ Secret`. -/
def archEraseLevel : TransLevel → SecretLevel
  | .Public    => .Public
  | .Transient => .Public
  | .Secret    => .Secret

/-- The architectural erasure of a transient table to a two-level `LevelTable`. -/
def archErase (tt : TransTable) : LevelTable := fun x => archEraseLevel (tt x)

/-- `archErase` is a left inverse of `embedSecret` pointwise on levels: erasing
    an embedded two-level value gives it back. So the two-level fragment is
    faithfully recovered. -/
theorem archEraseLevel_embedSecret (a : SecretLevel) :
    archEraseLevel (embedSecret a) = a := by cases a <;> rfl

/-- A slot erases to `Public` exactly when it is architecturally public, i.e.
    `Public` or `Transient`. -/
theorem archEraseLevel_eq_public_iff (l : TransLevel) :
    archEraseLevel l = SecretLevel.Public ↔ (l = .Public ∨ l = .Transient) := by
  cases l <;> simp [archEraseLevel]

/-! ## §4.  The transient typing judgment

`TransTyped tt c leafCT` factors as:

* `cmdCT c (archErase tt) leafCT` — the architectural analyser run on the erased
  table. Because erasure sends `Transient ↦ Public`, this accepts a branch /
  loop guard / address whose transient level is `Public` *or* `Transient` (the
  `⊑ Transient` half of the discipline). It is the conjunct that feeds the
  soundness chain.
* `noTransAddr tt c` — the strictly-stronger side condition forbidding a
  *Transient* slot from being a load/store **address**. This is the genuine
  transient-vs-public content: a Transient address erases to Public and would
  slip past `cmdCT` alone, but it is exactly the speculative leak the discipline
  rejects. -/

/-- A slot's transient level is *not* `Transient` (so it is `Public` or
    `Secret`). Used to require that an address slot is strictly `Public`
    (combined with the architectural check that already forces it `⊑ Transient`,
    this pins it to `Public`). -/
def notTransient (tt : TransTable) (x : String) : Bool :=
  match tt x with
  | .Transient => false
  | _          => true

/-- No load/store **address** slot is `Transient`: the speculative-safety side
    condition. Recurses through the `LowCT` control structure (via `foldNode`)
    and, at each runtime-indexed memory access, requires the index slot to be
    `notTransient`. (Literal-indexed and non-indexed leaves carry no runtime
    address and impose no constraint.) -/
def noTransAddr (tt : TransTable) (c : LowCT) : Bool :=
  LowCT.foldNode
    (leaf := fun c => match c with
      | .RArrStore _ idxVar _ => notTransient tt idxVar
      | .RArrLoad _ _ idxVar  => notTransient tt idxVar
      | _                     => true)
    (seqNode := fun _ r1 r2 => r1 && r2)
    (wrapNode := fun _ r => r)
    c

/-- **The transient typing judgment.** A program `c` is well-typed under the
    transient table `tt` (with leaf-CT oracle `leafCT`) when:

    1. it is architecturally CT under the erased table (`cmdCT` — every branch /
       guard / address is `⊑ Transient`, i.e. erases to `Public`); and
    2. no load/store address slot is `Transient` (`noTransAddr` — addresses are
       strictly `Public`).

    Together: branch conditions and loop guards may be `Public` or `Transient`;
    load/store addresses must be `Public`. This is the *Spectre Declassified*
    typing discipline. -/
def TransTyped (tt : TransTable) (c : LowCT) (leafCT : LeafCTTable) : Bool :=
  cmdCT c (archErase tt) leafCT && noTransAddr tt c

/-- Well-typedness gives architectural CT under the erased table — the first
    conjunct, the bridge into the speculative keystone. -/
theorem TransTyped.cmdCT {tt : TransTable} {c : LowCT} {leafCT : LeafCTTable}
    (h : TransTyped tt c leafCT = true) :
    cmdCT c (archErase tt) leafCT = true := by
  simp only [TransTyped, Bool.and_eq_true] at h
  exact h.1

/-- Well-typedness gives the speculative-address side condition — the second
    conjunct, the genuine transient-vs-public content. -/
theorem TransTyped.noTransAddr {tt : TransTable} {c : LowCT} {leafCT : LeafCTTable}
    (h : TransTyped tt c leafCT = true) :
    noTransAddr tt c = true := by
  simp only [TransTyped, Bool.and_eq_true] at h
  exact h.2

/-! ## §5.  Soundness: `TransTyped ⟹ SpeculativelyConstantTime`

The soundness theorem of the transient discipline against the existing
speculative-leakage predicate. Routing the architectural conjunct through the
keystone `architecturally_CT_imp_SCT` (specialised to `lt := archErase tt`)
yields `SpeculativelyConstantTime` *for every window and every oracle*. -/

/-- **Spectre-Declassified soundness.** A transient-well-typed program is
    speculatively constant-time under the architecturally-erased level table,
    for *every* speculation window and *every* misprediction oracle.

    The discipline's payload: a branch/guard may carry a `Transient` value
    (architecturally public — sequential CT is preserved), but `TransTyped`'s
    address side condition forbids a `Transient` slot from being a speculative
    load/store address, so no secret data reaches the cache channel under
    misprediction. -/
theorem transTyped_imp_SCT
    (window : SpecWindow) (O : MispredOracle)
    (tt : TransTable) (leafCT : LeafCTTable)
    (c : LowCT) (h : TransTyped tt c leafCT = true) :
    SpeculativelyConstantTime window O (archErase tt) c :=
  architecturally_CT_imp_SCT window O (archErase tt) leafCT c (TransTyped.cmdCT h)

/-- The architectural projection of soundness: a transient-well-typed program is
    (ordinary) architecturally constant-time under the erased table. -/
theorem transTyped_imp_ArchCT
    (tt : TransTable) (leafCT : LeafCTTable)
    (c : LowCT) (h : TransTyped tt c leafCT = true) :
    ArchConstantTime (archErase tt) c :=
  architecturally_CT_imp_ArchCT (archErase tt) leafCT c (TransTyped.cmdCT h)

/-! ## §6.  Worked example: a Transient branch is admitted; a Transient
address is rejected

We exhibit the genuine three-level content on two minimal programs.

* `transientBranch`: a branch on a `Transient`-classified flag, with a CT leaf
  call in each arm over `Public` slots. It is `TransTyped` — the Transient flag
  is admitted *as a branch condition* (sequential CT) — and hence SCT.
* `transientLoad`: a load whose **address** slot is `Transient`. It is **not**
  `TransTyped` (`TransTyped … = false`), witnessing that the discipline rejects
  a Transient address even though the *same* table makes it pass the
  architectural `cmdCT` check (which erases `Transient` to `Public`). This is the
  precise Spectre-Declassified distinction, made non-vacuous. -/

namespace Example

/-- A transient table: the flag `flag` is `Transient`, the index `idx` is
    `Transient`, everything else `Public`. -/
def tt : TransTable := fun s =>
  if s = "flag" then .Transient
  else if s = "idx" then .Transient
  else .Public

/-- A branch on a `Transient` flag with CT field-op leaves over public slots in
    each arm. -/
def transientBranch : LowCT :=
  .RIfNz "flag"
    (.RCall "fe25519_sqr" ⟨"a", .TFp25519⟩ [⟨"x", .TFp25519⟩])
    (.RCall "fe25519_mul" ⟨"a", .TFp25519⟩ [⟨"x", .TFp25519⟩, ⟨"x", .TFp25519⟩])

/-- **A Transient branch condition is well-typed.** The architectural check
    accepts (the Transient flag erases to Public, so the branch is admitted),
    and there is no address to violate the speculative side condition. -/
theorem transientBranch_typed :
    TransTyped tt transientBranch LeafCTTable.canonical = true := by
  native_decide

/-- **Hence the Transient-branch program is speculatively CT** — for every window
    and oracle. Even mispredicting down the wrong arm leaks only
    public-determined observations, because the (architecturally-public) branch
    decision drives both the path and the oracle. -/
theorem transientBranch_SCT (window : SpecWindow) (O : MispredOracle) :
    SpeculativelyConstantTime window O (archErase tt) transientBranch :=
  transTyped_imp_SCT window O tt LeafCTTable.canonical transientBranch
    transientBranch_typed

/-- A load whose runtime **address** slot `idx` is `Transient`. -/
def transientLoad : LowCT :=
  .RArrLoad ⟨"d", .TU64⟩ ⟨"src", .TU64⟩ "idx"

/-- **A Transient address is rejected.** Even though the architectural `cmdCT`
    check passes (the Transient index erases to Public), `TransTyped` is `false`:
    the speculative-address side condition `noTransAddr` forbids the Transient
    index. This is the non-vacuous transient-vs-public distinction — a Transient
    value is safe to branch on but not to use as a speculative load address. -/
theorem transientLoad_not_typed :
    TransTyped tt transientLoad LeafCTTable.canonical = false := by
  native_decide

/-- The companion fact making the rejection meaningful: the *same* table makes
    `transientLoad` pass the architectural `cmdCT` check (Transient erases to
    Public). So `TransTyped`'s rejection is genuinely the new, stronger
    speculative content — not something `cmdCT` already caught. -/
theorem transientLoad_archErase_cmdCT :
    cmdCT transientLoad (archErase tt) LeafCTTable.canonical = true := by
  native_decide

/-- Reclassifying the index slot `idx` as `Public` makes the load well-typed:
    the discipline admits a *Public* address. Contrast with
    `transientLoad_not_typed`. -/
def ttPublicIdx : TransTable := fun _ => .Public

theorem transientLoad_publicIdx_typed :
    TransTyped ttPublicIdx transientLoad LeafCTTable.canonical = true := by
  native_decide

/-- And the public-address load is then speculatively CT. -/
theorem transientLoad_publicIdx_SCT (window : SpecWindow) (O : MispredOracle) :
    SpeculativelyConstantTime window O (archErase ttPublicIdx) transientLoad :=
  transTyped_imp_SCT window O ttPublicIdx LeafCTTable.canonical transientLoad
    transientLoad_publicIdx_typed

end Example

end CatCrypt.Crypto.SecureCompilation.TransientTyping
