/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote


@[expose] public section
set_option autoImplicit false

/-!
# Whole-program denote for the data-dependent CONDITIONAL-side-effect region

`TranslateDialectDirectControl`'s `RIfNz` arm is a **φ-merge**: the guard chooses
between two *values* (case (C′): both branches a same-name `RScalarSet`, fused to
a `cmov`), and for every other shape the front passes through one branch's prefix
or re-translates the other — the emitted `catCryptDialect` `Com` runs `then` (and
`else`) **unconditionally** (there is no `Lcond`/label node in the dialect).
`semScalar`'s `RIfNz` arm mirrors that: the (C-otherwise) case denotes
`then; else` **unconditionally** (`TranslateDialectScalarDenote`, ~line 560).

So a `then`-branch that CALLS a function or WRITES state — the observe/sample
trigger `if inlen == 8 { call duplex; store … }` — has **no** faithful waist
model at the `semScalar` level: the φ-merge runs it always, which denotes WRONG
when the guard is false.  The genuine forward branch lives only at the raw `Lcmd`
layer (`QuerySampleBranchFront.condSkip` = `CMP ; Lcond ; <then> ; label`), which
runs its `then` band **iff** the guard holds — but that `Lcmd`-layer branch has
no `semScalar`-waist denote.

This sidecar closes that gap the SAME way `TranslateDialectWhileDenote` closed
the `RWhileNz` waist (semScalar-had-no-arm → add the missing control model): it
adds the **guarded-execution** waist model that `semScalar`'s φ-merge does not
capture, together with the front descent that denotes it — the conditional twin
of `semScalarWhile` / `loopWhileD` / `rWhileNz_whole_denote`:

* `semScalarCond semBody guard` — the **guard-gated do-once** waist model
  (`SEnvScalar` twin of `condSkip`'s run-`then`-iff-guard): run the block iff the
  guard is nonzero on the entry env, else IDENTITY (`env ↦ env`).  This is the
  model `semScalar`'s (C-otherwise) `RIfNz` arm LACKS — it runs `then`
  unconditionally;
* `condSkipD translateBody vm` — the **guard-indexed** front descent (the
  `loopWhileD` twin at trip ∈ {0,1}): `true ↦` the block descent
  (`translateDialectControl vm thenBlk`), `false ↦` the identity descent
  (`Γ' = Γ`, `cont = ComCont.id`, `vm` unchanged) — the skipped-block invariant;
* `condSkipD_denote` — the descent homomorphism **by case analysis on the guard
  value** (`true` → block denote via the body IH on the `IsCoveredSCtl` block;
  `false` → the identity denote, the block does NOT run), NOT unconditional
  `then; else`;
* `IsCoveredSCond` — the sidecar coverage predicate (`rCond`: a guarded block
  `RIfNz name thenBlk RSkip` over an `IsCoveredSCtl` `thenBlk`);
* `rCond_whole_denote` — the whole-program conditional denote: the front descent
  gated on the run's actual guard value denotes exactly the guard-gated
  do-once semantics, over any `IsCoveredSCtl` block, with the body's preservation
  homomorphism `translateDialectControl_denote_ctl`.

The guard is data-dependent (fixed at run time by the entry env), so — like the
while trip count — the descent is parameterised by the guard boolean read off the
run, and the denote holds per-value by the case split.  The `false` leg is the
key non-vacuity: the block's side effect (the call/store) does NOT run and the
descent is the identity, so the denote is env-preserving.

**0 sorries; no axioms beyond the front's existing set.**
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. The guard-gated do-once waist model `semScalarCond`

The `SEnvScalar` twin of the `Lcmd`-layer `condSkip` (`CMP ; Lcond ; <then> ;
label`): the `then` block runs **iff** the guard holds on the entry env, else the
env is left untouched (the label is reached with no block).  This is precisely
the waist model `semScalar`'s φ-merge `RIfNz` arm does not provide — that arm runs
`then` unconditionally in the (C-otherwise) case. -/

/-- Guard-gated do-once over `SEnvScalar` (the `condSkip` waist twin).  Runs
    `semBody` iff `guard` is nonzero on the entry env; otherwise IDENTITY.  The
    `false` leg leaves `env` untouched — the block's side effect does not fire. -/
def semScalarCond (semBody : SEnvScalar → Option SEnvScalar) (guard : SEnvScalar → Bool)
    (env : SEnvScalar) : Option SEnvScalar :=
  bif guard env then semBody env else some env

/-- The guard-false leg of `semScalarCond` is the identity: a skipped conditional
    leaves the environment untouched (the block does NOT run).  The key
    non-vacuity fact — distinguishes the genuine forward branch from the φ-merge
    that would run `then` regardless. -/
@[simp] theorem semScalarCond_false (semBody : SEnvScalar → Option SEnvScalar)
    (guard : SEnvScalar → Bool) (env : SEnvScalar) (hg : guard env = false) :
    semScalarCond semBody guard env = some env := by
  simp only [semScalarCond, hg, cond_false]

/-- The guard-true leg of `semScalarCond` runs the block. -/
@[simp] theorem semScalarCond_true (semBody : SEnvScalar → Option SEnvScalar)
    (guard : SEnvScalar → Bool) (env : SEnvScalar) (hg : guard env = true) :
    semScalarCond semBody guard env = semBody env := by
  simp only [semScalarCond, hg, cond_true]

/-! ## 2. The guard-indexed front descent `condSkipD`

The `loopWhileD` twin at trip ∈ {0, 1}: the guarded block either descends once
(`true`) or not at all (`false`, the identity descent — the skipped-block
invariant, exactly the loop-region `Γ' = Γ`, `cont = ComCont.id`, `vm` unchanged
that `translateDialectControl`'s `RWhileNz` arm returns).  As in `loopWhileD`, the
body translator `translateBody` is passed in. -/

/-- Guard-indexed dialect descent for a guarded block.  `true ↦` the block
    descent; `false ↦` the identity descent (the skipped-block invariant).
    `CProg`-free. -/
def condSkipD {Γ : Ctx}
    (translateBody : VarMap Γ → Option (DTransOut Γ))
    (vm : VarMap Γ) : Bool → Option (DTransOut Γ)
  | false => some { Γ' := Γ, cont := ComCont.id, vm := vm }
  | true => translateBody vm

/-! ## 3. The guard-case denote (the deliverable) -/

/-- **Guard-case denote for the conditional region** (the `loopWhileD_denote`
    twin, but by case analysis on the guard value rather than induction on a trip
    index).  For the guard value `b` read off the run: when `b = true` the front
    descent is the block descent and denotes the block's `semScalar` waist (via
    the body preservation homomorphism `ihBody`, the coverage IH); when `b =
    false` the front descent is the identity and the run is env-preserving, so the
    denote is the identity homomorphism (the block does NOT run — the key
    non-vacuity).  NOT unconditional `then; else`. -/
theorem condSkipD_denote (body : LowCT)
    (ihBody : ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm body = some o →
      semScalar body env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V') :
    ∀ (b : Bool) {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      condSkipD (translateBody := fun vm' => translateDialectControl vm' body) vm b = some o →
      (bif b then semScalar body env else some env) = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro b
  cases b with
  | false =>
      -- Guard false: the descent is the identity and the run is env-preserving.
      intro Γ vm V env env' o hc htr hsem
      simp only [condSkipD] at htr
      simp only [cond_false] at hsem
      obtain rfl := Option.some.inj htr
      obtain rfl := Option.some.inj hsem
      exact ⟨V, hc, fun tail => ⟨tail, rfl, rfl⟩⟩
  | true =>
      -- Guard true: the descent is the block descent; delegate to the body IH.
      intro Γ vm V env env' o hc htr hsem
      simp only [condSkipD] at htr
      simp only [cond_true] at hsem
      exact ihBody vm V env env' o hc htr hsem

/-- **Generic guard-case denote — the `rCond`-on-`IsCoveredSU` lift.**  The
    conditional applies its block only ONCE, and at the ENTRY env (the guard reads
    the entry env, and if it holds the block runs on that same entry env), so no
    per-trip env threading is needed: it suffices to supply the block's descent
    `transBody` and semantics `semBody` at the entry env, with the body
    preservation homomorphism `ihBody` (the unified coverage IH) at that env.
    Because `ihBody` is abstract, the block may be ANY covered shape (an
    `RSeq`/`RWhileNz`/nested `RCond`), not only an `IsCoveredSCtl` leaf — the
    lift that turns `condSkipD_denote`'s `IsCoveredSCtl` body into a full
    `IsCoveredSU` body. -/
theorem condSkipDEnv_denote {Γ0 : Ctx}
    (transBody : VarMap Γ0 → Option (DTransOut Γ0))
    (semBody : SEnvScalar → Option SEnvScalar)
    (vm : VarMap Γ0) (V : Ctxt.Valuation (d := catCryptDialect) Γ0) (env : SEnvScalar)
    (hc : ConsistentS vm V env)
    (ihBody : ∀ (env' : SEnvScalar) (o : DTransOut Γ0),
      transBody vm = some o →
      semBody env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V') :
    ∀ (b : Bool) (env' : SEnvScalar) (o : DTransOut Γ0),
      condSkipD (translateBody := transBody) vm b = some o →
      (bif b then semBody env else some env) = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro b
  cases b with
  | false =>
      intro env' o htr hsem
      simp only [condSkipD] at htr
      simp only [cond_false] at hsem
      obtain rfl := Option.some.inj htr
      obtain rfl := Option.some.inj hsem
      exact ⟨V, hc, fun tail => ⟨tail, rfl, rfl⟩⟩
  | true =>
      intro env' o htr hsem
      simp only [condSkipD] at htr
      simp only [cond_true] at hsem
      exact ihBody env' o htr hsem

/-! ## 4. The whole-program conditional denote + coverage predicate -/

/-- The control-extended covered fragment extended with the data-dependent
    guarded-execution region: a guarded block `RIfNz name thenBlk RSkip` (`if
    name != 0 then thenBlk`, no else) over an `IsCoveredSCtl` `thenBlk`.  Sidecar
    predicate (the `SeqExt`/guarded pattern) — the core `IsCoveredSCtl` inductive
    that the compiler-correctness headline's simulation consumes is untouched. -/
inductive IsCoveredSCond : LowCT → Prop
  | rCond {name : String} {thenBlk : LowCT} :
      IsCoveredSCtl thenBlk → IsCoveredSCond (.RIfNz name thenBlk .RSkip)

/-- **Whole-program conditional denote** (the guard-case denote instantiated at
    the run's actual guard value).  For a guard-gated do-once over an
    `IsCoveredSCtl` block, the front descent gated on the run's guard value
    denotes exactly the guard-gated do-once semantics.  `guard` is the guarded
    block's predicate (`name != 0`); the body's preservation homomorphism is
    `translateDialectControl_denote_ctl`. -/
theorem rCond_whole_denote {thenBlk : LowCT} (hcov : IsCoveredSCtl thenBlk)
    (guard : SEnvScalar → Bool)
    {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (o : DTransOut Γ)
    (hc : ConsistentS vm V env)
    (htr : condSkipD (translateBody := fun vm' => translateDialectControl vm' thenBlk)
      vm (guard env) = some o)
    (hrun : semScalarCond (fun e => semScalar thenBlk e) guard env = some env') :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
      ConsistentS o.vm V' env' ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
        ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  apply condSkipD_denote thenBlk
    (fun vm V env env' o hc ht hs => translateDialectControl_denote_ctl hcov vm V env env' o hc ht hs)
    (guard env) vm V env env' o hc htr
  simpa only [semScalarCond] using hrun

/-! ## 5. Worked witnesses -/

/-- A data-dependent guarded call+store — the observe/sample trigger `if g then
    call leaf; store` — over a covered block is conditional-covered. -/
example :
    IsCoveredSCond (.RIfNz "inlen"
      (.RSeq (.RCall "duplex" ⟨"st", .TU64⟩ [])
        (.RArrStore ⟨"buf", .TU64⟩ "i" ⟨"v", .TU64⟩)) .RSkip) :=
  .rCond (.ofStraight (.rSeq (.rCall _ _ _) (.rArrStore _ _ _)))

/-- The **guard-indexed descent** front-compiles on the block side (`true`): the
    guarded leaf call — the side-effecting `then` of the observe trigger —
    descends `CProg`-free. -/
example :
    (condSkipD (translateBody := fun vm' => translateDialectControl vm'
        (.RCall "duplex" ⟨"st", .TU64⟩ []))
      (Γ := []) VarMap.empty true).isSome := by native_decide

/-- The guard-indexed descent on the skip side (`false`) is the identity
    descent — always `isSome`, independent of the block. -/
example :
    (condSkipD (translateBody := fun vm' => translateDialectControl vm'
        (.RCall "duplex" ⟨"st", .TU64⟩ []))
      (Γ := []) VarMap.empty false).isSome := by native_decide

/-- **The g = 0 identity (the key non-vacuity).**  A concrete guard-gated
    call+store whose guard `inlen != 0` is FALSE (the entry env has `inlen = 0`):
    the block's side effect (the call and the store) does NOT run, and the
    guard-gated semantics is the IDENTITY — the environment is returned unchanged.
    This is exactly what `semScalar`'s φ-merge `RIfNz` arm would get WRONG (it
    would run `then` regardless of the guard).  The guard's Bool value on the
    entry env is `false` (`native_decide`); `semScalarCond_false` then collapses
    the do-once to the identity. -/
example :
    semScalarCond
      (fun e => semScalar (.RSeq (.RCall "duplex" ⟨"st", .TU64⟩ [])
        (.RArrStore ⟨"buf", .TU64⟩ "i" ⟨"v", .TU64⟩)) e)
      (fun e => decide ((envReadU64 e "inlen").getD 0 ≠ 0))
      (SEnvScalar.upd (fun _ => none) "inlen" (t := .sword 64) (0 : BitVec 64))
      = some (SEnvScalar.upd (fun _ => none) "inlen" (t := .sword 64) (0 : BitVec 64)) :=
  semScalarCond_false _ _ _ (by native_decide)

/-- The dual: when the guard `inlen != 0` is TRUE (`inlen = 8`, the observe
    trigger), the guarded block DOES run — the do-once semantics is the block's
    `semScalar`, not the identity. -/
example :
    semScalarCond
      (fun e => semScalar (.RCall "duplex" ⟨"st", .TU64⟩ []) e)
      (fun e => decide ((envReadU64 e "inlen").getD 0 ≠ 0))
      (SEnvScalar.upd (fun _ => none) "inlen" (t := .sword 64) (8 : BitVec 64))
      = semScalar (.RCall "duplex" ⟨"st", .TU64⟩ [])
          (SEnvScalar.upd (fun _ => none) "inlen" (t := .sword 64) (8 : BitVec 64)) :=
  semScalarCond_true _ _ _ (by native_decide)

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
