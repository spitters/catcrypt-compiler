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
# Whole-program denote for the data-dependent `RWhileNz` loop region

`TranslateDialectDirectControl`'s `RWhileNz` arm is **context plumbing**: it
gates on the guard being a bound scalar and on the body front-compiling, then
returns the context-invariant `DTransOut` (`Γ' = Γ`, `cont = ComCont.id`, `vm`
unchanged).  The real run-time back-edge is emitted downstream at `Lcmd`
(`TranslateDialectDataWhile.rolledWhileNz` / `X86Backend.LprogControlFlow`),
whose denote realises A3's fuel-bounded do-while `runWhileMem`.  `semScalar`
has **no** `RWhileNz` arm (it hits `| _, _ => none`), so a whole-program denote
at the **`semScalar` waist** needs a separate loop model.

This sidecar supplies it the same way the counted loop is handled
(`loopRForD` / `loopRForD_denote`), but guard-driven and fuel-indexed:

* `semWhileIter semBody k` — the **unconditional `k`-fold** body iteration over
  `SEnvScalar` (the `RFor`-twin `semRForD` minus the counter const bind);
* `loopWhileD translateBody k` — the **`k`-fold-unrolled** `ComCont` descent
  (the `loopRForD` twin minus the counter const bind);
* `loopWhileD_denote` — the homomorphism **by induction on the trip index `k`**:
  the `k`-fold-unrolled front descent's `Com`-prefix denotes exactly the `k`-fold
  body iteration (the deliverable, paralleling `loopRForD_denote`);
* `semScalarWhile semBody guard` — the **guard-driven do-while** waist model
  (`SEnvScalar` twin of A3's `runWhileMem`: read guard off the out-env, at least
  once, `fuel = 0 ↦ none`) together with its trip count `scalarWhileTrips`;
* `semScalarWhile_eq_iter` — the **fuel/termination bridge**: a guard-driven run
  that halts within `fuel` equals the unconditional `k`-fold iteration at
  `k = scalarWhileTrips … fuel` (the trip *read off the run*);
* `rWhileNz_whole_denote` — the whole-program while denote: for a guard-driven
  data-dependent `while` that terminates within `fuel`, the front descent
  unrolled to the run's actual trip count denotes the guard-driven while
  semantics, over any `IsCoveredSCtl` body.

The trip count is data-dependent (fixed at run time by the values the body
produces), so — unlike the static `RFor` unroll — the descent is parameterised
by the trip `k`, and the denote holds per-`k` under the explicit termination
hypothesis (the `fuel` the do-while halts within).  This is a fueled denote: an
unbounded-nontermination denote is out of scope.

**All goals closed; no axioms beyond the front's existing set.**
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

/-! ## 1. The trip-indexed while descent `loopWhileD`

`loopWhileD` is the `loopRForD` twin **minus** the per-iteration counter const
bind: per trip it just threads one more body descent (the while body reads and
decrements its own counter, so no fresh counter const is emitted).  The recursion
peels the LAST trip, so the trip-index induction closes in lock-step with
`semWhileIter`. -/

/-- Trip-indexed unrolled dialect while descent: a `Nat`-fold of the direct body
    translation, composing `ComCont` prefixes with `ComCont.comp`.
    The `k`-fold copy of the body region — the semantic witness that the loop
    region, run for `k` trips, is exactly `k` sequenced body descents.  The body
    translator `translateBody` is passed in (as in `loopRForD`). -/
def loopWhileD {Γ : Ctx}
    (translateBody : ∀ {Γ'' : Ctx}, VarMap Γ'' → Option (DTransOut Γ''))
    (vm : VarMap Γ) : Nat → Option (DTransOut Γ)
  | 0 => some { Γ' := Γ, cont := ComCont.id, vm := vm }
  | n + 1 =>
      match loopWhileD translateBody vm n with
      | none => none
      | some oPre =>
          match translateBody oPre.vm with
          | none => none
          | some oBody =>
              some { Γ' := oBody.Γ'
                     cont := ComCont.comp oPre.cont oBody.cont
                     vm := oBody.vm }

/-! ## 2. The while-body iteration semantics `semWhileIter`

The unconditional `k`-fold body iteration over `SEnvScalar` — the `semRForD`
twin minus the counter const `upd`.  Peels the LAST trip, matching `loopWhileD`. -/

/-- Unconditional `k`-fold iteration of the body semantics.  `semWhileIter semBody
    k env` runs `semBody` exactly `k` times from `env`. -/
def semWhileIter (semBody : SEnvScalar → Option SEnvScalar) :
    Nat → SEnvScalar → Option SEnvScalar
  | 0, env => some env
  | n + 1, env =>
      match semWhileIter semBody n env with
      | some envPre => semBody envPre
      | none => none

/-- Front-peeling form of `semWhileIter`: the first body application factors out.
    (The standard iterate-front vs. iterate-back commutation, used by the
    guard-driven bridge, which peels the FIRST trip.) -/
theorem semWhileIter_succ_front (semBody : SEnvScalar → Option SEnvScalar)
    (m : Nat) (env : SEnvScalar) :
    semWhileIter semBody (m + 1) env =
      match semBody env with
      | some b => semWhileIter semBody m b
      | none => none := by
  induction m generalizing env with
  | zero =>
      simp only [semWhileIter]
      cases semBody env <;> rfl
  | succ m ih =>
      conv_lhs => rw [semWhileIter, ih env]
      cases hb : semBody env with
      | none => simp
      | some b => simp only [semWhileIter]

/-! ## 3. The trip-index denote (the deliverable) -/

/-- **Trip-index denote for the while region** (the `loopRForD_denote` twin).
    The `k`-fold-unrolled front descent's `Com`-prefix denotes exactly the
    `k`-fold body iteration, by induction on the trip index `k`.  The entry
    `Γ`/`vm`/`V`/`env` stay FIXED across the induction (each step peels the LAST
    trip); only the output `o`/`env'` generalise.  The body's preservation
    homomorphism is passed in as `ihBody` (the coverage IH). -/
theorem loopWhileD_denote (body : LowCT)
    (ihBody : ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm body = some o →
      semScalar body env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V') :
    ∀ (N : Nat) {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      loopWhileD (translateBody := fun vm' => translateDialectControl vm' body) vm N = some o →
      semWhileIter (fun e => semScalar body e) N env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro N
  induction N with
  | zero =>
      intro Γ vm V env env' o hc htr hsem
      simp only [loopWhileD] at htr
      simp only [semWhileIter] at hsem
      obtain rfl := Option.some.inj htr
      obtain rfl := Option.some.inj hsem
      exact ⟨V, hc, fun tail => ⟨tail, rfl, rfl⟩⟩
  | succ n ihN =>
      intro Γ vm V env env' o hc htr hsem
      simp only [loopWhileD] at htr
      simp only [semWhileIter] at hsem
      rcases hpre : loopWhileD (translateBody := fun vm' => translateDialectControl vm' body)
          vm n with _ | oPre
      · rw [hpre] at htr; simp at htr
      · simp only [hpre] at htr
        rcases hspre : semWhileIter (fun e => semScalar body e) n env with _ | envPre
        · rw [hspre] at hsem; simp at hsem
        · simp only [hspre] at hsem
          rcases hbt : translateDialectControl oPre.vm body with _ | oBody
          · rw [hbt] at htr; simp at htr
          · simp only [hbt, Option.some.injEq] at htr
            obtain rfl := htr
            obtain ⟨VPre, hcPre, hcontPre⟩ := ihN vm V env envPre oPre hc hpre hspre
            obtain ⟨Vb, hcB, hcontB⟩ := ihBody oPre.vm VPre envPre env' oBody hcPre hbt hsem
            refine ⟨Vb, hcB, ?_⟩
            intro t tail
            obtain ⟨comB, hcomB, hdenB⟩ := hcontB tail
            obtain ⟨com, hcom, hden⟩ := hcontPre comB
            refine ⟨com, ?_, ?_⟩
            · show ComCont.comp oPre.cont oBody.cont tail = some com
              simp only [ComCont.comp, hcomB, hcom]
            · rw [hden, hdenB]

/-! ## 4. The guard-driven do-while waist model + the fuel/termination bridge

`semScalarWhile` is the `SEnvScalar` twin of A3's `runWhileMem`: the do-while
`repeat { env := body env } while (guard on the out-env)`, at least once, with
`fuel = 0 ↦ none`.  `scalarWhileTrips` reads the data-dependent trip count off
the run.  `semScalarWhile_eq_iter` is the fuel/termination hypothesis made
explicit: a run that halts within `fuel` equals the unconditional `k`-fold
iteration at the trip `k` read off the run. -/

/-- Guard-driven do-while over `SEnvScalar` (the `runWhileMem` waist twin).  The
    trip is decided by `guard` on the values the body produces — the
    data-dependent `while (name != 0)` shape.  `fuel = 0` returns `none`, so any
    `some` result is a termination within `fuel`. -/
def semScalarWhile (semBody : SEnvScalar → Option SEnvScalar) (guard : SEnvScalar → Bool) :
    Nat → SEnvScalar → Option SEnvScalar
  | 0, _ => none
  | k + 1, env =>
      match semBody env with
      | some b => if guard b then semScalarWhile semBody guard k b else some b
      | none => none

/-- The data-dependent trip count of the guard-driven do-while (the `whileTripsMem`
    twin): iterations before the guard goes false, bounded by `fuel`. -/
def scalarWhileTrips (semBody : SEnvScalar → Option SEnvScalar) (guard : SEnvScalar → Bool) :
    Nat → SEnvScalar → Nat
  | 0, _ => 0
  | k + 1, env =>
      match semBody env with
      | some b => if guard b then scalarWhileTrips semBody guard k b + 1 else 1
      | none => 0

/-- **Fuel/termination bridge.** A guard-driven do-while that halts within `fuel`
    equals the unconditional `k`-fold body iteration at `k = scalarWhileTrips …
    fuel env` — the trip read off the run.  This is the explicit termination
    hypothesis the trip-index denote consumes. -/
theorem semScalarWhile_eq_iter (semBody : SEnvScalar → Option SEnvScalar)
    (guard : SEnvScalar → Bool) :
    ∀ (fuel : Nat) (env env' : SEnvScalar),
      semScalarWhile semBody guard fuel env = some env' →
      semWhileIter semBody (scalarWhileTrips semBody guard fuel env) env = some env' := by
  intro fuel
  induction fuel with
  | zero => intro env env' h; simp [semScalarWhile] at h
  | succ k ih =>
      intro env env' h
      simp only [semScalarWhile] at h
      simp only [scalarWhileTrips]
      cases hb : semBody env with
      | none => simp [hb] at h
      | some b =>
          simp only [hb] at h ⊢
          by_cases hg : guard b
          · simp only [if_pos hg] at h ⊢
            rw [semWhileIter_succ_front, hb]
            exact ih b env' h
          · simp only [if_neg hg] at h ⊢
            obtain rfl := Option.some.inj h
            rw [semWhileIter_succ_front, hb]
            simp only [semWhileIter]

/-! ## 5. The whole-program while denote + coverage predicate -/

/-- The control-extended covered fragment extended with the data-dependent
    `while` region: an `RWhileNz` over an `IsCoveredSCtl` body.  Sidecar predicate
    (the `SeqExt`/`while` pattern) — the core `IsCoveredSCtl` inductive that the
    compiler-correctness headline's simulation consumes is left untouched. -/
inductive IsCoveredSWhile : LowCT → Prop
  | rWhileNz {name : String} {body : LowCT} :
      IsCoveredSCtl body → IsCoveredSWhile (.RWhileNz name body)

/-- **Whole-program while denote** (the trip-index denote instantiated at the
    run's actual trip count).  For a guard-driven data-dependent `while` over an
    `IsCoveredSCtl` body that terminates within `fuel` (the explicit termination
    hypothesis), the front descent unrolled to the trip count read off the run
    denotes exactly the guard-driven while semantics.  `guard` is the `RWhileNz`
    guard predicate (`name != 0`); the body's preservation homomorphism is
    `translateDialectControl_denote_ctl`. -/
theorem rWhileNz_whole_denote {body : LowCT} (hcov : IsCoveredSCtl body)
    (guard : SEnvScalar → Bool) (fuel : Nat)
    {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (o : DTransOut Γ)
    (hc : ConsistentS vm V env)
    (htr : loopWhileD (translateBody := fun vm' => translateDialectControl vm' body)
      vm (scalarWhileTrips (fun e => semScalar body e) guard fuel env) = some o)
    (hrun : semScalarWhile (fun e => semScalar body e) guard fuel env = some env') :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
      ConsistentS o.vm V' env' ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
        ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' :=
  loopWhileD_denote body
    (fun vm V env env' o hc ht hs => translateDialectControl_denote_ctl hcov vm V env env' o hc ht hs)
    (scalarWhileTrips (fun e => semScalar body e) guard fuel env)
    vm V env env' o hc htr
    (semScalarWhile_eq_iter (fun e => semScalar body e) guard fuel env env' hrun)

/-! ## 6. Worked witnesses -/

/-- A data-dependent `while (n != 0)` over a covered straight-line body is
    while-covered. -/
example : IsCoveredSWhile (.RWhileNz "n" (.RScalarSet "acc" 5)) :=
  .rWhileNz (.ofStraight (.rScalarSet "acc" 5))

/-- The deployed straight-line front **accepts** the same `RWhileNz` node (the
    context-plumbing arm gates on the guard being a bound scalar and the body
    front-compiling), so the loop region hands off to the downstream back-edge
    emitter. -/
example :
    (translateDialectControl (Γ := [.sword 64])
      ((VarMap.empty).bind "n") (.RWhileNz "n" (.RScalarSet "acc" 5))).isSome := by
  native_decide

/-- The **trip-indexed unrolled descent** front-compiles: the `3`-fold copy of the
    body region descends through the front (the loop region run for `3` trips). -/
example :
    (loopWhileD (translateBody := fun vm' => translateDialectControl vm' (.RScalarSet "acc" 5))
      (Γ := []) VarMap.empty 3).isSome := by
  native_decide

/-- A concrete guard-driven data-dependent countdown terminates and its trip
    count is read off the run: a `while` whose body decrements a counter halts in
    exactly `3` trips from the initial counter `3` (the `mpn_cmp`/countdown early
    exit shape).  `semBody` decrements the tracked counter; `guard` is `counter !=
    0`.  The trip is fixed at run time by the initial counter, not supplied. -/
example :
    scalarWhileTrips
      (fun e => some (SEnvScalar.upd e "c" (t := .sword 64)
        (((envReadU64 e "c").getD 0) - 1)))
      (fun e => decide ((envReadU64 e "c").getD 0 ≠ 0))
      10 (SEnvScalar.upd (fun _ => none) "c" (t := .sword 64) (3 : BitVec 64)) = 3 := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
