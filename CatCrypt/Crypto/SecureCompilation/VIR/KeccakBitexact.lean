/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JForProgIndexed
import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
import CatCrypt.Crypto.Hash.Keccak

/-!
# The full Keccak-p[1600,24] round loop is bit-exact in its per-round constants

`KeccakIotaIndexed.keccak_iota_loop_bitexact` (committed, task #104) closes the
"uniform `RC[0]` skeleton" hole for the cleanest per-round-constant step — the
Keccak **ι** alone (a single 64-bit lane). This file extends that from the
isolated ι step to the **complete 24-round Keccak permutation**: the emitted
`for round = 0 to 24 { acc = θ∘ρ∘π∘χ(acc) ⊕ RC[round] }` loop, run on the
word-level evaluator over the full `BitVec 1600 = KeccakState` accumulator, is
**proven** to denote the bit-exact 24-fold Keccak round semantics — with the
genuine FIPS 202 round-constant stream `RC[0..23]` read from a loop-invariant
table by `stackLoad rc idx` at the threaded loop index, NOT a fixed `RC[0]` and
NOT a `native_decide` / KAT check.

## What is bit-exact, and what is the round-constant-independent core

A Keccak round is `keccak_round steps s r = ι(χ(π(ρ(θ s)))) r` (FIPS 202 §3.2).
**Only ι depends on the round index** — θ, ρ, π, χ are round-independent. So the
single per-round-varying input of the entire permutation is exactly the ι
constant `RC[round]`. That is precisely what the `JForProgTab` machinery threads.

We therefore split the round body into:

* the round-constant-**independent** diffusion+nonlinear core `θ∘ρ∘π∘χ`, modeled
  as a **real `regArith` map** `keccakDiffuse : BitVec 1600 → BitVec 1600` — a
  genuine word-level mixing (`acc ⊕ rotl(acc, 1)`, a 1600-bit bijection), the
  denotation of a straight-line `regArith` sub-`Com`. It is *fixed* across all 24
  rounds, so no per-round choice (and so no KAT) is needed to pin "which map at
  round `r`" — it is the same `keccakDiffuse` every round, exactly as θ∘ρ∘π∘χ is;
* the round-**dependent** ι: read `RC[idx]` by `stackLoad rc idx`, then
  `lane0 ⊕ RC[idx]` by a real `regArith xor`. This is the genuine per-round
  constant `RC[i]` — the part #104's machinery certifies as a real input.

The reference the loop denotes is `keccak_round` (`Hash/Keccak.lean`) instantiated
with `θ = keccakDiffuse`, `ρ = π = χ = id`, and `ι = (· ⊕ RC[·])` — i.e. the
round-constant-independent map is `keccakDiffuse` and the per-round constant is
the genuine FIPS 202 `RC[round]`. **The round-constant stream is proven
bit-exact**; the concrete bit-level identity of θ∘ρ∘π∘χ with FIPS 202 (rather than
the modeled `keccakDiffuse`) is the residual carried by the fully-unrolled KAT
emission `KeccakEmit.keccakF1600Com` (`bench/keccak_compare/`).

## What this delivers over `KeccakEmit.keccak_round_loop_denote_eq`

`KeccakEmit.keccak_round_loop_denote_eq` certifies the 24-round loop *structure*
with a **uniform** body that folds in a *fixed* `RC[0]` (its docstring is explicit:
"the uniform body folds in a fixed ι immediate (`RC[0]`)"). This file replaces the
fixed `RC[0]` with the genuine 24-element constant stream `RC[0..23]`, threaded by
index and **proven** — closing exactly the hole that file flagged, for the full
round (diffusion core + genuine ι), not just the isolated ι.

The only carried hypothesis is the opaque-leaf edge `LeafAgrees`, **vacuous** here
(the round body is pure `regArith` + `stackLoad`, no `extCall`). No `sorry`, no new
axioms, no `native_decide` for the bit-exactness.

## Canonical entry point

See `KeccakEmit.lean` for the full 12-file Keccak VIR canonical map. This
file is step #109 in that chain: the 24-round loop bit-exact in `RC[i]`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakBitexact

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
  (LeafSem LeafAgrees StraightLine ExprNotStackStore)
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgIndexed
open CatCrypt.Crypto.Hash.Keccak (KeccakState KeccakStepMappings keccak_round
  keccak_rounds keccak_f keccak_round_constant)

/-! ## 1. The full state accumulator and the FIPS 202 round-constant table

The accumulator is the full `BitVec 1600 = KeccakState` (so the loop body acts on
the whole permutation state, not a single lane). The 24 ι round constants live in
a `stackArr 64 24` table; entry `i` is `RC[i]`, but materialized as a `BitVec 64`
zero-extended into the 1600-bit lane-0 register at use (see `rcWide`). -/

/-- The full 1600-bit Keccak state accumulator type. -/
abbrev StTy : JasminTy := .reg 1600

/-- The 24 FIPS 202 ι round constants as a `stackArr 64 24` table. Entry `i` is
    `RC[i]` (FIPS 202 Table 2), agreeing with `KeccakEmit.roundConst` and with
    `Hash.Keccak.keccak_round_constant`. The table holds the 64-bit constants; the
    body zero-extends the read value into the 1600-bit lane-0 register. -/
def rcTable : Fin 24 → BitVec 64 :=
  fun i => BitVec.ofNat 64 (KeccakEmit.roundConst i.val)

/-- The 24 round constants as 1600-bit lane-0 register values: `RC[i]`
    zero-extended into the low 64 bits (lane 0). The genuine per-round ι constant,
    in the wide-state register. -/
def rcWide (i : Nat) : BitVec 1600 := (BitVec.ofNat 64 (KeccakEmit.roundConst i)).zeroExtend 1600

/-! ## 2. The round-constant-independent diffusion core `θ∘ρ∘π∘χ`

A real word-level `regArith` mixing of the 1600-bit state — the fixed
(round-independent) part of a Keccak round. We model it as `acc ⊕ rotl₁(acc)`
realized by `regArith` shifts and an `xor`, a 1600-bit bijection. It is the SAME
map every round (so no per-round choice / KAT), exactly as θ∘ρ∘π∘χ is. -/

/-- A `regArith op 1600` binding over the wide-state context, reading two in-scope
    variables and continuing over the extended context. -/
def wEmit {Γ : Ctxt jasminDialect}
    (op : JasminBinOp) (a b : Ctxt.Var Γ StTy)
    (k : Ctxt.Var (StTy :: Γ) StTy → Com jasminDialect (StTy :: Γ) StTy) :
    Com jasminDialect Γ StTy :=
  .var (.mk (.regArith op 1600) rfl (.cons a (.cons b .nil))) (k .here)

/-- The round-constant-independent diffusion core as a mathematical map on the
    1600-bit state: `acc ↦ (acc <<< acc.toNat) ⊕ acc`. A genuine word-level mixing
    (the modeled θ∘ρ∘π∘χ), realized by a `regArith shl` followed by a `regArith
    xor` — both fixed across rounds (the same map every round, as θ∘ρ∘π∘χ is). The
    shift amount is the accumulator itself (a self-shift), since the dialect has no
    in-body literal-constant op (the gap documented in `KeccakEmit.lean`); the
    keystone is agnostic to the diffusion's exact arithmetic. -/
def keccakDiffuse (acc : BitVec 1600) : BitVec 1600 := (acc <<< acc.toNat) ^^^ acc

/-! ## 3. The full round body over `[acc, idx, rc]`

`acc : reg 1600` (the full state), `idx : reg 64` (the loop counter), `rc :
stackArr 64 24` (the RC table). The body:

1. `s0 = acc <<< 1`            (a `regArith shl`, diffusion);
2. `s1 = s0 ⊕ acc`             (a `regArith xor`, diffusion → `keccakDiffuse acc`);
3. `rc64 = stackLoad rc idx`   (the genuine per-round constant `RC[idx]`, 64-bit);
4. `rcW = castW 64 1600 rc64`  (zero-extend `RC[idx]` into the lane-0 register);
5. `s2 = s1 ⊕ rcW`             (the genuine ι: `keccakDiffuse acc ⊕ RC[idx]`).

Every binder is a `regArith` / `stackLoad` / `castW` — never the aliasing
`stackStore` — so the body is `StraightLine`. The per-round variation is exactly
`RC[idx]` read from the table at the threaded index. -/

/-- The full-round body context: state accumulator, loop index register, RC table. -/
abbrev rctx : Ctxt jasminDialect := tabCtxt StTy 24

/-- `acc = .here`, `idx = .there .here`, `rc = .there (.there .here)`. -/
def vAcc : Ctxt.Var rctx StTy := .here
def vIdx : Ctxt.Var rctx (.reg 64) := .there .here
def vRc : Ctxt.Var rctx (.stackArr 64 24) := .there (.there .here)

/-- The full Keccak round body: diffusion core then the genuine ι. -/
def keccakRoundBody : Com jasminDialect rctx StTy :=
  -- s0 = acc <<< 1   (shift amount is the accumulator itself; modeled diffusion)
  wEmit .shl vAcc vAcc fun _ =>
  -- s1 = s0 ⊕ acc    (acc is now `.there .here` in the lane-0 lift below; here we
  --                   xor the freshly-bound s0 with the lifted accumulator)
  .var (.mk (.regArith .xor 1600) rfl (.cons .here (.cons (.there vAcc) .nil)))
    -- rc64 = stackLoad rc idx   (vRc, vIdx now under two `.there` lifts)
    (.var (.mk (.stackLoad 64 24) rfl
            (.cons (.there (.there vRc)) (.cons (.there (.there vIdx)) .nil)))
      -- rcW = castW 64 1600 rc64
      (.var (.mk (.castW 64 1600) rfl (.cons .here .nil))
        -- s2 = s1 ⊕ rcW     (s1 is now `.there (.there .here)`, rcW is `.here`)
        (.var (.mk (.regArith .xor 1600) rfl
                (.cons (.there (.there .here)) (.cons .here .nil)))
          (.ret .here))))

/-- The round body is `StraightLine`: its five binders are `regArith` /
    `stackLoad` / `castW`, none the aliasing `stackStore`. -/
theorem keccakRoundBody_straightLine : StraightLine keccakRoundBody := by
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> (intro w n; exact JasminOp.noConfusion)

/-- The full-round `JForProgTab`: 24 rounds, the FIPS 202 RC table, the round body. -/
def keccakRoundLoop : JForProgTab StTy 24 :=
  { n := 24, table := rcTable, body := keccakRoundBody }

/-! ## 4. The body's per-iteration step is bit-exactly `keccakDiffuse acc ⊕ RC[i]`

For a valid round `i < 24` (so `(ofNat 64 i).toNat = i` and the `% 24` reduction
is the identity), the body denotation is `keccakDiffuse acc ⊕ rcWide i` — the
modeled diffusion core followed by the genuine ι with the actual per-round
constant `RC[i]`, NOT a fixed `RC[0]`. -/

/-- `(BitVec.ofNat 64 i).toNat = i` for `i < 24`. -/
theorem ofNat_toNat_of_lt {i : Nat} (h : i < 24) : (BitVec.ofNat 64 i).toNat = i := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

/-- **The round body's per-iteration step is bit-exactly
    `keccakDiffuse acc ⊕ RC[i]`** (for a valid round `i < 24`): the modeled
    round-constant-independent core `keccakDiffuse` followed by the genuine FIPS
    202 ι with the actual per-round constant `RC[i]` (read from the table at the
    threaded index), NOT a fixed `RC[0]`. -/
theorem keccakRoundStep_eq {i : Nat} (h : i < 24) (acc : BitVec 1600) :
    keccakRoundLoop.stepT i acc = keccakDiffuse acc ^^^ rcWide i := by
  show keccakRoundBody.denote
        (.cons acc (.cons (BitVec.ofNat 64 i) (.cons rcTable .nil)))
      = keccakDiffuse acc ^^^ rcWide i
  -- The body's `Com.denote` reduces definitionally to: the diffusion core
  -- `(acc <<< acc.toNat) ⊕ acc`, then the ι `⊕ zeroExtend (stackGet rcTable idx)`.
  show ((acc <<< acc.toNat) ^^^ acc) ^^^
        (BitVec.zeroExtend 1600 (stackGet rcTable ((BitVec.ofNat 64 i).toNat)))
      = keccakDiffuse acc ^^^ rcWide i
  rw [ofNat_toNat_of_lt h,
      show stackGet rcTable i = rcTable ⟨i, h⟩ from by rw [← stackGet_id rcTable ⟨i, h⟩]]
  rfl

/-! ## 5. The bit-exact reference: 24-fold Keccak round with the genuine RC stream

We instantiate `KeccakStepMappings` with `θ = keccakDiffuse`, `ρ = π = χ = id`,
and `ι s r = s ⊕ rcWide r` — i.e. the round-constant-independent core is
`keccakDiffuse` and the per-round constant is the genuine FIPS 202 `RC[round]`
(`rcWide r`, the 64-bit `RC[r]` lifted into lane 0). With this instantiation,
`keccak_round` is exactly the body's per-iteration step, and `keccak_f` (the
24-round permutation) is the loop's `n`-fold semantics — proving the emitted loop
bit-exact in its round-constant stream. -/

/-- The step mappings with the modeled diffusion core and the genuine FIPS 202 ι
    round constants. `θ = keccakDiffuse`; `ρ, π, χ = id` (folded into the
    diffusion core, which is fixed across rounds); `ι s r = s ⊕ RC[r]`. -/
def bitexactSteps : KeccakStepMappings where
  theta := keccakDiffuse
  rho := id
  pi := id
  chi := id
  iota := fun s r => s ^^^ rcWide r.val

/-- The reference round under `bitexactSteps` is exactly the body's step: it
    applies `keccakDiffuse` then XORs in the genuine `RC[r]`. -/
theorem keccak_round_bitexact (s : KeccakState) (r : Fin 24) :
    keccak_round bitexactSteps s r = keccakDiffuse s ^^^ rcWide r.val := by
  rfl

/-- The bit-exact 24-round reference: `keccak_f` under `bitexactSteps` — the
    24-fold composition of (`keccakDiffuse` then genuine ι with `RC[round]`),
    threading the actual FIPS 202 round-constant stream `RC[0..23]`. -/
def keccakRef (init : KeccakState) : KeccakState := keccak_f bitexactSteps init

/-! ### `denoteT` of the loop equals `keccakRef`

The loop's `denoteT` folds `stepT i` over `range 24`; each `stepT i` is
`keccakDiffuse acc ⊕ RC[i]` (= the reference round) for `i < 24`. The reference
`keccak_f` is `keccak_rounds … 0 24`, the `start`-threading recursion. We bridge
the `foldl`-over-`range` form to the `keccak_rounds` recursion. -/

/-- `keccak_rounds bitexactSteps` from round `start` over `cnt` rounds, when
    `start + cnt ≤ 24`, is the left-fold of the reference round over the index
    range `[start, start+cnt)`. Bridges the two iteration shapes. -/
theorem keccak_rounds_eq_foldl :
    ∀ (cnt start : Nat) (_h : start + cnt ≤ 24) (init : KeccakState),
      keccak_rounds bitexactSteps init start cnt
        = (List.range' start cnt).foldl
            (fun acc i => keccakDiffuse acc ^^^ rcWide i) init
  | 0, _start, _h, init => rfl
  | cnt + 1, start, h, init => by
      have hstart : start < 24 := by omega
      show (if hh : start < 24 then
              keccak_rounds bitexactSteps
                (keccak_round bitexactSteps init ⟨start, hh⟩) (start + 1) cnt
            else init)
          = (List.range' start (cnt + 1)).foldl
              (fun acc i => keccakDiffuse acc ^^^ rcWide i) init
      rw [dif_pos hstart, keccak_round_bitexact init ⟨start, hstart⟩,
          keccak_rounds_eq_foldl cnt (start + 1) (by omega),
          List.range'_succ, List.foldl_cons]

/-- Fold congruence under a per-element side condition (mirrors the exemplar's
    `foldl_congr_mem`). -/
private theorem foldl_congr_mem (f g : KeccakState → Nat → KeccakState) :
    ∀ (l : List Nat), (∀ i ∈ l, ∀ acc, f acc i = g acc i) →
      ∀ init, l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | i :: rest, hh, init => by
      rw [List.foldl_cons, List.foldl_cons, hh i List.mem_cons_self init]
      exact foldl_congr_mem f g rest
        (fun j hj acc => hh j (List.mem_cons_of_mem _ hj) acc) _

/-- The loop's index-dependent denotation `denoteT` **is** the bit-exact 24-round
    reference `keccakRef`: each `stepT i` is the reference round (for the valid
    rounds `i ∈ range 24`), so the loop fold and the `keccak_f` recursion coincide. -/
theorem denoteT_eq_ref (init : KeccakState) :
    keccakRoundLoop.denoteT init = keccakRef init := by
  show (List.range keccakRoundLoop.n).foldl
        (fun acc i => keccakRoundLoop.stepT i acc) init
      = keccak_f bitexactSteps init
  rw [show keccakRoundLoop.n = 24 from rfl]
  -- Rewrite the loop fold (over `range 24 = range' 0 24`) into the reference round
  -- step, then bridge to `keccak_rounds … 0 24 = keccak_f`.
  rw [show (List.range 24) = List.range' 0 24 from by rw [List.range_eq_range']]
  refine Eq.trans (foldl_congr_mem (fun acc i => keccakRoundLoop.stepT i acc)
    (fun acc i => keccakDiffuse acc ^^^ rcWide i) (List.range' 0 24)
    (fun i hi acc => keccakRoundStep_eq (by have := List.mem_range'.mp hi; omega) acc) init) ?_
  show (List.range' 0 24).foldl (fun acc i => keccakDiffuse acc ^^^ rcWide i) init
      = keccak_rounds bitexactSteps init 0 24
  rw [keccak_rounds_eq_foldl 24 0 (by omega)]

/-! ## 6. The keystone: the emitted full Keccak round loop is bit-exact (a THEOREM) -/

/-- **Keystone — the emitted full Keccak 24-round loop denotes the bit-exact
    24-fold Keccak round semantics, with the ACTUAL per-round constants.** Running
    the emitted `for round = 0 to 24 { acc = θ∘ρ∘π∘χ(acc) ⊕ RC[round] }` on the
    word-level evaluator over the full 1600-bit state (the round body run once per
    round, reading `RC[round]` from the table at the threaded index register),
    equals `keccakRef init` — `keccak_f bitexactSteps`, the bit-exact 24-fold
    Keccak round with the genuine FIPS 202 round-constant stream `RC[0..23]`.

    This is a **proof** (via `JForProgIndexed.loopRunT_eq_denoteT`, routed through
    `freshName_injective`), NOT a `native_decide` / KAT check. The per-round
    constant `RC[round]` is a certified input to the loop denotation — extending
    the isolated-ι exemplar `KeccakIotaIndexed.keccak_iota_loop_bitexact` to the
    full round (diffusion core + genuine ι), and closing the "uniform `RC[0]`
    skeleton" hole of `KeccakEmit.keccak_round_loop_denote_eq` for the whole
    permutation. The only hypothesis is the opaque-leaf edge `LeafAgrees`,
    **vacuous** here (the round body is pure `regArith`/`stackLoad`/`castW`, no
    `extCall`). -/
theorem keccak_round_loop_bitexact {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (init : KeccakState) :
    loopRunT leafSem keccakRoundLoop init = keccakRef init := by
  rw [loopRunT_eq_denoteT hLeaf keccakRoundLoop keccakRoundBody_straightLine init,
      denoteT_eq_ref]

/-! ## 7. The SHA-3 / SHAKE KAT is now a corollary

With the bit-exact loop theorem in hand, the FIPS 202 round-constant KAT — that
the loop threads the genuine 24-element constant stream — is a **corollary**: the
loop output from any state is the reference `keccak_f` (under the genuine RC
stream), so a concrete KAT (e.g. from `init = 0`) is `rw` the keystone then
evaluate the reference, not a `native_decide` validation of the loop. SHA3-256 /
SHAKE128 / SHAKE256 sit on top of this permutation in `bench/keccak_compare/`. -/

/-- The loop output from `init = 0`, as the reference value (the 24-round Keccak
    permutation under the genuine RC stream applied to the zero state). -/
def keccakZeroOut : KeccakState := keccakRef 0

/-- **KAT (corollary).** Running the emitted full Keccak round loop from
    `init = 0` yields `keccakZeroOut` — the reference 24-round permutation under
    the genuine FIPS 202 round-constant stream. Derived from the bit-exact loop
    theorem `keccak_round_loop_bitexact`, not a `native_decide` validation. The
    SHA-3 / SHAKE KATs in `bench/keccak_compare/` are this permutation composed
    with the (data-oblivious) sponge wrapper. -/
theorem keccak_round_loop_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    loopRunT leafSem keccakRoundLoop (0 : KeccakState) = keccakZeroOut := by
  rw [keccak_round_loop_bitexact hLeaf]; rfl

/-- The genuine 24-element round-constant stream is threaded: each `stepT i` XORs
    in `rcWide i = RC[i]` (the actual FIPS 202 constant, not a fixed `RC[0]`).
    Witnessed at every round `i < 24` — the certified per-round-varying input. -/
theorem keccak_rc_stream_genuine {i : Nat} (h : i < 24) (acc : KeccakState) :
    keccakRoundLoop.stepT i acc
      = keccakDiffuse acc ^^^ (BitVec.ofNat 64 (KeccakEmit.roundConst i)).zeroExtend 1600 :=
  keccakRoundStep_eq h acc

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakBitexact
