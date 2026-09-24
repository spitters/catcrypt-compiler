/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit
public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2DiffuseExact
public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2DiffuseExact
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2BbMulFieldExact
public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2BbMulFieldExact

/-!
# Poseidon2-BabyBear whole permutation as a flat `Com jasminDialect`

This module supplies the input of the owned-RA producer for the Poseidon2 bench. The
owned-RA path (`JasminLprogExport.Com.toLprogPhysAbi`) consumes a **whole-function
flat `Com jasminDialect`** — the same shape `Sha2Emit.compressCom` /
`Plonky3CompressEmit.compressCom` / the Keccak permutation Com take. The other
Poseidon2 artifacts are:

* a **text** `.jazz` emit (`Poseidon2Emit.poseidon2Jazz`, a `String`),
* opaque-leaf reflect bodies (`Jasmin/Poseidon2Reflect.lean`, one `RCall`),
* round-loop / single-round theorems with a **modeled** mixing core
  (`Poseidon2Bitexact.pos2Diffuse`, `Poseidon2DiffuseExact.pos2InternalRoundClosed`).

None of these is a whole-permutation flat `Com`. This module builds that `Com` and
ties it to a closed-form BitVec permutation, reusing the **field-correct** Baby
Bear seams already proven elsewhere:

* `Poseidon2Emit.bbAdd_correct` / `bbCsub_correct` / `bbMul_correct` — the
  `regArith`-only reductions are exactly `+ mod p` / `· mod p` on canonical reps;
* `Poseidon2BbMulFieldExact.bbMul_eq_mod_p` — the `bbMul_field_correct_residual`
  seam from `Poseidon2DiffuseExact` is **proved**.

## Construction (mirrors `Plonky3CompressEmit.compressCom`)

The permutation state is 16 Baby Bear lanes, each a `reg 64` canonical residue.
We thread it as a `BState` (`cur : Fin 16 → Ctxt.Var Γ r64`) through a CPS
builder. Each field operation is emitted as the exact `regArith` / `regConst`
binding chain its `Poseidon2Emit.bbX` definition uses, so each result lane's
`Com.denote` is precisely the corresponding `bbX` applied to the input lanes'
denotations. Field constants (the prime `P`, fold multiplier `C`, mask `M`, the
round constants, and the internal diagonal `V`) are materialized by the dialect's
nullary `regConst` op (denoting `BitVec.ofNat 64 n`) — no immediate-operand hack.

## What is proved vs the named residual

* **Atomic denotation lemmas** (`emitBin_denote`, `emitConst_denote`,
  `slotVal_step`, `here_lookup`, `there_lookup`) — `rfl`/structural proofs of the
  binding-level semantics and slot evolution.
* **Composite field-op denotation lemmas, fully proved (no residual):**
  - `emitFold_denote_ret` : the 7-binding fold chain denotes `bbFold (slotVal src)`;
  - `emitCsub_denote_ret` : the 9-binding conditional-subtract chain denotes
    `bbCsub (slotVal src)`;
  - `emitAdd_denote_ret`  : `emitAdd` denotes `bbAdd (slotVal a) (slotVal b)`.
  These establish that the `Com`'s binding arithmetic *is* the Baby Bear field
  arithmetic (`bbFold`/`bbCsub`/`bbAdd`), not a placeholder — and `bbAdd`/`bbMul`
  are themselves proven field-correct (`Poseidon2Emit.bbAdd_correct`,
  `Poseidon2BbMulFieldExact.bbMul_eq_mod_p`), so the add layer computes
  `+ mod p`.
* **The closed-form whole permutation** `poseidon2BBPermClosed` composes the
  proven `Poseidon2DiffuseExact` round forms (`pos2SboxClosed`,
  `pos2InternalRoundClosed`, an external-MDS spelled with `bbAdd`) over the
  Plonky3 schedule (pre-mix + 4 external + 13 partial + 4 external).
* **The field bridge** `poseidon2BBPermClosed_eq_spec_residual` names the one
  remaining step: that the closed-form BitVec permutation on canonical reps
  equals `BabyBear.poseidon2BabyBearPermute` lifted through the `bbX = mod p`
  identities. The `bbX`-correctness lemmas it rests on are all proved; the
  residual is the lane-by-lane `ZMod ↔ BitVec` transport bookkeeping over the
  full 21-round schedule, factored as a named `Prop` (the pattern of the SHA-2 and Poseidon2 readout
  halves).
* **The whole-perm `Com` denotation** `poseidon2_perm_com_denote_residual` names
  the structural `Com.denote = poseidon2BBPermClosed` reduction over the full
  binding tree (≈ several-thousand bindings) — too large to `rfl` in one build,
  factored as a named `Prop` exactly as `Poseidon2DiffuseExact.emitter_denote_eq
  _closed_form_residual` does for the single-round case.

## Consumability by the owned-RA producer

`(poseidon2PermCom ())` is a `Com jasminDialect permCtxt r64`, so it is directly
consumable by `Com.toLprogPhysAbi`; `poseidon2PermLprog` is the witness
application.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2WholePermCom

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit
  (bbP bbC bbM bbFold bbCsub bbReduce bbMul bbAdd r64
   rcInitFlat rcFinFlat rcIntFlat diagVFlat)
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2DiffuseExact
  (BBState diagV64 pos2SboxClosed sumAll64 pos2InternalMDSClosed
   pos2InternalRoundClosed)

/-! ## 1. Builder state

The builder threads the 16 Baby Bear lanes as `Ctxt.Var`s of the current
context, plus nine scratch slots used by the reduction chains and the MDS
layers. We keep the lanes and scratch as one `Fin 25 → Ctxt.Var Γ r64` map
(16 lanes + 9 scratch). The lanes are slots `0..15`; scratch slots are
`16..24`. -/

/-- The builder state: current variable for each of the 16 lanes + 9 scratch
    slots. -/
structure BState (Γ : Ctxt jasminDialect) where
  /-- Current SSA variable holding each of the 25 working slots: 16 lanes
      (`0..15`), 3 reduction scratch (`16,17,18` — overwritten by every
      `bbCsub`/`bbReduce` chain), 2 S-box lane temporaries (`19,20`), 2 MDS
      accumulators (`21,22`), and 2 dedicated MDS product temporaries
      (`23,24` — never aliased onto the reduction scratch, so a value parked in
      an accumulator survives an inner `emitAdd`/`emitMul`). -/
  cur : Fin 25 → Ctxt.Var Γ r64

/-- The fresh head variable of an extended context. -/
def headVar (Γ : Ctxt jasminDialect) : Ctxt.Var (r64 :: Γ) r64 := .here

/-- A continuation over an arbitrary extended context (the CPS body). -/
abbrev Cont (t : JasminTy) :=
  {Γ' : Ctxt jasminDialect} → BState Γ' → Com jasminDialect Γ' t

/-! ## 2. Atomic emitters and their denotation lemmas -/

/-- Emit one `regArith op 64` binding writing slot `dst` from slots `a`, `b`,
    then continue with `k` over the extended context (slot `dst` rebound to the
    fresh head var; everything else shifted by `.there`). -/
def emitBin {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (op : JasminBinOp) (dst a b : Fin 25) (k : Cont t) :
    Com jasminDialect Γ t :=
  let e : Expr jasminDialect Γ r64 :=
    { op := .regArith op 64
      retTy_eq := rfl
      args := .cons (st.cur a) (.cons (st.cur b) .nil) }
  let st' : BState (r64 :: Γ) :=
    { cur := fun i => if i = dst then headVar Γ else (st.cur i).there }
  .var e (k st')

/-- Emit one `regConst 64 n` binding writing slot `dst` (a nullary constant
    materialization), then continue. -/
def emitConst {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst : Fin 25) (n : Nat) (k : Cont t) :
    Com jasminDialect Γ t :=
  let e : Expr jasminDialect Γ r64 :=
    { op := .regConst 64 n, retTy_eq := rfl, args := .nil }
  let st' : BState (r64 :: Γ) :=
    { cur := fun i => if i = dst then headVar Γ else (st.cur i).there }
  .var e (k st')

/-- Copy slot `src` into slot `dst` via the idempotent `or` (`x ||| x = x`),
    so the dialect can express a register move with the existing op alphabet. -/
def emitCopy {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst src : Fin 25) (k : Cont t) : Com jasminDialect Γ t :=
  emitBin st .or dst src src k

/-- Slot value of a builder state under a valuation. -/
def slotVal {Γ : Ctxt jasminDialect} (st : BState Γ)
    (V : Ctxt.Valuation Γ) (i : Fin 25) : BitVec 64 := (st.cur i).lookup V

/-- Looking up the fresh head variable in an extended valuation returns the
    extension value. -/
theorem headVar_lookup {Γ : Ctxt jasminDialect}
    (V : Ctxt.Valuation Γ) (x : BitVec 64) :
    (headVar Γ).lookup (V.extend x) = x := rfl

/-- `Ctxt.Var.here.lookup (V.extend x) = x`. -/
@[simp] theorem here_lookup {Γ : Ctxt jasminDialect}
    (V : Ctxt.Valuation Γ) (x : ⟦r64⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := r64)).lookup (V.extend x) = x := rfl

/-- Looking up a `.there`-shifted variable drops the extension. -/
theorem there_lookup {Γ : Ctxt jasminDialect}
    (v : Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ) (x : ⟦r64⟧) :
    (Ctxt.Var.there (s := r64) v).lookup (V.extend x) = v.lookup V := rfl

/-- **`emitBin` denotation**: the freshly bound `dst` lane denotes
    `op.apply (slotVal a) (slotVal b)`, every other slot is unchanged, and the
    overall `Com.denote` is the continuation applied to the updated state. -/
theorem emitBin_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (op : JasminBinOp) (dst a b : Fin 25) (k : Cont t)
    (V : Ctxt.Valuation Γ) :
    (emitBin st op dst a b k).denote V =
      (k (Γ' := r64 :: Γ)
        { cur := fun i => if i = dst then headVar Γ else (st.cur i).there }).denote
        (V.extend (op.apply (slotVal st V a) (slotVal st V b))) := by
  rfl

/-- **`emitConst` denotation**: the freshly bound `dst` lane denotes
    `BitVec.ofNat 64 n`. -/
theorem emitConst_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst : Fin 25) (n : Nat) (k : Cont t)
    (V : Ctxt.Valuation Γ) :
    (emitConst st dst n k).denote V =
      (k (Γ' := r64 :: Γ)
        { cur := fun i => if i = dst then headVar Γ else (st.cur i).there }).denote
        (V.extend (BitVec.ofNat 64 n)) := by
  rfl

/-- **Slot evolution through one binding.** After an `emitBin`/`emitConst`
    binding writing `dst` with value `x`, the updated state reads `x` at `dst`
    and the (shifted) old value at every other slot. This is the state-transition
    fact that lets the composite emitters' denotation chain through. -/
theorem slotVal_step {Γ : Ctxt jasminDialect} (st : BState Γ)
    (V : Ctxt.Valuation Γ) (dst j : Fin 25) (x : BitVec 64) :
    slotVal (Γ := r64 :: Γ)
        { cur := fun i => if i = dst then headVar Γ else (st.cur i).there }
        (V.extend x) j
      = if j = dst then x else slotVal st V j := by
  unfold slotVal headVar
  by_cases h : j = dst
  · simp [h]
  · simp only [h, if_false]; rfl

/-! ## 3. Scratch slots and constant indices

Slots `16,17,18` are scratch. The field reduction needs the constants `C`
(`bbC = 134217727`), `M` (`bbM = 2147483647`), `P` (`bbP = 2013265921`), and the
shift amount `31`/`63`. We materialize them with `emitConst` into scratch slots
on demand. -/

/-- Scratch slot indices. -/
def sc0 : Fin 25 := ⟨16, by omega⟩
def sc1 : Fin 25 := ⟨17, by omega⟩
def sc2 : Fin 25 := ⟨18, by omega⟩
/-- S-box lane temporaries (distinct from scratch and from the 16 lanes). -/
def tmp2 : Fin 25 := ⟨19, by omega⟩
def tmp4 : Fin 25 := ⟨20, by omega⟩
/-- MDS accumulators (a running sum and a per-lane temporary). -/
def acc0 : Fin 25 := ⟨21, by omega⟩
def acc1 : Fin 25 := ⟨22, by omega⟩
/-- Dedicated MDS product temporaries (the `2·x`/`3·x` terms in `applyMat4`).
    Distinct from the reduction scratch `sc0,sc1,sc2`, so a row staged in
    `tmp2,tmp4,acc0,acc1` is not clobbered by an inner `emitMul`/`emitAdd`. -/
def prod0 : Fin 25 := ⟨23, by omega⟩
def prod1 : Fin 25 := ⟨24, by omega⟩

/-- The lane slot for state index `i : Fin 16`. -/
def laneSlot (i : Fin 16) : Fin 25 := ⟨i.val, by omega⟩

/-- `bbC` as a Nat literal (`2^27 - 1`). -/
def cC : Nat := 134217727
/-- `bbM` as a Nat literal (`2^31 - 1`). -/
def cM : Nat := 2147483647
/-- `bbP` as a Nat literal (`p`). -/
def cP : Nat := 2013265921

/-! ## 4. The fold step `bbFold x = (x >>> 31) * C + (x & M)`

Emitted as the exact binding chain:
* `sc0 = regConst 31`,  `sc1 = x >>> sc0`,  `sc0 = regConst cC`,
  `sc1 = sc1 * sc0`  (the high part `(x>>>31)*C`);
* `sc0 = regConst cM`,  `sc2 = x & sc0`     (the low part `x & M`);
* `dst = sc1 + sc2`.
Writes only `dst` (and scratch); reads only `src`. -/
def emitFold {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst src : Fin 25) (k : Cont t) : Com jasminDialect Γ t :=
  emitConst st sc0 31 fun s1 =>
  emitBin s1 .shr sc1 src sc0 fun s2 =>
  emitConst s2 sc0 cC fun s3 =>
  emitBin s3 .mul sc1 sc1 sc0 fun s4 =>
  emitConst s4 sc0 cM fun s5 =>
  emitBin s5 .and sc2 src sc0 fun s6 =>
  emitBin s6 .add dst sc1 sc2 k

/-! ## 5. The conditional subtract `bbCsub r = (r - P) + (P & (0 - ((r-P) >>> 63)))`

Emitted exactly:
* `sc0 = regConst cP`,  `sc1 = src - sc0`      (`t = r - P`);
* `sc0 = regConst 63`,  `sc2 = sc1 >>> sc0`    (sign bit broadcast input);
* `sc0 = regConst 0`,   `sc2 = sc0 - sc2`      (`mask = 0 - (t>>>63)`);
* `sc0 = regConst cP`,  `sc2 = sc0 & sc2`      (`P & mask`);
* `dst = sc1 + sc2`.
Writes only `dst` (and scratch); reads only `src`. -/
def emitCsub {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst src : Fin 25) (k : Cont t) : Com jasminDialect Γ t :=
  emitConst st sc0 cP fun s1 =>
  emitBin s1 .sub sc1 src sc0 fun s2 =>
  emitConst s2 sc0 63 fun s3 =>
  emitBin s3 .shr sc2 sc1 sc0 fun s4 =>
  emitConst s4 sc0 0 fun s5 =>
  emitBin s5 .sub sc2 sc0 sc2 fun s6 =>
  emitConst s6 sc0 cP fun s7 =>
  emitBin s7 .and sc2 sc0 sc2 fun s8 =>
  emitBin s8 .add dst sc1 sc2 k

/-- **`emitCsub` computes `bbCsub` at `dst`** (read by a `ret dst` continuation),
    when `src` is distinct from `sc0`,`sc1`,`sc2`,`dst`. The destination lane
    denotes exactly `bbCsub (slotVal src)` — the branchless conditional subtract
    `(src-P) + (P & (0 - ((src-P)>>>63)))`. Fully proved (no residual), same
    per-binding-reduction technique as `emitFold_denote_ret`. -/
theorem emitCsub_denote_ret {Γ : Ctxt jasminDialect}
    (st : BState Γ) (V : Ctxt.Valuation Γ) (dst src : Fin 25)
    (hs0 : src ≠ sc0) (_hs1 : src ≠ sc1) (_hs2 : src ≠ sc2) :
    (emitCsub st dst src (fun {_} s => .ret (s.cur dst))).denote V
      = bbCsub (slotVal st V src) := by
  show ((emitConst st sc0 cP fun s1 =>
         emitBin s1 .sub sc1 src sc0 fun s2 =>
         emitConst s2 sc0 63 fun s3 =>
         emitBin s3 .shr sc2 sc1 sc0 fun s4 =>
         emitConst s4 sc0 0 fun s5 =>
         emitBin s5 .sub sc2 sc0 sc2 fun s6 =>
         emitConst s6 sc0 cP fun s7 =>
         emitBin s7 .and sc2 sc0 sc2 fun s8 =>
         emitBin s8 .add dst sc1 sc2 (fun {_} s => .ret (s.cur dst)))).denote V = _
  rw [emitConst_denote, emitBin_denote, emitConst_denote, emitBin_denote,
      emitConst_denote, emitBin_denote, emitConst_denote, emitBin_denote,
      emitBin_denote]
  simp only [Com.denote, slotVal, headVar,
    JasminBinOp.apply, bbCsub, bbP, if_true, if_false,
    hs0,
    show (sc1 : Fin 25) ≠ sc0 from by decide,
    show (sc2 : Fin 25) ≠ sc0 from by decide,
    show (sc1 : Fin 25) ≠ sc2 from by decide,
    show (sc2 : Fin 25) ≠ sc1 from by decide,
    here_lookup, there_lookup]
  rfl

/-- **`emitFold` computes `bbFold` at `dst`** (read by a `ret dst` continuation),
    when `src` is distinct from the scratch slots `sc0`,`sc1`,`sc2` and from
    `dst`. The destination lane denotes exactly `bbFold (slotVal src)` — i.e. the
    7-binding chain realizes the Baby Bear fold-reduction step
    `(src >>> 31) * C + (src & M)`. Proved by reducing the
    binding denotations (`emitConst_denote`/`emitBin_denote`) and the slot
    lookups (`headVar_lookup`/`there_lookup`), with the scratch-slot
    disjointness resolved by `decide`. -/
theorem emitFold_denote_ret {Γ : Ctxt jasminDialect}
    (st : BState Γ) (V : Ctxt.Valuation Γ) (dst src : Fin 25)
    (hs0 : src ≠ sc0) (hs1 : src ≠ sc1) (_hs2 : src ≠ sc2) :
    (emitFold st dst src (fun {_} s => .ret (s.cur dst))).denote V
      = bbFold (slotVal st V src) := by
  show ((emitConst st sc0 31 fun s1 =>
         emitBin s1 .shr sc1 src sc0 fun s2 =>
         emitConst s2 sc0 cC fun s3 =>
         emitBin s3 .mul sc1 sc1 sc0 fun s4 =>
         emitConst s4 sc0 cM fun s5 =>
         emitBin s5 .and sc2 src sc0 fun s6 =>
         emitBin s6 .add dst sc1 sc2 (fun {_} s => .ret (s.cur dst)))).denote V = _
  rw [emitConst_denote, emitBin_denote, emitConst_denote, emitBin_denote,
      emitConst_denote, emitBin_denote, emitBin_denote]
  -- Each binding's denotation reduces; the slot lookups resolve via the
  -- `slotVal_step` shape. The scratch-slot disjointness (`sc0≠sc1`, etc.) and
  -- `src ∉ {sc0,sc1,sc2}` are decidable / hypotheses.
  simp only [Com.denote, slotVal, headVar,
    JasminBinOp.apply, bbFold, bbC, bbM, if_true, if_false,
    hs0, hs1,
    show (sc1 : Fin 25) ≠ sc0 from by decide,
    show (sc2 : Fin 25) ≠ sc0 from by decide,
    show (sc1 : Fin 25) ≠ sc2 from by decide,
    show (sc2 : Fin 25) ≠ sc1 from by decide,
    here_lookup, there_lookup]
  -- Residual pure BitVec identity: the dialect's `>>>` reads the shift amount via
  -- `(31#64).toNat = 31`, and `cC`/`cM` are the literals `bbC`/`bbM`.
  rfl

/-! ## 6. The full reduction `bbReduce x` = 10 folds then 2 csubs

`emitReduce dst src`: fold `src` into `dst`, then fold `dst` in place 9 more
times, then 2 conditional subtracts in place. `dst` must be a lane slot
(`0..15`), distinct from the scratch `sc0,sc1,sc2`. -/
def emitReduce {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst src : Fin 25) (k : Cont t) : Com jasminDialect Γ t :=
  emitFold st  dst src fun s1 =>
  emitFold s1  dst dst fun s2 =>
  emitFold s2  dst dst fun s3 =>
  emitFold s3  dst dst fun s4 =>
  emitFold s4  dst dst fun s5 =>
  emitFold s5  dst dst fun s6 =>
  emitFold s6  dst dst fun s7 =>
  emitFold s7  dst dst fun s8 =>
  emitFold s8  dst dst fun s9 =>
  emitFold s9  dst dst fun s10 =>
  emitCsub s10 dst dst fun s11 =>
  emitCsub s11 dst dst k

/-- **Continuation-general `emitFold` step.** Running `emitFold st dst src k`
    equals running `k` on a post-state/valuation whose `dst` slot reads
    `bbFold (slotVal st V src)`. The existential form (mirroring `RoundDenoteStep`)
    threads each fold's `dst` value into the next without naming the 7-binding
    intermediate context; the `dst`-value fact reuses `emitFold_denote_ret`. -/
theorem emitFold_denote_step {Γ : Ctxt jasminDialect}
    (st : BState Γ) (dst src : Fin 25) (k : Cont r64) (V : Ctxt.Valuation Γ)
    (hs0 : src ≠ sc0) (hs1 : src ≠ sc1) (hs2 : src ≠ sc2) :
    ∃ (Γ' : Ctxt jasminDialect) (st' : BState Γ') (V' : Ctxt.Valuation Γ'),
      (emitFold st dst src k).denote V = (k st').denote V'
        ∧ slotVal st' V' dst = bbFold (slotVal st V src) := by
  refine ⟨_, _, _, rfl, ?_⟩
  exact emitFold_denote_ret st V dst src hs0 hs1 hs2

/-- **Continuation-general `emitCsub` step.** Running `emitCsub st dst src k`
    equals running `k` on a post-state/valuation whose `dst` slot reads
    `bbCsub (slotVal st V src)`. The `dst`-value fact reuses `emitCsub_denote_ret`. -/
theorem emitCsub_denote_step {Γ : Ctxt jasminDialect}
    (st : BState Γ) (dst src : Fin 25) (k : Cont r64) (V : Ctxt.Valuation Γ)
    (hs0 : src ≠ sc0) (hs1 : src ≠ sc1) (hs2 : src ≠ sc2) :
    ∃ (Γ' : Ctxt jasminDialect) (st' : BState Γ') (V' : Ctxt.Valuation Γ'),
      (emitCsub st dst src k).denote V = (k st').denote V'
        ∧ slotVal st' V' dst = bbCsub (slotVal st V src) := by
  refine ⟨_, _, _, rfl, ?_⟩
  exact emitCsub_denote_ret st V dst src hs0 hs1 hs2

/-- **`emitReduce` computes `bbReduce` at `dst`** (read by a `ret dst`
    continuation), when `dst` and `src` are distinct from the scratch slots
    `sc0,sc1,sc2`. The destination lane denotes exactly `bbReduce (slotVal src)`
    — the Baby Bear full reduction (10 folds then 2 conditional subtracts). Proved
    by threading the per-op `dst` value through the 10 `emitFold_denote_step`s and
    2 `emitCsub_denote_step`s; the composite `bbCsub∘bbCsub∘bbFold^10` is
    definitionally `bbReduce`. Fully proved (no residual). -/
theorem emitReduce_denote_ret {Γ : Ctxt jasminDialect}
    (st : BState Γ) (V : Ctxt.Valuation Γ) (dst src : Fin 25)
    (hd0 : dst ≠ sc0) (hd1 : dst ≠ sc1) (hd2 : dst ≠ sc2)
    (hs0 : src ≠ sc0) (hs1 : src ≠ sc1) (hs2 : src ≠ sc2) :
    (emitReduce st dst src (fun {_} s => .ret (s.cur dst))).denote V
      = bbReduce (slotVal st V src) := by
  unfold emitReduce
  obtain ⟨_, st1, V1, e1, v1⟩ := emitFold_denote_step st dst src _ V hs0 hs1 hs2
  rw [e1]
  obtain ⟨_, st2, V2, e2, v2⟩ := emitFold_denote_step st1 dst dst _ V1 hd0 hd1 hd2
  rw [e2]
  obtain ⟨_, st3, V3, e3, v3⟩ := emitFold_denote_step st2 dst dst _ V2 hd0 hd1 hd2
  rw [e3]
  obtain ⟨_, st4, V4, e4, v4⟩ := emitFold_denote_step st3 dst dst _ V3 hd0 hd1 hd2
  rw [e4]
  obtain ⟨_, st5, V5, e5, v5⟩ := emitFold_denote_step st4 dst dst _ V4 hd0 hd1 hd2
  rw [e5]
  obtain ⟨_, st6, V6, e6, v6⟩ := emitFold_denote_step st5 dst dst _ V5 hd0 hd1 hd2
  rw [e6]
  obtain ⟨_, st7, V7, e7, v7⟩ := emitFold_denote_step st6 dst dst _ V6 hd0 hd1 hd2
  rw [e7]
  obtain ⟨_, st8, V8, e8, v8⟩ := emitFold_denote_step st7 dst dst _ V7 hd0 hd1 hd2
  rw [e8]
  obtain ⟨_, st9, V9, e9, v9⟩ := emitFold_denote_step st8 dst dst _ V8 hd0 hd1 hd2
  rw [e9]
  obtain ⟨_, st10, V10, e10, v10⟩ := emitFold_denote_step st9 dst dst _ V9 hd0 hd1 hd2
  rw [e10]
  obtain ⟨_, st11, V11, e11, v11⟩ := emitCsub_denote_step st10 dst dst _ V10 hd0 hd1 hd2
  rw [e11]
  obtain ⟨_, st12, V12, e12, v12⟩ := emitCsub_denote_step st11 dst dst _ V11 hd0 hd1 hd2
  rw [e12]
  show slotVal st12 V12 dst = _
  rw [v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1]
  rfl

/-! ## 7. Field add / multiply / S-box on canonical lanes

`emitAdd dst a b`: `dst = a + b` then one csub (`bbAdd`).
`emitMul dst a b`: `dst = a * b` then full reduce (`bbMul`).
`emitSbox dst src`: `x^7` via the Plonky3 5-multiply chain `(x4·x2)·x` with
`x2 = x·x`, `x4 = x2·x2`. Uses lane slots `dst` and scratch lanes; `dst` and
the temporaries must be distinct lanes from `sc0,sc1,sc2`. -/
def emitAdd {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst a b : Fin 25) (k : Cont t) : Com jasminDialect Γ t :=
  emitBin st .add dst a b fun s1 =>
  emitCsub s1 dst dst k

/-- **`emitAdd` computes `bbAdd` at `dst`** (read by a `ret dst` continuation),
    when `dst` is distinct from the scratch slots and `a`,`b` are distinct from
    `dst` and the scratch slots. The destination denotes exactly
    `bbAdd (slotVal a) (slotVal b)` — the Baby Bear field sum `bbCsub (a + b)`.
    Fully proved: `emitBin` sets `dst = a + b`, then `emitCsub_denote_ret` shows
    the conditional subtract yields `bbCsub (a + b) = bbAdd a b`. -/
theorem emitAdd_denote_ret {Γ : Ctxt jasminDialect}
    (st : BState Γ) (V : Ctxt.Valuation Γ) (dst a b : Fin 25)
    (hd0 : dst ≠ sc0) (hd1 : dst ≠ sc1) (hd2 : dst ≠ sc2)
    (_ha : a ≠ dst) (_hb : b ≠ dst) :
    (emitAdd st dst a b (fun {_} s => .ret (s.cur dst))).denote V
      = bbAdd (slotVal st V a) (slotVal st V b) := by
  show (emitBin st .add dst a b
        (fun {_} s => emitCsub s dst dst (fun {_} s' => .ret (s'.cur dst)))).denote V = _
  rw [emitBin_denote]
  -- The csub now runs on the post-`add` state `s` with `src = dst`.
  rw [emitCsub_denote_ret _ _ dst dst hd0 hd1 hd2]
  -- `slotVal (post-add state) dst = bbAdd's a + b`; reduce via `slotVal_step`.
  show bbCsub (slotVal (Γ := r64 :: Γ) _ (V.extend _) dst) = bbAdd _ _
  rw [slotVal_step, if_pos rfl]
  rfl

def emitMul {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst a b : Fin 25) (k : Cont t) : Com jasminDialect Γ t :=
  emitBin st .mul dst a b fun s1 =>
  emitReduce s1 dst dst k

/-- **`emitMul` computes `bbMul` at `dst`** (read by a `ret dst` continuation),
    when `dst` is distinct from the scratch slots and `a`,`b` are distinct from
    `dst`. The destination denotes exactly `bbMul (slotVal a) (slotVal b)` — the
    Baby Bear field product `bbReduce (a * b)`. Fully proved: `emitBin` sets
    `dst = a * b`, then `emitReduce_denote_ret` reduces it. Same shape as
    `emitAdd_denote_ret`, with `emitReduce` in place of the single `emitCsub`. -/
theorem emitMul_denote_ret {Γ : Ctxt jasminDialect}
    (st : BState Γ) (V : Ctxt.Valuation Γ) (dst a b : Fin 25)
    (hd0 : dst ≠ sc0) (hd1 : dst ≠ sc1) (hd2 : dst ≠ sc2)
    (_ha : a ≠ dst) (_hb : b ≠ dst) :
    (emitMul st dst a b (fun {_} s => .ret (s.cur dst))).denote V
      = bbMul (slotVal st V a) (slotVal st V b) := by
  show (emitBin st .mul dst a b
        (fun {_} s => emitReduce s dst dst (fun {_} s' => .ret (s'.cur dst)))).denote V = _
  rw [emitBin_denote]
  rw [emitReduce_denote_ret _ _ dst dst hd0 hd1 hd2 hd0 hd1 hd2]
  show bbReduce (slotVal (Γ := r64 :: Γ) _ (V.extend _) dst) = bbMul _ _
  rw [slotVal_step, if_pos rfl]
  rfl

/-- `emitSbox dst src tmp2 tmp4`: writes `sbox(src) = src^7` into `dst`, using
    two distinct lane temporaries `tmp2`,`tmp4` (all four of `dst,src,tmp2,tmp4`
    must be distinct from `sc0,sc1,sc2`). Computes:
    `tmp2 = src·src (x²); tmp4 = tmp2·tmp2 (x⁴); tmp4 = tmp4·tmp2 (x⁶);
     dst = tmp4·src (x⁷)`.

    The `x⁶` product is staged in `tmp4`, **not** in `dst`, and the original
    `src` value is read in the final multiply. This matters when the caller
    passes `dst = src` (the in-place lane S-box `emitSbox s (laneSlot i)
    (laneSlot i) …`): writing `x⁶` into `dst` first would overwrite `src`, so
    the final `dst·src` would compute `x⁶·x⁶ = x¹²` instead of `x⁶·x = x⁷`. -/
def emitSbox {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst src tmp2 tmp4 : Fin 25) (k : Cont t) :
    Com jasminDialect Γ t :=
  emitMul st  tmp2 src src fun s1 =>
  emitMul s1  tmp4 tmp2 tmp2 fun s2 =>
  emitMul s2  tmp4 tmp4 tmp2 fun s3 =>
  emitMul s3  dst  tmp4 src  k

/-! ## 8. Round-constant tables as Nat lists

Re-exported flat from `Poseidon2Emit` (themselves byte-identical to upstream
`p3-baby-bear v0.5`). `rcInitFlat`/`rcFinFlat` are 4×16 row-major; `rcIntFlat`
is the 13 internal constants; `diagVFlat` the internal diagonal `V`. -/

/-- The external round constant for round `r` (`0..7`), lane `i` (`0..15`):
    rounds `0..3` from `rcInitFlat`, rounds `4..7` from `rcFinFlat`. -/
def rcExtNat (r : Fin 8) (i : Fin 16) : Nat :=
  if r.val < 4 then rcInitFlat.getD (r.val * 16 + i.val) 0
  else rcFinFlat.getD ((r.val - 4) * 16 + i.val) 0

/-- The internal round constant for partial round `r` (`0..12`). -/
def rcIntNat (r : Fin 13) : Nat := rcIntFlat.getD r.val 0

/-- The internal diagonal `V[i]` as a Nat (`0..15`). -/
def diagVNat (i : Fin 16) : Nat := diagVFlat.getD i.val 0

/-! ## 9. The S-box layer and round-constant layers

* `emitSboxAll` — apply the S-box to every lane (the external-round S-box layer);
* `emitSboxLane0` — apply the S-box to lane 0 only (the internal-round S-box);
* `emitAddRC` — add the external round constants `RC[r][·]` to every lane;
* `emitAddRCLane0` — add the internal round constant `RC_INT[r]` to lane 0. -/

/-- Apply the S-box to each lane `0..15` in turn (external-round S-box layer). -/
def emitSboxAll {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  let step (i : Fin 16) (kk : Cont t) : Cont t :=
    fun {_} s => emitSbox s (laneSlot i) (laneSlot i) tmp2 tmp4 kk
  (List.finRange 16).foldr step k st

/-- Apply the S-box to lane 0 only (internal-round S-box). -/
def emitSboxLane0 {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  emitSbox st (laneSlot 0) (laneSlot 0) tmp2 tmp4 k

/-- Add external round constants `RC[r][i]` to every lane `i`. -/
def emitAddRC {Γ : Ctxt jasminDialect} {t : JasminTy}
    (r : Fin 8) (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  let step (i : Fin 16) (kk : Cont t) : Cont t :=
    fun {_} s =>
      emitConst s sc0 (rcExtNat r i) fun s1 =>
      emitAdd s1 (laneSlot i) (laneSlot i) sc0 kk
  (List.finRange 16).foldr step k st

/-- Add the internal round constant `RC_INT[r]` to lane 0. -/
def emitAddRCLane0 {Γ : Ctxt jasminDialect} {t : JasminTy}
    (r : Fin 13) (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  emitConst st sc0 (rcIntNat r) fun s1 =>
  emitAdd s1 (laneSlot 0) (laneSlot 0) sc0 k

/-! ## 10. The internal MDS layer

`internalMDS(s)[i] = Σ + V[i]·s[i]` with `Σ = Σⱼ s[j]`. We compute `Σ` into
`acc0` with a 15-step `bbAdd` left fold over the lanes, snapshot each lane's
old value before overwriting (the MDS reads all lanes' *input* values), and
write `lane[i] = bbAdd(acc0, bbMul(V[i], lane_old[i]))`.

Because the row sum reads all 16 input lanes, we must snapshot the input lanes
before any are overwritten. We keep the running sum in `acc0` and, lane by lane,
compute the new value into a fresh scratch and only write it back after the sum
is fixed. Concretely: first build `Σ` in `acc0`; then for each lane write
`lane[i] := acc0 + V[i]·(lane[i])` — but `lane[i]` here is the *input* value,
which is still live because we have not modified `lane[i]` yet in this pass and
the sum already used a copy. The left-fold sum overwrites nothing (it only reads),
so each `lane[i]` still holds its input value when its row is computed. -/

/-- Build `Σ = Σⱼ s[j]` into slot `acc0` via the 15-step `bbAdd` left fold
    (matching `Poseidon2DiffuseExact.sumAll64`). Reads all lanes; writes `acc0`
    (and scratch). -/
def emitRowSum {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  emitAdd st  acc0 (laneSlot 0) (laneSlot 1) fun s1 =>
  emitAdd s1  acc0 acc0 (laneSlot 2) fun s2 =>
  emitAdd s2  acc0 acc0 (laneSlot 3) fun s3 =>
  emitAdd s3  acc0 acc0 (laneSlot 4) fun s4 =>
  emitAdd s4  acc0 acc0 (laneSlot 5) fun s5 =>
  emitAdd s5  acc0 acc0 (laneSlot 6) fun s6 =>
  emitAdd s6  acc0 acc0 (laneSlot 7) fun s7 =>
  emitAdd s7  acc0 acc0 (laneSlot 8) fun s8 =>
  emitAdd s8  acc0 acc0 (laneSlot 9) fun s9 =>
  emitAdd s9  acc0 acc0 (laneSlot 10) fun s10 =>
  emitAdd s10 acc0 acc0 (laneSlot 11) fun s11 =>
  emitAdd s11 acc0 acc0 (laneSlot 12) fun s12 =>
  emitAdd s12 acc0 acc0 (laneSlot 13) fun s13 =>
  emitAdd s13 acc0 acc0 (laneSlot 14) fun s14 =>
  emitAdd s14 acc0 acc0 (laneSlot 15) k

/-- The internal MDS: build `Σ` into `acc0`, then write each lane
    `lane[i] := acc0 + V[i]·lane[i]` using `acc1` as the `V[i]·lane[i]`
    temporary. The per-lane write uses the lane's still-live input value. -/
def emitInternalMDS {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  emitRowSum st fun s0 =>
  let step (i : Fin 16) (kk : Cont t) : Cont t :=
    fun {_} s =>
      emitConst s sc0 (diagVNat i) fun s1 =>
      emitMul s1 acc1 sc0 (laneSlot i) fun s2 =>
      emitAdd s2 (laneSlot i) acc0 acc1 kk
  (List.finRange 16).foldr step k s0

/-- One internal (partial) round `r`: add `RC_INT[r]` to lane 0, S-box lane 0,
    internal MDS. Matches `Poseidon2DiffuseExact.pos2InternalRoundClosed`. -/
def emitInternalRound {Γ : Ctxt jasminDialect} {t : JasminTy}
    (r : Fin 13) (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  emitAddRCLane0 r st fun s1 =>
  emitSboxLane0 s1 fun s2 =>
  emitInternalMDS s2 k

/-! ## 11. The external MDS layer (4×4 block + circulant sums)

`externalMDS(s)`:
* `applyMat4` per 4-lane block: `circ(2,3,1,1)` over `(s0,s1,s2,s3)`;
* then `sums[k] = s'[k] + s'[k+4] + s'[k+8] + s'[k+12]` added to lane `i ≡ k (4)`.

We emit `applyMat4` per block writing the four rows into the same four lane
slots (using `acc0`,`acc1` as `+2·x`/`+3·x` temporaries — but to avoid clobbering
inputs mid-block we compute each new value before overwriting). Then the
circulant sums use `acc0` for `sums[k]` and `acc1` as a `bbAdd` temporary.

Block `applyMat4`: with `c2 = bbMul 2 x`, `c3 = bbMul 3 x` per term, the rows
are sums of these. To stay within the 23 slots we materialize the constants `2`,
`3` into `sc0` on demand and accumulate. -/

/-- Closed-form `applyMat4` on four BitVec lanes (matches `BabyBear.applyMat4`
    over canonical reps via `bbAdd`/`bbMul`). -/
def applyMat4Closed (x0 x1 x2 x3 : BitVec 64) : Fin 4 → BitVec 64
  | ⟨0, _⟩ => bbAdd (bbAdd (bbAdd (bbMul 2 x0) (bbMul 3 x1)) x2) x3
  | ⟨1, _⟩ => bbAdd (bbAdd (bbAdd x0 (bbMul 2 x1)) (bbMul 3 x2)) x3
  | ⟨2, _⟩ => bbAdd (bbAdd (bbAdd x0 x1) (bbMul 2 x2)) (bbMul 3 x3)
  | ⟨3, _⟩ => bbAdd (bbAdd (bbAdd (bbMul 3 x0) x1) x2) (bbMul 2 x3)

/-- Emit one `applyMat4` block on the four lane slots `base..base+3`, writing
    the four output rows back.

    The four output rows are staged in `tmp2,tmp4,acc0,acc1` (slots `19..22`)
    before write-back, so the four input lanes stay live until all rows are
    computed. The `2·x`/`3·x` products use the **dedicated** product temporary
    `prod0` and `prod1` is the running row accumulator — both disjoint from the
    reduction scratch `sc0,sc1,sc2`. (Staging in `sc1,sc2` would be
    clobbered by the inner `emitMul`/`emitAdd` reduction chains of the later
    rows, corrupting output lane `4b+2`.) -/
def emitApplyMat4 {Γ : Ctxt jasminDialect} {t : JasminTy}
    (b : Fin 4) (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  let l0 : Fin 25 := ⟨4 * b.val + 0, by have := b.isLt; omega⟩
  let l1 : Fin 25 := ⟨4 * b.val + 1, by have := b.isLt; omega⟩
  let l2 : Fin 25 := ⟨4 * b.val + 2, by have := b.isLt; omega⟩
  let l3 : Fin 25 := ⟨4 * b.val + 3, by have := b.isLt; omega⟩
  -- row 0 = 2*l0 + 3*l1 + l2 + l3  -> staged into tmp2
  emitConst st sc0 2 fun s1 =>
  emitMul s1 prod1 sc0 l0 fun s2 =>          -- prod1 = 2*l0
  emitConst s2 sc0 3 fun s3 =>
  emitMul s3 prod0 sc0 l1 fun s4 =>          -- prod0 = 3*l1
  emitAdd s4 prod1 prod1 prod0 fun s5 =>     -- prod1 = 2*l0+3*l1
  emitAdd s5 prod1 prod1 l2 fun s6 =>
  emitAdd s6 tmp2 prod1 l3 fun s7 =>         -- tmp2 = row0
  -- row 1 = l0 + 2*l1 + 3*l2 + l3 -> staged into tmp4
  emitConst s7 sc0 2 fun s8 =>
  emitMul s8 prod1 sc0 l1 fun s9 =>
  emitConst s9 sc0 3 fun s10 =>
  emitMul s10 prod0 sc0 l2 fun s11 =>
  emitAdd s11 prod1 l0 prod1 fun s12 =>
  emitAdd s12 prod1 prod1 prod0 fun s13 =>
  emitAdd s13 tmp4 prod1 l3 fun s14 =>       -- tmp4 = row1
  -- row 2 = l0 + l1 + 2*l2 + 3*l3 -> staged into acc0
  emitConst s14 sc0 2 fun s15 =>
  emitMul s15 prod1 sc0 l2 fun s16 =>
  emitConst s16 sc0 3 fun s17 =>
  emitMul s17 prod0 sc0 l3 fun s18 =>
  emitAdd s18 prod1 l0 prod1 fun s19 =>
  emitAdd s19 prod1 l1 prod1 fun s20 =>
  emitAdd s20 acc0 prod1 prod0 fun s21 =>    -- acc0 = row2
  -- row 3 = 3*l0 + l1 + l2 + 2*l3 -> staged into acc1
  emitConst s21 sc0 3 fun s22 =>
  emitMul s22 prod1 sc0 l0 fun s23 =>
  emitConst s23 sc0 2 fun s24 =>
  emitMul s24 prod0 sc0 l3 fun s25 =>
  emitAdd s25 prod1 prod1 l1 fun s26 =>
  emitAdd s26 prod1 prod1 l2 fun s27 =>
  emitAdd s27 acc1 prod1 prod0 fun s28 =>    -- acc1 = row3
  -- write back the four staged rows (copy via idempotent `or`)
  emitCopy s28 l0 tmp2 fun s29 =>
  emitCopy s29 l1 tmp4 fun s30 =>
  emitCopy s30 l2 acc0 fun s31 =>
  emitCopy s31 l3 acc1 k

/-- Closed-form circulant `sums[k] = s'[k]+s'[k+4]+s'[k+8]+s'[k+12]`. -/
def colSumClosed (s' : Fin 16 → BitVec 64) (k : Fin 4) : BitVec 64 :=
  bbAdd (bbAdd (bbAdd
    (s' ⟨k.val, by have := k.isLt; omega⟩)
    (s' ⟨k.val + 4, by have := k.isLt; omega⟩))
    (s' ⟨k.val + 8, by have := k.isLt; omega⟩))
    (s' ⟨k.val + 12, by have := k.isLt; omega⟩)

/-- Emit the circulant-sum half of the external MDS: compute the four column
    sums into `tmp2,tmp4,acc0,acc1`, then add `sums[i mod 4]` to lane `i`.

    The four column-sum destinations **must avoid the reduction scratch slots**
    `sc0,sc1,sc2` (`16,17,18`): the final per-lane `emitAdd` runs an internal
    `bbCsub` whose chain overwrites `sc0,sc1,sc2`, so a column sum parked in a
    scratch slot would be clobbered before the lanes `≡ 2,3 (mod 4)` read it
    (corrupting output lanes `2,6,10,14` / `3,7,11,15`). We therefore park the
    four sums in `tmp2,tmp4,acc0,acc1` (slots `19,20,21,22`), all disjoint from
    `sc0,sc1,sc2`. `acc1` doubles as the running accumulator while each column
    sum is built (it is read back only as the final destination for column 3,
    after which no further accumulation occurs). -/
def emitColSums {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  -- sums[0] -> tmp2, sums[1] -> tmp4, sums[2] -> acc0, sums[3] -> acc1;
  -- `acc1` is the running accumulator for each column.
  emitAdd st  acc1 (laneSlot 0) (laneSlot 4) fun s1 =>
  emitAdd s1  acc1 acc1 (laneSlot 8) fun s2 =>
  emitAdd s2  tmp2 acc1 (laneSlot 12) fun s3 =>
  emitAdd s3  acc1 (laneSlot 1) (laneSlot 5) fun s4 =>
  emitAdd s4  acc1 acc1 (laneSlot 9) fun s5 =>
  emitAdd s5  tmp4 acc1 (laneSlot 13) fun s6 =>
  emitAdd s6  acc1 (laneSlot 2) (laneSlot 6) fun s7 =>
  emitAdd s7  acc1 acc1 (laneSlot 10) fun s8 =>
  emitAdd s8  acc0 acc1 (laneSlot 14) fun s9 =>
  emitAdd s9  acc1 (laneSlot 3) (laneSlot 7) fun s10 =>
  emitAdd s10 acc1 acc1 (laneSlot 11) fun s11 =>
  emitAdd s11 acc1 acc1 (laneSlot 15) fun s12 =>
  -- add sums[i mod 4] to lane i
  let colSlot : Fin 4 → Fin 25
    | ⟨0, _⟩ => tmp2 | ⟨1, _⟩ => tmp4 | ⟨2, _⟩ => acc0 | ⟨3, _⟩ => acc1
  let step (i : Fin 16) (kk : Cont t) : Cont t :=
    fun {_} s => emitAdd s (laneSlot i) (laneSlot i) (colSlot ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩) kk
  (List.finRange 16).foldr step k s12

/-- The full external MDS: four `applyMat4` blocks then the circulant sums. -/
def emitExternalMDS {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  emitApplyMat4 0 st fun s1 =>
  emitApplyMat4 1 s1 fun s2 =>
  emitApplyMat4 2 s2 fun s3 =>
  emitApplyMat4 3 s3 fun s4 =>
  emitColSums s4 k

/-! ## 12. External round and the full permutation

`externalRound r`: add RC[r], S-box all lanes, external MDS.
The permutation: external MDS pre-mix, 4 external rounds, 13 internal rounds,
4 external rounds. -/

/-- One external (full) round `r`: add RC[r] to all lanes, S-box all lanes,
    external MDS. Matches `BabyBear.externalRound`. -/
def emitExternalRound {Γ : Ctxt jasminDialect} {t : JasminTy}
    (r : Fin 8) (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  emitAddRC r st fun s1 =>
  emitSboxAll s1 fun s2 =>
  emitExternalMDS s2 k

/-- The whole Poseidon2-BabyBear permutation body as a CPS builder: external
    MDS pre-mix, 4 initial external rounds (RC rows `0..3`), 13 internal rounds,
    4 final external rounds (RC rows `4..7`). Mirrors
    `BabyBear.poseidon2BabyBearPermute`. -/
def emitPermBody {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  emitExternalMDS st fun s0 =>
  emitExternalRound 0 s0 fun s1 =>
  emitExternalRound 1 s1 fun s2 =>
  emitExternalRound 2 s2 fun s3 =>
  emitExternalRound 3 s3 fun s4 =>
  emitInternalRound 0 s4 fun p0 =>
  emitInternalRound 1 p0 fun p1 =>
  emitInternalRound 2 p1 fun p2 =>
  emitInternalRound 3 p2 fun p3 =>
  emitInternalRound 4 p3 fun p4 =>
  emitInternalRound 5 p4 fun p5 =>
  emitInternalRound 6 p5 fun p6 =>
  emitInternalRound 7 p6 fun p7 =>
  emitInternalRound 8 p7 fun p8 =>
  emitInternalRound 9 p8 fun p9 =>
  emitInternalRound 10 p9 fun p10 =>
  emitInternalRound 11 p10 fun p11 =>
  emitInternalRound 12 p11 fun p12 =>
  emitExternalRound 4 p12 fun e4 =>
  emitExternalRound 5 e4 fun e5 =>
  emitExternalRound 6 e5 fun e6 =>
  emitExternalRound 7 e6 k

/-! ## 13. Input context, initial state, and the top-level `Com`

The export takes the 16-lane state as 16 `reg 64` input words. The initial
builder state points the 16 lane slots at inputs `0..15`; the 7 scratch / temp
slots are seeded at input 0 (their value is irrelevant — each is written before
any read). The body returns lane 0; the full 16-lane output is read off by the
owned-RA producer via its out-store map. -/

/-- The input context: 16 `r64` state words. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate 16 r64

/-- De Bruijn variable for input word `i` of a `replicate (m+1) r64` context. -/
def inputVar : (m : Nat) → Nat →
    @Ctxt.Var jasminDialect (List.replicate (m + 1) r64) r64
  | _, 0 => .here
  | 0, _ => .here
  | (m + 1), (j + 1) => (inputVar m j).there

/-- Input word `i` of `inCtxt`. -/
def inVar (i : Nat) : Ctxt.Var inCtxt r64 := inputVar 15 i

/-- The initial builder state: lanes `0..15` ↦ inputs `0..15`; scratch / temp
    slots ↦ input 0 (seed; overwritten before first read). -/
def initBState : BState inCtxt where
  cur := fun i => if i.val < 16 then inVar i.val else inVar 0

/-- **The whole Poseidon2-BabyBear permutation as a flat `Com jasminDialect`.**
    Built entirely from `regArith` / `regConst` bindings (no `extCall` / opaque
    leaf) — the BabyBear field arithmetic, the `x^7` S-box, the Plonky3
    external/internal MDS layers, and the round-constant schedule, over
    the full 21-round (pre-mix + 4 + 13 + 4) Poseidon2 schedule. Consumable by
    `JasminLprogExport.Com.toLprogPhysAbi` (the owned-RA producer). -/
def poseidon2PermCom (_ : Unit) : Com jasminDialect inCtxt r64 :=
  emitPermBody initBState (fun {_} s => .ret (s.cur (laneSlot 0)))

/-- Output staging: rebind the 16 lane slots `0..15` as the **last 16
    bindings** (ascending), each via an idempotent `or` copy (`emitCopy`), so
    they are exactly output words `0..15` under the
    `JasminLprogExport` last-`nOut` out-store convention (mirrors
    `KeccakEmit.emitOutStage`). -/
def emitOutStage16 {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  let step (i : Fin 16) (kk : Cont t) : Cont t :=
    fun {_} s => emitCopy s (laneSlot i) (laneSlot i) kk
  (List.finRange 16).foldr step k st

/-- **The whole Poseidon2-BabyBear permutation as a flat `Com jasminDialect`,
    with the 16-lane output staging appended.** Identical body to
    `(poseidon2PermCom ())`, but the last 16 bindings are the 16 output lanes in
    order — the shape the owned-RA producer's `outStoreMap` reads off (the
    `KeccakEmit.keccakF1600Com` convention). This is the value the bench
    harness exports. -/
def poseidon2PermComOut (_ : Unit) : Com jasminDialect inCtxt r64 :=
  emitPermBody initBState fun {_} s =>
  emitOutStage16 s (fun {_} s' => .ret (s'.cur (laneSlot 15)))

/-! ## 14. The Com is leaf-free (pure field arithmetic)

Every binding is a `regArith` or `regConst` op — no `extCall`, `stackLoad`,
`stackStore`. So the Com's denotation is the pure-BitVec word arithmetic, and
the owned-RA producer emits it with no skipped op. -/

/-- A binding is a pure arithmetic op (`regArith` or `regConst`). -/
def isPureArith (op : JasminOp) : Bool :=
  match op with
  | .regArith _ _ => true
  | .regConst _ _ => true
  | _ => false

/-- Every binding of a `Com` is a pure arithmetic op. -/
def allPureArith : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body => isPureArith e.op && allPureArith body

/-- A continuation is pure-arith-preserving if it always yields a pure-arith
    `Com` (for every extended context `Γ'`). The context is an **explicit**
    argument so that the preservation proofs can pass `fun Γ' s => …`. -/
def PureCont {t : JasminTy} (k : Cont t) : Prop :=
  ∀ (Γ' : Ctxt jasminDialect) (s : BState Γ'), allPureArith (k s) = true

/-- `emitBin` preserves pure-arith. -/
theorem emitBin_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (op : JasminBinOp) (dst a b : Fin 25) {k : Cont t}
    (hk : PureCont k) : allPureArith (emitBin st op dst a b k) = true := by
  show (isPureArith (JasminOp.regArith op 64) && _) = true
  rw [Bool.and_eq_true]
  exact ⟨rfl, hk _ _⟩

/-- `emitConst` preserves pure-arith. -/
theorem emitConst_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst : Fin 25) (n : Nat) {k : Cont t}
    (hk : PureCont k) : allPureArith (emitConst st dst n k) = true := by
  show (isPureArith (JasminOp.regConst 64 n) && _) = true
  rw [Bool.and_eq_true]
  exact ⟨rfl, hk _ _⟩

/-- `emitCopy` preserves pure-arith. -/
theorem emitCopy_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst src : Fin 25) {k : Cont t}
    (hk : PureCont k) : allPureArith (emitCopy st dst src k) = true :=
  emitBin_pure st .or dst src src hk

/-- The `.ret` base continuation is pure. -/
theorem ret_pure {Γ : Ctxt jasminDialect} (v : Ctxt.Var Γ r64) :
    allPureArith (.ret v) = true := rfl


/-- A `foldr` of pure-arith-preserving steps over a list is pure-arith
    preserving. -/
theorem foldr_pure {t : JasminTy} (l : List (Fin 16))
    (step : Fin 16 → Cont t → Cont t)
    (hstep : ∀ i (kk : Cont t), PureCont kk → PureCont (step i kk))
    {k : Cont t} (hk : PureCont k) :
    PureCont (@List.foldr (Fin 16) (Cont t) step k l) := by
  induction l with
  | nil => exact hk
  | cons a rest ih => exact hstep a _ ih

/-- `emitFold` preserves pure-arith. -/
theorem emitFold_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst src : Fin 25) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitFold st dst src k) = true := by
  unfold emitFold
  exact emitConst_pure _ _ _ (fun _ _ => emitBin_pure _ _ _ _ _
    (fun _ _ => emitConst_pure _ _ _ (fun _ _ => emitBin_pure _ _ _ _ _
    (fun _ _ => emitConst_pure _ _ _ (fun _ _ => emitBin_pure _ _ _ _ _
    (fun _ _ => emitBin_pure _ _ _ _ _ hk))))))

/-- `emitCsub` preserves pure-arith. -/
theorem emitCsub_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst src : Fin 25) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitCsub st dst src k) = true := by
  unfold emitCsub
  exact emitConst_pure _ _ _ (fun _ _ => emitBin_pure _ _ _ _ _
    (fun _ _ => emitConst_pure _ _ _ (fun _ _ => emitBin_pure _ _ _ _ _
    (fun _ _ => emitConst_pure _ _ _ (fun _ _ => emitBin_pure _ _ _ _ _
    (fun _ _ => emitConst_pure _ _ _ (fun _ _ => emitBin_pure _ _ _ _ _
    (fun _ _ => emitBin_pure _ _ _ _ _ hk))))))))

/-- `emitReduce` preserves pure-arith. -/
theorem emitReduce_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst src : Fin 25) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitReduce st dst src k) = true := by
  unfold emitReduce
  exact emitFold_pure _ _ _ (fun _ _ => emitFold_pure _ _ _
    (fun _ _ => emitFold_pure _ _ _ (fun _ _ => emitFold_pure _ _ _
    (fun _ _ => emitFold_pure _ _ _ (fun _ _ => emitFold_pure _ _ _
    (fun _ _ => emitFold_pure _ _ _ (fun _ _ => emitFold_pure _ _ _
    (fun _ _ => emitFold_pure _ _ _ (fun _ _ => emitFold_pure _ _ _
    (fun _ _ => emitCsub_pure _ _ _ (fun _ _ => emitCsub_pure _ _ _ hk)))))))))))

/-- `emitAdd` preserves pure-arith. -/
theorem emitAdd_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst a b : Fin 25) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitAdd st dst a b k) = true := by
  unfold emitAdd
  exact emitBin_pure _ _ _ _ _ (fun _ _ => emitCsub_pure _ _ _ hk)

/-- `emitMul` preserves pure-arith. -/
theorem emitMul_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst a b : Fin 25) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitMul st dst a b k) = true := by
  unfold emitMul
  exact emitBin_pure _ _ _ _ _ (fun _ _ => emitReduce_pure _ _ _ hk)

/-- `emitSbox` preserves pure-arith. -/
theorem emitSbox_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst src tp2 tp4 : Fin 25) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitSbox st dst src tp2 tp4 k) = true := by
  unfold emitSbox
  exact emitMul_pure _ _ _ _ (fun _ _ => emitMul_pure _ _ _ _
    (fun _ _ => emitMul_pure _ _ _ _ (fun _ _ => emitMul_pure _ _ _ _ hk)))

/-- `emitSboxAll` preserves pure-arith. -/
theorem emitSboxAll_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitSboxAll st k) = true := by
  unfold emitSboxAll
  exact foldr_pure _ _ (fun _ _ hkk => fun _ _ =>
    emitSbox_pure _ _ _ _ _ hkk) hk _ st

/-- `emitSboxLane0` preserves pure-arith. -/
theorem emitSboxLane0_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitSboxLane0 st k) = true :=
  emitSbox_pure _ _ _ _ _ hk

/-- `emitAddRC` preserves pure-arith. -/
theorem emitAddRC_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (r : Fin 8) (st : BState Γ) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitAddRC r st k) = true := by
  unfold emitAddRC
  exact foldr_pure _ _ (fun _ _ hkk => fun _ _ =>
    emitConst_pure _ _ _ (fun _ _ => emitAdd_pure _ _ _ _ hkk)) hk _ st

/-- `emitAddRCLane0` preserves pure-arith. -/
theorem emitAddRCLane0_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (r : Fin 13) (st : BState Γ) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitAddRCLane0 r st k) = true := by
  unfold emitAddRCLane0
  exact emitConst_pure _ _ _ (fun _ _ => emitAdd_pure _ _ _ _ hk)

/-- `emitRowSum` preserves pure-arith. -/
theorem emitRowSum_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitRowSum st k) = true := by
  unfold emitRowSum
  exact emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ hk))))))))))))))

/-- `emitInternalMDS` preserves pure-arith. -/
theorem emitInternalMDS_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitInternalMDS st k) = true := by
  unfold emitInternalMDS
  refine emitRowSum_pure _ ?_
  intro Γ' s0
  exact foldr_pure _ _ (fun _ _ hkk => fun _ _ =>
    emitConst_pure _ _ _ (fun _ _ => emitMul_pure _ _ _ _
      (fun _ _ => emitAdd_pure _ _ _ _ hkk))) hk _ s0

/-- `emitInternalRound` preserves pure-arith. -/
theorem emitInternalRound_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (r : Fin 13) (st : BState Γ) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitInternalRound r st k) = true := by
  unfold emitInternalRound
  exact emitAddRCLane0_pure _ _ (fun _ _ => emitSboxLane0_pure _
    (fun _ _ => emitInternalMDS_pure _ hk))

/-- `emitApplyMat4` preserves pure-arith. -/
theorem emitApplyMat4_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (b : Fin 4) (st : BState Γ) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitApplyMat4 b st k) = true := by
  unfold emitApplyMat4
  exact emitConst_pure _ _ _ (fun _ _ => emitMul_pure _ _ _ _
    (fun _ _ => emitConst_pure _ _ _ (fun _ _ => emitMul_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitConst_pure _ _ _
    (fun _ _ => emitMul_pure _ _ _ _ (fun _ _ => emitConst_pure _ _ _
    (fun _ _ => emitMul_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitConst_pure _ _ _ (fun _ _ => emitMul_pure _ _ _ _
    (fun _ _ => emitConst_pure _ _ _ (fun _ _ => emitMul_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitConst_pure _ _ _
    (fun _ _ => emitMul_pure _ _ _ _ (fun _ _ => emitConst_pure _ _ _
    (fun _ _ => emitMul_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitCopy_pure _ _ _ (fun _ _ => emitCopy_pure _ _ _
    (fun _ _ => emitCopy_pure _ _ _ (fun _ _ => emitCopy_pure _ _ _ hk)))))))))))))))))))))))))))))))

/-- `emitColSums` preserves pure-arith. -/
theorem emitColSums_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitColSums st k) = true := by
  unfold emitColSums
  refine emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _
    (fun _ _ => emitAdd_pure _ _ _ _ (fun _ _ => emitAdd_pure _ _ _ _ ?_)))))))))))
  intro Γ' s12
  exact foldr_pure _ _ (fun _ _ hkk => fun _ _ => emitAdd_pure _ _ _ _ hkk) hk _ s12

/-- `emitExternalMDS` preserves pure-arith. -/
theorem emitExternalMDS_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitExternalMDS st k) = true := by
  unfold emitExternalMDS
  exact emitApplyMat4_pure _ _ (fun _ _ => emitApplyMat4_pure _ _
    (fun _ _ => emitApplyMat4_pure _ _ (fun _ _ => emitApplyMat4_pure _ _
    (fun _ _ => emitColSums_pure _ hk))))

/-- `emitExternalRound` preserves pure-arith. -/
theorem emitExternalRound_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (r : Fin 8) (st : BState Γ) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitExternalRound r st k) = true := by
  unfold emitExternalRound
  exact emitAddRC_pure _ _ (fun _ _ => emitSboxAll_pure _
    (fun _ _ => emitExternalMDS_pure _ hk))

/-- `emitPermBody` preserves pure-arith. -/
theorem emitPermBody_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitPermBody st k) = true := by
  unfold emitPermBody
  exact emitExternalMDS_pure _ (fun _ _ =>
    emitExternalRound_pure _ _ (fun _ _ => emitExternalRound_pure _ _
    (fun _ _ => emitExternalRound_pure _ _ (fun _ _ => emitExternalRound_pure _ _
    (fun _ _ => emitInternalRound_pure _ _ (fun _ _ => emitInternalRound_pure _ _
    (fun _ _ => emitInternalRound_pure _ _ (fun _ _ => emitInternalRound_pure _ _
    (fun _ _ => emitInternalRound_pure _ _ (fun _ _ => emitInternalRound_pure _ _
    (fun _ _ => emitInternalRound_pure _ _ (fun _ _ => emitInternalRound_pure _ _
    (fun _ _ => emitInternalRound_pure _ _ (fun _ _ => emitInternalRound_pure _ _
    (fun _ _ => emitInternalRound_pure _ _ (fun _ _ => emitInternalRound_pure _ _
    (fun _ _ => emitInternalRound_pure _ _ (fun _ _ => emitExternalRound_pure _ _
    (fun _ _ => emitExternalRound_pure _ _ (fun _ _ => emitExternalRound_pure _ _
    (fun _ _ => emitExternalRound_pure _ _ hk)))))))))))))))))))))

/-- **`(poseidon2PermCom ())` is pure field arithmetic** — every binding is a
    `regArith` / `regConst` op, so its denotation is the BitVec word arithmetic
    and the owned-RA producer renders it with no opaque-leaf call.

    Proved compositionally: each emitter preserves the `PureCont` predicate
    (`emit*_pure`), so the whole permutation body — built only from
    `emitBin`/`emitConst`/`emitCopy` — is pure-arith down to the `.ret` leaf.
    (We avoid `native_decide` on the full `Com`: it blows the interpreter
    recursion stack, the materialization issue `Sha256LinearMain` documents.) -/
theorem poseidon2PermCom_pureArith : allPureArith (poseidon2PermCom ()) = true :=
  emitPermBody_pure initBState (fun _ s => ret_pure (s.cur (laneSlot 0)))

/-- `emitOutStage16` preserves pure-arith. -/
theorem emitOutStage16_pure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) {k : Cont t} (hk : PureCont k) :
    allPureArith (emitOutStage16 st k) = true := by
  unfold emitOutStage16
  exact foldr_pure _ _ (fun _ _ hkk => fun _ _ =>
    emitCopy_pure _ _ _ hkk) hk _ st

/-- **`(poseidon2PermComOut ())` is pure field arithmetic** — body + 16-lane output
    staging, all `regArith` / `regConst` bindings (no opaque leaf). -/
theorem poseidon2PermComOut_pureArith : allPureArith (poseidon2PermComOut ()) = true :=
  emitPermBody_pure initBState (fun _ s =>
    emitOutStage16_pure s (fun _ s' => ret_pure (s'.cur (laneSlot 15))))

/-- Binding count of a `Com`. -/
def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

/-! ## 14b. Logical-slot trace for register-residence

The owned-RA producer (`JasminLprogExport.Com.toLprogPhysAbi`) names each binding
of `(poseidon2PermComOut ())` with a **fresh** SSA register `r{depth}` and runs a
linear-scan register allocator over those names. Because every one of the
≈107 000 bindings is a distinct virtual register, the linear scan sees ≈107 000
live ranges spanning the whole permutation and exhausts the 15 GP registers — so
nearly every value lands on the stack and is reloaded per use (≈79 % of the
emitted body is `(%rsp)` traffic; the bench shows 102 739 cyc vs gcc-O3's 5 999).

But the permutation only ever touches **25 logical slots** (16 lanes + 9 scratch,
the `BState.cur` index): each binding writes exactly one `dst : Fin 25`, and a
slot is overwritten only after its previous value is dead (the residence
invariant the builder maintains by construction — e.g. `emitFold s1 dst dst`,
`emitReduce` in place). If the allocator coalesces all bindings that write the
same logical slot onto one live range, it scans **25** ranges, of which ≤17 are
simultaneously live, so the working state stays register-**resident** across the
13 partial rounds and the 8 external rounds — exactly the X25519 monolithic
register-residence move, at the 17× headroom Poseidon2 offers.

`(slotTrace ())` records, in program order, the logical `Fin 25` slot each binding
writes. It mirrors the emit structure of `emitPermBody`/`emitOutStage16`
binding-for-binding (a difference-list recorder over the same `dst` arguments),
so `(slotTrace ()).length = comBindings (poseidon2PermComOut ())` and the `n`-th entry is
the logical slot of the `n`-th body binding. The owned-RA producer consumes it
as the residence-coalescing map (binding depth → residence class). -/

/-- A difference-list slot recorder: a function appending the dst-slot sequence
    of one emit fragment onto an accumulator. -/
abbrev SlotRec := List Nat → List Nat

/-- A recorder fragment: a `SlotRec` transformer, mirroring the emitters' `Cont →
    Cont` CPS shape so the composite recorders compose exactly like the composite
    emitters (`f ∘ g` = "emit `f`'s bindings, then `g`'s"). -/
abbrev SlotRecT := SlotRec → SlotRec

/-- Record one binding writing logical slot `dst` (mirrors `emitBin`/`emitConst`/
    `emitCopy`, each of which emits exactly one binding writing `dst`). -/
def recOne (dst : Fin 25) (k : SlotRec) : SlotRec := fun acc => k (acc ++ [dst.val])

/-- Recorder for `emitFold dst src`: 7 bindings, dst-slots
    `[sc0,sc1,sc0,sc1,sc0,sc2,dst]` (matching the `emitConst/emitBin` chain). -/
def recFold (dst : Fin 25) : SlotRecT :=
  recOne sc0 ∘ recOne sc1 ∘ recOne sc0 ∘ recOne sc1 ∘ recOne sc0 ∘ recOne sc2 ∘ recOne dst

/-- Recorder for `emitCsub dst`: 9 bindings, dst-slots
    `[sc0,sc1,sc0,sc2,sc0,sc2,sc0,sc2,dst]`. -/
def recCsub (dst : Fin 25) : SlotRecT :=
  recOne sc0 ∘ recOne sc1 ∘ recOne sc0 ∘ recOne sc2 ∘ recOne sc0 ∘ recOne sc2 ∘
    recOne sc0 ∘ recOne sc2 ∘ recOne dst

/-- Recorder for `emitReduce dst`: 10 folds then 2 csubs, all writing `dst`. -/
def recReduce (dst : Fin 25) : SlotRecT :=
  (List.foldr (· ∘ ·) id (List.replicate 10 (recFold dst))) ∘ recCsub dst ∘ recCsub dst

/-- Recorder for `emitAdd dst`: one `+` binding then `emitCsub`. -/
def recAdd (dst : Fin 25) : SlotRecT := recOne dst ∘ recCsub dst

/-- Recorder for `emitMul dst`: one `*` binding then `emitReduce`. -/
def recMul (dst : Fin 25) : SlotRecT := recOne dst ∘ recReduce dst

/-- Recorder for `emitSbox dst src tmp2 tmp4`: `tmp2,tmp4,tmp4,dst` muls. -/
def recSbox (dst : Fin 25) : SlotRecT :=
  recMul tmp2 ∘ recMul tmp4 ∘ recMul tmp4 ∘ recMul dst

/-- Recorder for the S-box layer (every lane in turn). -/
def recSboxAll : SlotRecT :=
  List.foldr (· ∘ ·) id ((List.finRange 16).map (fun i => recSbox (laneSlot i)))

/-- Recorder for the external-round RC-add layer (one `emitConst sc0` + `emitAdd`
    per lane). -/
def recAddRC : SlotRecT :=
  List.foldr (· ∘ ·) id
    ((List.finRange 16).map (fun i => recOne sc0 ∘ recAdd (laneSlot i)))

/-- Recorder for the internal-round RC-add (lane 0 only). -/
def recAddRCLane0 : SlotRecT := recOne sc0 ∘ recAdd (laneSlot 0)

/-- Recorder for `emitRowSum`: 15 `emitAdd acc0` bindings. -/
def recRowSum : SlotRecT :=
  List.foldr (· ∘ ·) id (List.replicate 15 (recAdd acc0))

/-- Recorder for `emitInternalMDS`: row sum, then per lane
    `emitConst sc0; emitMul acc1; emitAdd lane`. -/
def recInternalMDS : SlotRecT :=
  recRowSum ∘
    List.foldr (· ∘ ·) id
      ((List.finRange 16).map (fun i =>
        recOne sc0 ∘ recMul acc1 ∘ recAdd (laneSlot i)))

/-- Recorder for one internal (partial) round. -/
def recInternalRound : SlotRecT :=
  recAddRCLane0 ∘ recSbox (laneSlot 0) ∘ recInternalMDS

/-- Recorder for one `emitApplyMat4` block on lanes `4b..4b+3`. Mirrors the 28
    staged bindings + 4 copy-backs. -/
def recApplyMat4 (b : Fin 4) : SlotRecT :=
  let l0 : Fin 25 := ⟨4 * b.val + 0, by have := b.isLt; omega⟩
  let l1 : Fin 25 := ⟨4 * b.val + 1, by have := b.isLt; omega⟩
  let l2 : Fin 25 := ⟨4 * b.val + 2, by have := b.isLt; omega⟩
  let l3 : Fin 25 := ⟨4 * b.val + 3, by have := b.isLt; omega⟩
  recOne sc0 ∘ recMul prod1 ∘ recOne sc0 ∘ recMul prod0 ∘ recAdd prod1 ∘ recAdd prod1 ∘ recAdd tmp2 ∘
  recOne sc0 ∘ recMul prod1 ∘ recOne sc0 ∘ recMul prod0 ∘ recAdd prod1 ∘ recAdd prod1 ∘ recAdd tmp4 ∘
  recOne sc0 ∘ recMul prod1 ∘ recOne sc0 ∘ recMul prod0 ∘ recAdd prod1 ∘ recAdd prod1 ∘ recAdd acc0 ∘
  recOne sc0 ∘ recMul prod1 ∘ recOne sc0 ∘ recMul prod0 ∘ recAdd prod1 ∘ recAdd prod1 ∘ recAdd acc1 ∘
  recOne l0 ∘ recOne l1 ∘ recOne l2 ∘ recOne l3

/-- Recorder for `emitColSums`: 12 column-sum `emitAdd`s into `tmp2,tmp4,acc0,acc1`
    + the 16 per-lane `emitAdd`s. -/
def recColSums : SlotRecT :=
  recAdd acc1 ∘ recAdd acc1 ∘ recAdd tmp2 ∘
  recAdd acc1 ∘ recAdd acc1 ∘ recAdd tmp4 ∘
  recAdd acc1 ∘ recAdd acc1 ∘ recAdd acc0 ∘
  recAdd acc1 ∘ recAdd acc1 ∘ recAdd acc1 ∘
  List.foldr (· ∘ ·) id ((List.finRange 16).map (fun i => recAdd (laneSlot i)))

/-- Recorder for the external MDS: four blocks then circulant sums. -/
def recExternalMDS : SlotRecT :=
  recApplyMat4 0 ∘ recApplyMat4 1 ∘ recApplyMat4 2 ∘ recApplyMat4 3 ∘ recColSums

/-- Recorder for one external (full) round. -/
def recExternalRound : SlotRecT := recAddRC ∘ recSboxAll ∘ recExternalMDS

/-- Recorder for the 16-lane output staging (`emitOutStage16`): 16 copies. -/
def recOutStage16 : SlotRecT :=
  List.foldr (· ∘ ·) id ((List.finRange 16).map (fun i => recOne (laneSlot i)))

/-- Recorder for the whole permutation body (`emitPermBody`): pre-mix, 4 external,
    13 internal, 4 external. -/
def recPermBody : SlotRecT :=
  recExternalMDS ∘
  recExternalRound ∘ recExternalRound ∘ recExternalRound ∘ recExternalRound ∘
  recInternalRound ∘ recInternalRound ∘ recInternalRound ∘ recInternalRound ∘
  recInternalRound ∘ recInternalRound ∘ recInternalRound ∘ recInternalRound ∘
  recInternalRound ∘ recInternalRound ∘ recInternalRound ∘ recInternalRound ∘
  recInternalRound ∘
  recExternalRound ∘ recExternalRound ∘ recExternalRound ∘ recExternalRound

/-- **The logical-slot trace of `(poseidon2PermComOut ())`**: in program order, the
    `Fin 25` residence slot (as a `Nat`) written by each body binding. Mirrors
    `emitPermBody` then `emitOutStage16` binding-for-binding. The owned-RA
    producer consumes it as the residence-coalescing map: binding number `n` is
    coalesced onto residence class `(slotTrace ())[n]`, collapsing the ≈107 000-name
    SSA universe onto the 25 logical slots so the linear scan keeps the working
    state register-resident. -/
def slotTrace (_ : Unit) : List Nat := (recPermBody ∘ recOutStage16) id []

/-- The residence-coalescing map as an `Array Nat` for `O(1)` per-binding lookup
    by the owned-RA producer (`JasminLprogExport.residenceArraySlotOf`). -/
def slotTraceArr (_ : Unit) : Array Nat := (slotTrace ()).toArray

/-- The residence universe has exactly 25 logical slots. -/
def residenceSlots : Nat := 25

/-! ## 15. The closed-form whole permutation (BitVec)

The closed-form whole permutation on the 16 Baby Bear lanes (`BBState =
Fin 16 → BitVec 64`), composing the round forms over the Plonky3
schedule. Internal rounds reuse `Poseidon2DiffuseExact.pos2InternalRoundClosed`
(the proven-bit-exact-to-spec internal round); external rounds use the S-box
layer + the `applyMat4Closed`/`colSumClosed` external MDS spelled here. This is
the mathematical value the emitted `Com` computes (the `Com.denote` tie-in is the
named residual `poseidon2_perm_com_denote_residual`). -/

/-- The external MDS in closed form: `applyMat4` per block, then circulant
    sums. Matches `BabyBear.externalMDS` over canonical reps. -/
def externalMDSClosed (s : BBState) : BBState :=
  let s' : BBState := fun i =>
    let b : Fin 4 := ⟨i.val / 4, by have := i.isLt; omega⟩
    let inB : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩
    applyMat4Closed
      (s ⟨4 * b.val + 0, by have := b.isLt; omega⟩)
      (s ⟨4 * b.val + 1, by have := b.isLt; omega⟩)
      (s ⟨4 * b.val + 2, by have := b.isLt; omega⟩)
      (s ⟨4 * b.val + 3, by have := b.isLt; omega⟩) inB
  fun i =>
    let inB : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩
    bbAdd (s' i) (colSumClosed s' inB)

/-- One external round in closed form: add `RC[r]`, S-box every lane, external
    MDS. `rc` is the round-constant vector for this round. -/
def externalRoundClosed (s : BBState) (rc : Fin 16 → BitVec 64) : BBState :=
  externalMDSClosed (fun i => pos2SboxClosed (bbAdd (s i) (rc i)))

/-- The external round-constant vector for round `r` (`0..7`) as BitVec. -/
def rcExtVec (r : Fin 8) : Fin 16 → BitVec 64 :=
  fun i => BitVec.ofNat 64 (rcExtNat r i)

/-- The internal round constant `RC_INT[r]` as BitVec. -/
def rcIntVal (r : Fin 13) : BitVec 64 := BitVec.ofNat 64 (rcIntNat r)

/-- **The closed-form whole Poseidon2-BabyBear permutation** over 16 canonical
    `BitVec 64` lanes: external MDS pre-mix, 4 initial external rounds, 13
    internal rounds (`Poseidon2DiffuseExact.pos2InternalRoundClosed`), 4 final
    external rounds. Mirrors `BabyBear.poseidon2BabyBearPermute`. This is the
    value `(poseidon2PermCom ())` computes; the `Com.denote` equality is the named
    residual `poseidon2_perm_com_denote_residual`. -/
def poseidon2BBPermClosed (s : BBState) : BBState :=
  let s0  := externalMDSClosed s
  let s1  := externalRoundClosed s0 (rcExtVec 0)
  let s2  := externalRoundClosed s1 (rcExtVec 1)
  let s3  := externalRoundClosed s2 (rcExtVec 2)
  let s4  := externalRoundClosed s3 (rcExtVec 3)
  let p0  := pos2InternalRoundClosed s4  (rcIntVal 0)
  let p1  := pos2InternalRoundClosed p0  (rcIntVal 1)
  let p2  := pos2InternalRoundClosed p1  (rcIntVal 2)
  let p3  := pos2InternalRoundClosed p2  (rcIntVal 3)
  let p4  := pos2InternalRoundClosed p3  (rcIntVal 4)
  let p5  := pos2InternalRoundClosed p4  (rcIntVal 5)
  let p6  := pos2InternalRoundClosed p5  (rcIntVal 6)
  let p7  := pos2InternalRoundClosed p6  (rcIntVal 7)
  let p8  := pos2InternalRoundClosed p7  (rcIntVal 8)
  let p9  := pos2InternalRoundClosed p8  (rcIntVal 9)
  let p10 := pos2InternalRoundClosed p9  (rcIntVal 10)
  let p11 := pos2InternalRoundClosed p10 (rcIntVal 11)
  let p12 := pos2InternalRoundClosed p11 (rcIntVal 12)
  let e4  := externalRoundClosed p12 (rcExtVec 4)
  let e5  := externalRoundClosed e4  (rcExtVec 5)
  let e6  := externalRoundClosed e5  (rcExtVec 6)
  externalRoundClosed e6 (rcExtVec 7)

/-! ## 16. The whole-perm `Com` denotation — named residual

The `Com.denote` of `(poseidon2PermCom ())` equals `poseidon2BBPermClosed` read off
the 16 lane slots. Each individual emitter's denotation IS the matching `bbX`
(the per-emitter denotation lemmas `emitBin_denote`/`emitConst_denote` give the
atomic case; `bbAdd`/`bbMul`/`bbReduce`/`bbCsub` are the closed forms the
composite emitters realize), so the equality holds binding-by-binding. The
structural `Com.denote` reduction over the full ≈several-thousand-binding tree is
too large to `rfl` in one elaboration; we factor it as a named `Prop`, exactly as
`Poseidon2DiffuseExact.emitter_denote_eq_closed_form_residual` does for the
single internal round. -/

/-- Read the 16 lane slots off a final valuation as a `BBState`. -/
def readLanes {Γ : Ctxt jasminDialect} (st : BState Γ)
    (V : Ctxt.Valuation Γ) : BBState := fun i => slotVal st V (laneSlot i)

/-- **The whole-perm `Com` denotation residual.** The emitted permutation `Com`,
    run on an input valuation `V`, returns the lane-0 value of
    `poseidon2BBPermClosed` applied to the input lanes. Stated as a named `Prop`
    (the composition over the full binding tree is the structural residual; the
    per-binding content is the `emit*_denote` / `bbX` correspondence).

    `poseidon2_perm_com_denote_of_rounds`
    (below) proves it from the explicit per-round denote steps
    (`externalMDS_denote_step`, `externalRound_denote_step r`,
    `internalRound_denote_step r`), folding them through the 21-round schedule.
    The remaining obligation is exactly those per-round lane-tracking
    `Com.denote` reductions (one round's binding block at a time). -/
def poseidon2_perm_com_denote_residual : Prop :=
  ∀ (V : Ctxt.Valuation inCtxt),
    (poseidon2PermCom ()).denote V
      = poseidon2BBPermClosed (readLanes initBState V) ⟨0, by omega⟩

/-! ### Per-round denotation steps: the structural residual, decomposed

The whole-perm `Com.denote = poseidon2BBPermClosed` reduction over the
~2720-binding tree is too large to `rfl` in one elaboration. Rather than leave it
as a single ignored `Prop`, we decompose it into the **per-round-component denote
steps** and prove the whole-perm residual *follows* from them by folding through
the 21-round schedule. Each step says: a round-component emitter `E`, applied to
a pre-state and *any* continuation `k`, denotes `k` on a post-state whose lanes
read off (via `readLanes`) as the matching closed round `R` applied to the input
lanes — leaving the continuation's own context/valuation otherwise untouched.

This is the continuation-general form of the `emit*_denote_ret` lemmas already
proved for the atomic field ops (`emitAdd_denote_ret`, `emitFold_denote_ret`,
`emitCsub_denote_ret`); the remaining obligation is exactly these three
per-round steps (the lane-tracking `Com.denote` reduction through one round's
binding block), which we name explicitly instead of burying them. -/

/-- A round-component emitter `E` (over arbitrary extended contexts, returning a
    `Com … r64`) denotes the closed round `R` on the lanes: for every pre-state
    `st`, continuation `k`, and valuation `V`, there is a post-state `st'` and a
    post-valuation `V'` such that running `E st k` is the same as running `k st'`
    on `V'`, and the post-state lanes are `R` applied to the pre-state lanes. -/
def RoundDenoteStep
    (E : {Γ : Ctxt jasminDialect} → BState Γ → Cont r64 → Com jasminDialect Γ r64)
    (R : BBState → BBState) : Prop :=
  ∀ {Γ : Ctxt jasminDialect} (st : BState Γ) (k : Cont r64)
    (V : Ctxt.Valuation Γ),
    ∃ (Γ' : Ctxt jasminDialect) (st' : BState Γ') (V' : Ctxt.Valuation Γ'),
      (E st k).denote V = (k st').denote V'
      ∧ readLanes st' V' = R (readLanes st V)

/-- The external-MDS pre-mix denote step (closed form `externalMDSClosed`). -/
def externalMDS_denote_step : Prop :=
  RoundDenoteStep (fun {_} st k => emitExternalMDS st k) externalMDSClosed

/-- The external-round denote step for round `r` (closed form
    `externalRoundClosed · (rcExtVec r)`). -/
def externalRound_denote_step (r : Fin 8) : Prop :=
  RoundDenoteStep (fun {_} st k => emitExternalRound r st k)
    (fun s => externalRoundClosed s (rcExtVec r))

/-- The internal-round denote step for round `r` (closed form
    `pos2InternalRoundClosed · (rcIntVal r)`). -/
def internalRound_denote_step (r : Fin 13) : Prop :=
  RoundDenoteStep (fun {_} st k => emitInternalRound r st k)
    (fun s => pos2InternalRoundClosed s (rcIntVal r))

/-- **The whole-perm `Com` denotation, reduced to the per-round steps.** Assuming
    the external-MDS pre-mix step, the four external-round steps for the head
    rounds (`0..3`), the thirteen internal-round steps (`0..12`), and the four
    external-round steps for the tail rounds (`4..7`), the whole permutation
    `Com.denote` equals lane-0 of `poseidon2BBPermClosed` on the input lanes —
    i.e. `poseidon2_perm_com_denote_residual` holds.

    The proof folds the per-round denote steps through `emitPermBody`'s CPS chain
    (each step rewrites the denote into the continuation on a post-state whose
    lanes are the closed round of the input lanes), so the only open
    content is the per-round lane-tracking reductions named above. -/
theorem poseidon2_perm_com_denote_of_rounds
    (hmds : externalMDS_denote_step)
    (he : ∀ r : Fin 8, externalRound_denote_step r)
    (hi : ∀ r : Fin 13, internalRound_denote_step r) :
    poseidon2_perm_com_denote_residual := by
  intro V
  -- Unfold the top-level Com and body into the CPS chain.
  show (emitPermBody initBState (fun {_} s => .ret (s.cur (laneSlot 0)))).denote V
      = poseidon2BBPermClosed (readLanes initBState V) ⟨0, by omega⟩
  -- Peel each round via its denote step, threading the lane invariant.
  -- External MDS pre-mix.
  obtain ⟨Γ0, st0, V0, hd0, hl0⟩ := hmds initBState _ V
  -- Four head external rounds.
  obtain ⟨Γ1, st1, V1, hd1, hl1⟩ := he 0 st0 _ V0
  obtain ⟨Γ2, st2, V2, hd2, hl2⟩ := he 1 st1 _ V1
  obtain ⟨Γ3, st3, V3, hd3, hl3⟩ := he 2 st2 _ V2
  obtain ⟨Γ4, st4, V4, hd4, hl4⟩ := he 3 st3 _ V3
  -- Thirteen internal rounds.
  obtain ⟨Γ5, st5, V5, hd5, hl5⟩ := hi 0 st4 _ V4
  obtain ⟨Γ6, st6, V6, hd6, hl6⟩ := hi 1 st5 _ V5
  obtain ⟨Γ7, st7, V7, hd7, hl7⟩ := hi 2 st6 _ V6
  obtain ⟨Γ8, st8, V8, hd8, hl8⟩ := hi 3 st7 _ V7
  obtain ⟨Γ9, st9, V9, hd9, hl9⟩ := hi 4 st8 _ V8
  obtain ⟨Γ10, st10, V10, hd10, hl10⟩ := hi 5 st9 _ V9
  obtain ⟨Γ11, st11, V11, hd11, hl11⟩ := hi 6 st10 _ V10
  obtain ⟨Γ12, st12, V12, hd12, hl12⟩ := hi 7 st11 _ V11
  obtain ⟨Γ13, st13, V13, hd13, hl13⟩ := hi 8 st12 _ V12
  obtain ⟨Γ14, st14, V14, hd14, hl14⟩ := hi 9 st13 _ V13
  obtain ⟨Γ15, st15, V15, hd15, hl15⟩ := hi 10 st14 _ V14
  obtain ⟨Γ16, st16, V16, hd16, hl16⟩ := hi 11 st15 _ V15
  obtain ⟨Γ17, st17, V17, hd17, hl17⟩ := hi 12 st16 _ V16
  -- Four tail external rounds.
  obtain ⟨Γ18, st18, V18, hd18, hl18⟩ := he 4 st17 _ V17
  obtain ⟨Γ19, st19, V19, hd19, hl19⟩ := he 5 st18 _ V18
  obtain ⟨Γ20, st20, V20, hd20, hl20⟩ := he 6 st19 _ V19
  obtain ⟨Γ21, st21, V21, hd21, hl21⟩ := he 7 st20 _ V20
  -- Chain the per-round denote equalities; the final continuation reads lane 0.
  show (emitExternalMDS initBState (fun {_} s0 =>
          emitExternalRound 0 s0 fun s1 =>
          emitExternalRound 1 s1 fun s2 =>
          emitExternalRound 2 s2 fun s3 =>
          emitExternalRound 3 s3 fun s4 =>
          emitInternalRound 0 s4 fun p0 =>
          emitInternalRound 1 p0 fun p1 =>
          emitInternalRound 2 p1 fun p2 =>
          emitInternalRound 3 p2 fun p3 =>
          emitInternalRound 4 p3 fun p4 =>
          emitInternalRound 5 p4 fun p5 =>
          emitInternalRound 6 p5 fun p6 =>
          emitInternalRound 7 p6 fun p7 =>
          emitInternalRound 8 p7 fun p8 =>
          emitInternalRound 9 p8 fun p9 =>
          emitInternalRound 10 p9 fun p10 =>
          emitInternalRound 11 p10 fun p11 =>
          emitInternalRound 12 p11 fun p12 =>
          emitExternalRound 4 p12 fun e4 =>
          emitExternalRound 5 e4 fun e5 =>
          emitExternalRound 6 e5 fun e6 =>
          emitExternalRound 7 e6 (fun {_} s => .ret (s.cur (laneSlot 0))))).denote V = _
  rw [hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13,
      hd14, hd15, hd16, hd17, hd18, hd19, hd20, hd21]
  -- The final continuation is `ret (lane 0)`; its denote is the lane-0 slot.
  show slotVal st21 V21 (laneSlot 0) = _
  -- Assemble the closed-form composition from the lane invariants.
  have hlanes : readLanes st21 V21 = poseidon2BBPermClosed (readLanes initBState V) := by
    rw [hl21, hl20, hl19, hl18, hl17, hl16, hl15, hl14, hl13, hl12, hl11, hl10,
        hl9, hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1, hl0]
    rfl
  have := congrFun hlanes ⟨0, by omega⟩
  simpa [readLanes] using this

/-! ## 17. The field bridge to the `ZMod` spec — named residual

`poseidon2BBPermClosed` is over canonical `BitVec 64` reps; the spec
`BabyBear.poseidon2BabyBearPermute` is over `F = ZMod babyBearPrime`. The bridge
rests on the **proven** field-correctness of the Baby Bear seams:

* `Poseidon2Emit.bbAdd_correct` : `bbAdd a b = (a+b) % p` on canonical reps;
* `Poseidon2Emit.bbMul_correct` / `Poseidon2BbMulFieldExact.bbMul_eq_mod_p` :
  `bbMul a b = (a*b) % p` on canonical reps;
* `Poseidon2DiffuseExact.pos2_internal_round_bitexact` : the closed internal
  round equals the Plonky3 internal round (bit-exact).

What remains is the lane-by-lane `ZMod ↔ BitVec` transport (canonical-rep
`ZMod.val` ↔ `BitVec.toNat`) carried coherently across the full 21-round
schedule. We factor it as a named `Prop`. -/

/-- Canonical `BitVec 64` rep of a Baby Bear field element. -/
noncomputable def reprF (x : CatCrypt.Crypto.Hash.Poseidon2.BabyBear.F) :
    BitVec 64 := BitVec.ofNat 64 x.val

/-- **The field-bridge residual.** On canonical-rep inputs, the closed-form
    BitVec permutation `poseidon2BBPermClosed` agrees lane-by-lane (via `reprF`)
    with the Plonky3 spec permutation `BabyBear.poseidon2BabyBearPermute`. Stated
    as a named `Prop`; rests on the proved `bbAdd`/`bbMul`-field-correctness seams
    plus the `ZMod ↔ BitVec` transport bookkeeping (the residual). -/
def poseidon2BBPermClosed_eq_spec_residual : Prop :=
  ∀ (input : Fin 16 → CatCrypt.Crypto.Hash.Poseidon2.BabyBear.F),
    (∀ i, poseidon2BBPermClosed (fun j => reprF (input j)) i
      = reprF (CatCrypt.Crypto.Hash.Poseidon2.BabyBear.poseidon2BabyBearPermute
          input i))

/-! ## 18. Consumability by the owned-RA producer

`(poseidon2PermCom ())` is a `Com jasminDialect inCtxt r64`. The owned-RA producer
`JasminLprogExport.Com.toLprogPhysAbi` consumes exactly such a value (as
`Sha256LinearMain` / `KeccakLinearMain` do for SHA-256 / Keccak). Below is the
witness application — proof that the whole-perm `Com` is consumable by the
producer. (We use a custom 16+1-input SysV ABI: the export
takes one input/output buffer pointer; the 16 lanes are loaded/stored by the
`inLoadMap` / `outStoreMap`. For this prerequisite step we wire the default
two-pointer ABI; the bench harness supplies the concrete load/store maps.) -/

/-- **The owned-RA `Lprog` for the whole Poseidon2 permutation.** This is the
    witness that `(poseidon2PermCom ())` is consumable by the owned-RA producer
    `Com.toLprogPhysAbi`: it elaborates iff the whole-perm `Com` has the right
    `Com jasminDialect inCtxt r64` shape the producer expects. -/
noncomputable def poseidon2PermLprog :
    CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lprog :=
  CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Com.toLprogPhysAbi
    (poseidon2PermCom ()) "poseidon2_bb_permute"

/-- **Consumability witness**: the owned-RA producer emits exactly one function
    named `poseidon2_bb_permute` from the whole-perm `Com`. This certifies that
    the producer accepts the whole-permutation flat `Com`. -/
theorem poseidon2PermLprog_one_func :
    poseidon2PermLprog.lp_funcs.length = 1
      ∧ poseidon2PermLprog.lp_funcs.head?.map Prod.fst
          = some "poseidon2_bb_permute" :=
  ⟨rfl, rfl⟩

end CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2WholePermCom
