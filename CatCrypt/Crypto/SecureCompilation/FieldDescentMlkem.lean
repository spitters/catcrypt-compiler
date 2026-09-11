/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The ML-KEM `q = 3329` Stage-2 word realization, discharged CONCRETELY

This is the ML-KEM-prime analogue of `Poseidon2/FieldDescentBabyBear.lean`. That
file discharges the `FieldDescent` Stage-2 leaf squares (`modMul`/`modAdd`/
`modSub` → word block) for the BabyBear prime `p = 2013265921`; this file does
the same for the **ML-KEM forward-NTT prime `q = 3329`**, so the field-authored
ML-KEM NTT (`MlkemNttFieldAuthored.lean`) can descend through `fieldComToJasmin`
with a *proved* (not assumed, not `native_decide`-pinned) word realization.

## Why q = 3329 is the *scalar* case (no Montgomery folding)

`q = 3329` is a 12-bit prime, so `q² = 3329² = 11 082 241 < 2^64`. A single
64-bit word holds both a canonical residue (`< q < 2^64`) **and** any product of
two canonical residues (`< q² < 2^64`) with no overflow. The descent's `modMul`
leaf is therefore the *direct schoolbook reduce* `(a · b) % q` — exactly the
shape of BabyBear's `bbMul = (a · b) % p`, but here the reduction is a single
`%`, not the 10-fold Montgomery `bbReduce`. (The 16-bit lane Montgomery block in
`MLKEM.NttEmit.fqmulBlk` is the *AVX2* realization; the **scalar** descent
this file serves does not need it, and the canonical-rep `%` is what the proof
discharges.)

## What is proved (the residual, closed for q = 3329)

Under the canonical-representative encoding `mkEnc x = BitVec.ofNat 64 x.val`:

* `mkMul_realizes` : `mkMul (mkEnc a) (mkEnc b) = mkEnc (modMulF a b)` — the
  `modMul` leaf, where `mkMul a b = (a * b) % q` at the BitVec level (no overflow
  because `a, b < q ⇒ a·b < q² < 2^64`).
* `mkAdd_realizes` : `mkAdd (mkEnc a) (mkEnc b) = mkEnc (modAddF a b)` — the
  `modAdd` leaf, `mkAdd a b = mkCsub (a + b)` (one conditional subtract, since
  `a + b < 2q`).
* `mkSub_realizes` : `mkSub (mkEnc a) (mkEnc b) = mkEnc (modSubF a b)` — the
  `modSub` leaf, `mkSub a b = mkCsub (a + (q − b))` (one conditional subtract,
  since `a + (q − b) < 2q`).

Each is a commuting square `enc (op_q a b) = wordOp (enc a) (enc b)` under the
canonical encoding, discharged with kernel-safe `Nat`/`BitVec.toNat` reasoning —
**never assumed**. Target axioms: `{propext, Classical.choice, Quot.sound}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldDescentMlkem

open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect

/-- The ML-KEM NTT prime as a `Nat`. -/
abbrev Q : Nat := 3329

/-! ## 1. The canonical-representative encoding `ZMod Q → BitVec 64` -/

/-- The Stage-2 encoding: the canonical representative `x.val ∈ [0, Q)` as a
    64-bit word — the non-identity `ZMod Q ↪ BitVec 64` the word realization is
    stated over (mirrors BabyBear's `bbEnc`). -/
def mkEnc (x : ZMod Q) : BitVec 64 := BitVec.ofNat 64 x.val

/-- `x.val < Q` (the canonical representative is `< Q`). -/
lemma val_lt_Q (x : ZMod Q) : x.val < Q := ZMod.val_lt x

/-- The encoding's `.toNat` is the canonical representative (no `% 2^64`
    wraparound: `x.val < Q < 2^64`). -/
lemma mkEnc_toNat (x : ZMod Q) : (mkEnc x).toNat = x.val := by
  unfold mkEnc
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans (val_lt_Q x) (by norm_num))

/-! ## 2. The three word blocks (`mkMul` / `mkCsub` / `mkAdd` / `mkSub`)

`mkMul` is the direct schoolbook reduce — sound because `a, b < Q ⇒ a·b < Q²
< 2^64`, so the BitVec product doesn't wrap and `%` canonicalises. `mkCsub` is
the single conditional subtract used by `mkAdd`/`mkSub` (both feed it a value
`< 2Q`). -/

/-- The ML-KEM field multiply on canonical `reg 64` reps: product then reduce.
    No overflow (`a·b < Q² < 2^64`), so the `%` is the canonicaliser. -/
def mkMul (a b : BitVec 64) : BitVec 64 := (a * b) % (3329 : BitVec 64)

/-- One conditional subtract of `Q`: if `r ≥ Q` subtract `Q`, else keep `r`.
    Canonicalises any `r < 2Q` (`r % Q`). -/
def mkCsub (r : BitVec 64) : BitVec 64 := r % (3329 : BitVec 64)

/-- ML-KEM field add on canonical reps: `a + b` then one csub (`a + b < 2Q`). -/
def mkAdd (a b : BitVec 64) : BitVec 64 := mkCsub (a + b)

/-- ML-KEM field subtract on canonical reps: `a + (Q − b)` then one csub
    (`a + (Q − b) < 2Q`); `a + (Q − b) ≡ a − b (mod Q)`. -/
def mkSub (a b : BitVec 64) : BitVec 64 := mkCsub (a + ((3329 : BitVec 64) - b))

/-! ## 3. `toNat`-level facts -/

/-- `(3329 : BitVec 64).toNat = 3329`. -/
lemma toNat_q : (3329 : BitVec 64).toNat = 3329 := by decide

/-- The encoding lands `< Q` (canonical). -/
lemma mkEnc_lt (x : ZMod Q) : (mkEnc x).toNat < 3329 := by
  rw [mkEnc_toNat]; exact val_lt_Q x

/-! ## 4. The three op-level realization squares (the discharged leaf content) -/

/-- **`modMul` word-realization square.** `mkMul (mkEnc a) (mkEnc b)
    = mkEnc (a * b)`. The single op the descent's `modMul` lowers to, proved on
    canonical reps: `a·b < Q² < 2^64` so the BitVec product is exact, and `% Q`
    matches `(a*b).val = a.val*b.val % Q`. -/
theorem mkMul_realizes (a b : ZMod Q) :
    mkMul (mkEnc a) (mkEnc b) = mkEnc (modMulF a b) := by
  apply BitVec.eq_of_toNat_eq
  have ha := val_lt_Q a
  have hb := val_lt_Q b
  unfold mkMul
  rw [BitVec.toNat_umod, BitVec.toNat_mul, mkEnc_toNat, mkEnc_toNat, toNat_q]
  -- a.val * b.val < Q² < 2^64, so the inner `% 2^64` is inert.
  have hnoover : a.val * b.val % 2 ^ 64 = a.val * b.val := by
    apply Nat.mod_eq_of_lt
    simp only [Q] at ha hb; nlinarith [ha, hb]
  rw [hnoover]
  show a.val * b.val % 3329 = (mkEnc (a * b)).toNat
  rw [mkEnc_toNat, ZMod.val_mul]

/-- **`modAdd` word-realization square.** `mkAdd (mkEnc a) (mkEnc b)
    = mkEnc (a + b)`. `a + b < 2Q < 2^64`, one csub canonicalises. -/
theorem mkAdd_realizes (a b : ZMod Q) :
    mkAdd (mkEnc a) (mkEnc b) = mkEnc (modAddF a b) := by
  apply BitVec.eq_of_toNat_eq
  have ha := val_lt_Q a
  have hb := val_lt_Q b
  unfold mkAdd mkCsub
  rw [BitVec.toNat_umod, BitVec.toNat_add, mkEnc_toNat, mkEnc_toNat, toNat_q]
  have hnoover : (a.val + b.val) % 2 ^ 64 = a.val + b.val := by
    apply Nat.mod_eq_of_lt; simp only [Q] at ha hb; omega
  rw [hnoover]
  show (a.val + b.val) % 3329 = (mkEnc (a + b)).toNat
  rw [mkEnc_toNat, ZMod.val_add]

/-- **`modSub` word-realization square.** `mkSub (mkEnc a) (mkEnc b)
    = mkEnc (a - b)`. Rewrite the field difference as the canonical Nat
    `a.val + (Q − b.val) < 2Q`; one csub canonicalises and the residue matches. -/
theorem mkSub_realizes (a b : ZMod Q) :
    mkSub (mkEnc a) (mkEnc b) = mkEnc (modSubF a b) := by
  have ha := val_lt_Q a
  have hb := val_lt_Q b
  -- Express the field difference as a canonical Nat cast.
  have hcast : modSubF a b = (((a.val + (Q - b.val)) : Nat) : ZMod Q) := by
    show a - b = _
    have hQb : (((Q - b.val) : Nat) : ZMod Q) = -b := by
      rw [Nat.cast_sub (le_of_lt hb), ZMod.natCast_self, ZMod.natCast_val,
          ZMod.cast_id]
      ring
    rw [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id, hQb]; ring
  apply BitVec.eq_of_toNat_eq
  rw [hcast]
  unfold mkSub mkCsub
  -- (3329 - mkEnc b).toNat = 3329 - b.val  (no wrap, b.val < 3329).
  have hsubQ : ((3329 : BitVec 64) - mkEnc b).toNat = 3329 - b.val := by
    rw [BitVec.toNat_sub_of_le, toNat_q, mkEnc_toNat]
    rw [BitVec.le_def, toNat_q, mkEnc_toNat]; simp only [Q] at hb; omega
  rw [BitVec.toNat_umod, BitVec.toNat_add, mkEnc_toNat, hsubQ, toNat_q]
  have hnoover : (a.val + (3329 - b.val)) % 2 ^ 64 = a.val + (3329 - b.val) := by
    apply Nat.mod_eq_of_lt; simp only [Q] at ha hb; omega
  rw [hnoover]
  show (a.val + (3329 - b.val)) % 3329
      = (mkEnc (((a.val + (Q - b.val)) : Nat) : ZMod Q)).toNat
  rw [mkEnc_toNat, ZMod.val_natCast]

/-! ## 5. The three realization squares packaged (the carried Stage-2 leaves)

These three theorems are exactly the content of the Stage-2 `hOpJ` hypothesis at
a `modMul`/`modAdd`/`modSub` node in `FieldDescent.fieldComToJasmin_denote`, now
discharged for the ML-KEM prime — the q = 3329 analogue of
`FieldDescentBabyBear`'s `bb{Mul,Add,Sub}_realizes`. -/

/-- The ML-KEM word realization, bundled: the three commuting squares the
    scalar `fieldComToJasmin` descent of an ML-KEM-prime field `Com` carries. -/
theorem mlkem_word_realization (a b : ZMod Q) :
    mkMul (mkEnc a) (mkEnc b) = mkEnc (modMulF a b)
      ∧ mkAdd (mkEnc a) (mkEnc b) = mkEnc (modAddF a b)
      ∧ mkSub (mkEnc a) (mkEnc b) = mkEnc (modSubF a b) :=
  ⟨mkMul_realizes a b, mkAdd_realizes a b, mkSub_realizes a b⟩

end CatCrypt.Crypto.SecureCompilation.FieldDescentMlkem
