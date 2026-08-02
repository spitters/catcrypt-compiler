/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.ExprLeaf

/-!
# The `corres_rotl` value leaf — a fixed-count rotate as derived shifts + xor

Rotate-left by a fixed count is the arithmetic core of ChaCha, the SHA-2 `Σ`/`σ`
mixers, and the Keccak `θ`/`ρ` steps. Constant-time code never uses a variable
rotate instruction; it open-codes a fixed rotate as

```
rotl x n = (x <<< n) ||| (x >>> (w - n))
```

two fixed shifts and a disjunction. The `SExpr` IR (`Jasmin/LowCT.lean`) has **no
native rotate arm** — the covered word fragment is `SVar`/`SLit`/`SShl`/`SShr`/
`SXor`/`SAnd` — so a rotate is a **derived** leaf, exactly the shape the
`ExprLeaf` bitwise docstring already records: `SXor (SShl x n) (SShr x (w-n))`,
itself `IsWordClean`. For a rotate the two shifted halves are bit-disjoint, so the
`|||` in the spec coincides with the `^^^` the LowCT chain emits — this is the
genuine content of `rotl_or_eq_xor`, letting the chain be ascended through the
existing bitwise value leaf `corres_setExprBitwise` with no new `SExpr` op and no
`|||` leaf.

The ascent leg (`Corres`) was begun by Sebastian Graf (`sgraf812/ascent`) as the
AutoCorres-in-Lean port; this module adds a rotate value leaf to that calculus.

## What is proved

* `rotlWord` / `rotl_spec` — the shift-`|||` open-coding **is** `BitVec.rotateLeft`
  (for `n < 64`), the mathematical fact the leaf rests on.
* `rotl_or_eq_xor` — the two shifted halves are bit-disjoint, so `^^^` = `|||` =
  `rotlWord`; this is why the emitted xor chain computes the rotate.
* `corres_rotl` — a `Corres` value leaf over the three-statement LowCT chain
  `lo := x <<< n; hi := x >>> (w-n); dst := lo ^^^ hi`, built by `corres_seq` over
  three `corres_setExprBitwise` leaves, concluding that the written slot `dst`
  holds `rotlWord (a x) n` in the `BitVec 64` word algebra.

Width is **64** (Keccak / SHA-512); a 32-bit variant (ChaCha / SHA-256) is the
same documented re-indexing the `ExprLeaf` bitwise leaf notes.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Transfer
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge

/-! ## The rotate word operation and its `BitVec.rotateLeft` characterization -/

/-- Fixed-count rotate-left, open-coded exactly as constant-time code emits it:
    `(x <<< n) ||| (x >>> (64 - n))`. -/
def rotlWord (x : BitVec 64) (n : Nat) : BitVec 64 := (x <<< n) ||| (x >>> (64 - n))

/-- **The genuine rotate content.** The shift-`|||` open-coding is exactly
    `BitVec.rotateLeft` for an in-range count `n < 64`: `BitVec.rotateLeft` is
    (`BitVec.rotateLeft_def`) `x <<< (n % 64) ||| x >>> (64 - n % 64)`, and
    `n % 64 = n`. -/
theorem rotl_spec (x : BitVec 64) (n : Nat) (hn : n < 64) :
    rotlWord x n = BitVec.rotateLeft x n := by
  simp only [rotlWord, BitVec.rotateLeft_def, Nat.mod_eq_of_lt hn]

/-- **Disjointness = why xor computes the rotate.** In a rotate the low half
    `x <<< n` has its bottom `n` bits zeroed and the high half `x >>> (64 - n)`
    has everything at index `≥ n` zeroed, so at every bit at most one half is set:
    `^^^` and `|||` agree, and both equal `rotlWord x n`. This is what lets the
    emitted xor chain (no `|||` op) stand in for the rotate. -/
theorem rotl_or_eq_xor (x : BitVec 64) (n : Nat) (hn : n < 64) :
    (x <<< n) ^^^ (x >>> (64 - n)) = rotlWord x n := by
  unfold rotlWord
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  by_cases hin : i < n
  · simp [hin]
  · have h0 : x.getLsbD (64 - n + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [h0]

/-! ## The rotate LowCT chain and its ascent

The chain writes the two shifted halves to source slots `lo`, `hi`, then their
`^^^` to the destination `dst`. Each statement is an `RScalarSetExpr` in the
bitwise `IsWordClean` fragment, so each ascends through `corres_setExprBitwise`;
`corres_seq` threads the three, and `rotl_or_eq_xor` collapses the destination
value to `rotlWord`. (When a dedicated `corres_setExprOr` value leaf lands from
the sibling stream, the final `^^^` can be swapped for the syntactic `|||` the
spec uses; for a rotate the two are equal by `rotl_or_eq_xor`.) -/

/-- The three-statement rotate chain: `lo := x <<< n; hi := x >>> (64 - n);
    dst := lo ^^^ hi`. -/
def rotlProg (dst lo hi x : String) (n : Nat) : LowCT :=
  .RSeq (.RScalarSetExpr lo (.SShl (.SVar x) (.SLit n)))
    (.RSeq (.RScalarSetExpr hi (.SShr (.SVar x) (.SLit (64 - n))))
      (.RScalarSetExpr dst (.SXor (.SVar lo) (.SVar hi))))

/-- Transport a `Corres` along an abstract-transformer equality — collapses the
    `corres_seq` composite transformer to the clean rotate transformer. -/
theorem corres_of_eq {AState : Type} {SR : SEnvScalar → AState → Prop}
    {P : AState → Prop} {fa fa' : AState → AState} {c : LowCT}
    (hfa : fa = fa') (h : Corres SR P fa c) : Corres SR P fa' c := hfa ▸ h

/-- A fixed-count `n < 64` is a legal `SLit` payload (`< 2^64`). -/
theorem rotl_lit_lt (n : Nat) (hn : n < 64) : n < 2 ^ 64 :=
  lt_of_lt_of_le hn (by norm_num)

/-- `(BitVec.ofNat 64 k).toNat = k` for a shift-count `k < 2^64` — the shift amount
    read back from an `SLit` literal is the literal. -/
theorem rotl_shiftAmt (k : Nat) (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- `corres_rotl` — the rotate value leaf. From a concrete env `SRwordBV`-related
    to abstract `a : String → BitVec 64`, the real `semScalar` runs the rotate
    chain `rotlProg` to a state in which the destination slot `dst` holds the clean
    rotate `rotlWord (a x) n` (in the `BitVec 64` word algebra), the scratch slots
    `lo`/`hi` hold the two shifted halves, and every other source name is untouched.
    Built by `corres_seq` over three `corres_setExprBitwise` leaves; the destination
    value collapses to `rotlWord` by `rotl_or_eq_xor`. Requires an in-range count
    (`n < 64`), non-temp source names, and the scratch slots distinct from `x`/each
    other (`x ≠ lo`, `lo ≠ hi`) so the halves are read before being overwritten. -/
theorem corres_rotl (dst lo hi x : String) (n : Nat)
    (hn : n < 64) (hxt : ¬ isTmpName x) (hlot : ¬ isTmpName lo) (hhit : ¬ isTmpName hi)
    (hxlo : x ≠ lo) (hlohi : lo ≠ hi) :
    Corres SRwordBV (fun _ => True)
      (fun a s =>
        if s = dst then rotlWord (a x) n
        else if s = hi then (a x) >>> (64 - n)
        else if s = lo then (a x) <<< n
        else a s)
      (rotlProg dst lo hi x n) := by
  have hn1 : n < 2 ^ 64 := rotl_lit_lt n hn
  have hn2 : 64 - n < 2 ^ 64 := lt_of_le_of_lt (Nat.sub_le 64 n) (by norm_num)
  have hshn : (BitVec.ofNat 64 n).toNat = n := rotl_shiftAmt n hn1
  have hshm : (BitVec.ofNat 64 (64 - n)).toNat = 64 - n := rotl_shiftAmt (64 - n) hn2
  refine corres_of_eq ?_ (corres_seq SRwordBV
      (corres_setExprBitwise lo (.SShl (.SVar x) (.SLit n)) ⟨hxt, hn1⟩)
      (corres_seq SRwordBV
        (corres_setExprBitwise hi (.SShr (.SVar x) (.SLit (64 - n))) ⟨hxt, hn2⟩)
        (corres_setExprBitwise dst (.SXor (.SVar lo) (.SVar hi)) ⟨hlot, hhit⟩)
        (fun _ _ => trivial))
      (fun _ _ => trivial))
  funext a s
  simp only [SExpr.evalBV, hshn, hshm]
  split_ifs <;> simp_all [rotl_or_eq_xor]

end CatCrypt.Crypto.SecureCompilation.Ascent
