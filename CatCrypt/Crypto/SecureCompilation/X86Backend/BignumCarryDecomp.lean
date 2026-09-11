/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
public import Mathlib.Tactic.Ring

/-!
# Structured carry-decomposition for bignum schoolbook multiplies (#325, SB-4)

The s2n-bignum word kernels (`bignum_mul_4_8`, montmul, add/sub) compute their
results through interleaved carry chains built from the word primitives
`waddcarry` (`ADD`/`ADC`/`ADCX`/`ADOX`) and `wumul` (`MULX`). HOL's s2n proof
discharges *all-inputs* functional correctness with `DECARRY_RULE`: it rewrites
each word equation into a `toNat`/`Z` carry decomposition and closes the residual
by real arithmetic, never bit-blasting the 256×256 product.

This module is the Lean analogue. It provides:

* **`wumul_decompose` / `waddcarry_decompose`** — the two atomic DECARRY steps:
  the `(hi,lo)` of a `MULX` and the `(carry,low)` of an `ADD`-family op each
  reassemble (`lo + 2^w·hi`, `low + 2^w·carry`) to the exact unbounded integer.
* **`limbsToNat` + `limbsToNat_*`** — the little-endian limb codec and its
  round-trip / value lemmas (task **C4**): `Σ limb_i · 2^(w·i)` over a `List`,
  with `limbsToNat_append`, `limbsToNat_cons`, and the bijection on the canonical
  `[0, 2^(w·k))` range.
* **`schoolbook_eq_mul`** — the generic, *k-limb*, distributive identity
  `(Σ x_i B^i)(Σ y_j B^j) = Σ_{i,j} x_i y_j B^(i+j)` over `Nat` (task **C5**'s
  mathematical core), reusable for any schoolbook kernel.

These are width- and length-generic (`{w : Nat}`, `List (BitVec w)`), so the
montmul / add / sub kernels can reuse the same DECARRY steps and the same
schoolbook identity. `BignumMontMulKernel.lean` instantiates them at `w = 64`,
`k = 4` for `bignum_mul_4_8`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. Atomic DECARRY steps (the `wumul`/`waddcarry` reassembly) -/

/-- **DECARRY for `MULX`.** The `(hi, lo)` halves of a full unsigned product
    reassemble exactly: `lo + 2^w · hi = x · y` over `Nat` (no wrap, since the
    product is `< 2^w · 2^w`). This is the `MULX` step of `DECARRY_RULE`. -/
theorem wumul_decompose {w : Nat} (x y : BitVec w) :
    (wumul x y).2.toNat + 2 ^ w * (wumul x y).1.toNat = x.toNat * y.toNat := by
  unfold wumul high_bits
  simp only [BitVec.toNat_ofNat]
  have hx := x.isLt
  have hy := y.isLt
  have hprod : x.toNat * y.toNat < 2 ^ w * 2 ^ w :=
    Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (Nat.lt_of_le_of_lt (Nat.zero_le _) hy)
  -- the inner `/ 2^w` of the high word does not itself wrap
  have hhi : (x.toNat * y.toNat) / 2 ^ w < 2 ^ w :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm (2 ^ w)]; exact hprod)
  rw [Nat.mod_eq_of_lt hhi]
  have hdm := Nat.div_add_mod (x.toNat * y.toNat) (2 ^ w)
  omega

/-- **DECARRY for `ADD`-family** (`ADD`/`ADC`/`ADCX`/`ADOX`). The `(carry, low)`
    pair reassembles exactly: `low + 2^w · carry = x + y + c`. This is the
    additive step of `DECARRY_RULE`. -/
theorem waddcarry_decompose {w : Nat} (x y : BitVec w) (c : Bool) :
    (waddcarry x y c).2.toNat
        + 2 ^ w * (if (waddcarry x y c).1 then 1 else 0)
      = x.toNat + y.toNat + (if c then 1 else 0) := by
  simp only [waddcarry, BitVec.toNat_ofNat, decide_eq_true_eq]
  have hx := x.isLt
  have hy := y.isLt
  have hcle : (if c then 1 else 0) ≤ 1 := by split <;> omega
  by_cases hc : 2 ^ w ≤ x.toNat + y.toNat + (if c then 1 else 0)
  · rw [if_pos hc, Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg hc, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## 2. The little-endian limb codec (task C4) -/

/-- `limbsToNat ℓ`: the unsigned integer of a little-endian list of `w`-bit
    limbs, `Σ_i ℓ_i · 2^(w·i)` (limb `0` is least significant). Length-generic,
    so it serves every `k`-limb kernel. -/
def limbsToNat {w : Nat} : List (BitVec w) → Nat
  | [] => 0
  | a :: ℓ => a.toNat + 2 ^ w * limbsToNat ℓ

@[simp] theorem limbsToNat_nil {w : Nat} : limbsToNat ([] : List (BitVec w)) = 0 := rfl

@[simp] theorem limbsToNat_cons {w : Nat} (a : BitVec w) (ℓ : List (BitVec w)) :
    limbsToNat (a :: ℓ) = a.toNat + 2 ^ w * limbsToNat ℓ := rfl

/-- Concatenation splits the codec at the limb boundary: the high block is
    shifted by `2^(w·|low|)`. The append rule that lets a `2k`-limb product be
    re-expressed in terms of two `k`-limb halves. -/
theorem limbsToNat_append {w : Nat} (ℓ₁ ℓ₂ : List (BitVec w)) :
    limbsToNat (ℓ₁ ++ ℓ₂) = limbsToNat ℓ₁ + 2 ^ (w * ℓ₁.length) * limbsToNat ℓ₂ := by
  induction ℓ₁ with
  | nil => simp
  | cons a ℓ ih =>
    have hpow : w * (ℓ.length + 1) = w + w * ℓ.length := by
      rw [Nat.mul_succ, Nat.add_comm]
    simp only [List.cons_append, limbsToNat_cons, List.length_cons, ih]
    rw [Nat.mul_add, ← Nat.mul_assoc, hpow, Nat.pow_add, Nat.add_assoc]

/-- Every limb-list value is `< 2^(w·k)`, `k = |ℓ|`: the codec lands in the
    canonical range. -/
theorem limbsToNat_lt {w : Nat} (ℓ : List (BitVec w)) :
    limbsToNat ℓ < 2 ^ (w * ℓ.length) := by
  induction ℓ with
  | nil => simp
  | cons a ℓ ih =>
    have hpow : w * (ℓ.length + 1) = w + w * ℓ.length := by
      rw [Nat.mul_succ, Nat.add_comm]
    simp only [limbsToNat_cons, List.length_cons]
    have ha := a.isLt
    rw [hpow, Nat.pow_add]
    calc a.toNat + 2 ^ w * limbsToNat ℓ
        < 2 ^ w + 2 ^ w * limbsToNat ℓ := by omega
      _ ≤ 2 ^ w + 2 ^ w * (2 ^ (w * ℓ.length) - 1) := by
            have : limbsToNat ℓ ≤ 2 ^ (w * ℓ.length) - 1 := by omega
            exact Nat.add_le_add_left (Nat.mul_le_mul_left _ this) _
      _ = 2 ^ w * 2 ^ (w * ℓ.length) := by
            have hpos : 0 < 2 ^ (w * ℓ.length) := Nat.two_pow_pos _
            rw [Nat.mul_sub_one]
            have : 2 ^ w ≤ 2 ^ w * 2 ^ (w * ℓ.length) :=
              Nat.le_mul_of_pos_right _ hpos
            omega

/-- **C4: limb codec round-trip / bijection on the canonical range.** Reading
    `k` little-endian limbs out of a value `< 2^(w·k)` and re-serializing
    recovers the value. Concretely: `limbsToNat ∘ toLimbs = id` on `[0, 2^(w·k))`.
    We state it as the recovery identity for the explicit `toLimbs` below. -/
def toLimbs {w : Nat} : Nat → (k : Nat) → List (BitVec w)
  | _, 0 => []
  | n, (k+1) => BitVec.ofNat w n :: toLimbs (n / 2 ^ w) k

@[simp] theorem toLimbs_zero {w : Nat} (n : Nat) : toLimbs (w := w) n 0 = [] := rfl

@[simp] theorem toLimbs_length {w : Nat} (n k : Nat) :
    (toLimbs (w := w) n k).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [toLimbs, ih]

/-- The codec round-trip: `limbsToNat (toLimbs n k) = n % 2^(w·k)`; on the
    canonical range `n < 2^(w·k)` this is `n` (`limbsToNat_toLimbs_of_lt`). -/
theorem limbsToNat_toLimbs {w : Nat} (n k : Nat) :
    limbsToNat (toLimbs (w := w) n k) = n % 2 ^ (w * k) := by
  induction k generalizing n with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    have hpow : w * (k + 1) = w + w * k := by
      rw [Nat.mul_succ, Nat.add_comm]
    simp only [toLimbs, limbsToNat_cons, BitVec.toNat_ofNat, ih]
    rw [hpow, Nat.pow_add, Nat.mod_mul]

/-- C4 on the canonical range: `n < 2^(w·k) ⇒ limbsToNat (toLimbs n k) = n`. -/
theorem limbsToNat_toLimbs_of_lt {w : Nat} {n k : Nat} (h : n < 2 ^ (w * k)) :
    limbsToNat (toLimbs (w := w) n k) = n := by
  rw [limbsToNat_toLimbs, Nat.mod_eq_of_lt h]

/-! ## 3. The schoolbook identity (task C5 core)

`schoolbook_eq_mul4` is the distributive product `(Σ xᵢ Bⁱ)(Σ yⱼ Bʲ) = Σᵢⱼ xᵢyⱼ
B^(i+j)` specialised to four limbs each — exactly the partial-product layout of
`bignum_mul_4_8`. The `B := 2^w` powers are kept as `2^0, 2^w, 2^(2w), …` so the
identity holds at every word width without `ring` (only `Nat.pow_add` +
`Nat.mul_add`/`Nat.add_mul` rearrangement). This is the algebraic content the
DECARRY carry-chain trace must land on.

`B := 2^w`. The sixteen partial products `pᵢⱼ = xᵢ·yⱼ` accumulate at weight
`B^(i+j)`. Writing `bₖ := 2^(w·k)`, the identity is
`(x₀+x₁b₁+x₂b₂+x₃b₃)(y₀+y₁b₁+y₂b₂+y₃b₃) = Σᵢⱼ xᵢyⱼ bᵢ₊ⱼ`. -/

/-- Abbreviation for the `k`-th little-endian weight `2^(w·k)`. -/
def wpow (w k : Nat) : Nat := 2 ^ (w * k)

theorem wpow_zero (w : Nat) : wpow w 0 = 1 := by simp [wpow]

theorem wpow_one (w : Nat) : wpow w 1 = 2 ^ w := by simp [wpow]

/-- Weights multiply additively: `bᵢ · bⱼ = bᵢ₊ⱼ`. The single fact that turns
    the limb-product expansion into a reindexed double sum. -/
theorem wpow_mul (w i j : Nat) : wpow w i * wpow w j = wpow w (i + j) := by
  unfold wpow
  rw [← Nat.pow_add, Nat.mul_add]

/-- The weight `bₖ` is the `k`-th power of the base `b₁ = 2^w`. Lets `ring`
    discharge the schoolbook expansion (it normalises `bⁱ·bʲ = bⁱ⁺ʲ`). -/
theorem wpow_eq_pow (w k : Nat) : wpow w k = (2 ^ w) ^ k := by
  unfold wpow; rw [← Nat.pow_mul]

/-- **C5 core, 4-limb schoolbook = product.** The product of two 4-limb
    little-endian integers equals the weighted sum of the sixteen partial
    products `xᵢ·yⱼ` at weight `2^(w·(i+j))`. Width-generic; no `ring` (uses only
    `wpow_mul` + `Nat` add/mul distribution). Reusable as the algebraic target
    for any 4×4 schoolbook kernel (`bignum_mul_4_8`, 4-limb montmul). -/
theorem schoolbook_eq_mul4 (w : Nat) (x0 x1 x2 x3 y0 y1 y2 y3 : Nat) :
    (x0 + x1 * wpow w 1 + x2 * wpow w 2 + x3 * wpow w 3)
        * (y0 + y1 * wpow w 1 + y2 * wpow w 2 + y3 * wpow w 3)
      = x0 * y0 * wpow w 0
        + (x0 * y1 + x1 * y0) * wpow w 1
        + (x0 * y2 + x1 * y1 + x2 * y0) * wpow w 2
        + (x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0) * wpow w 3
        + (x1 * y3 + x2 * y2 + x3 * y1) * wpow w 4
        + (x2 * y3 + x3 * y2) * wpow w 5
        + (x3 * y3) * wpow w 6 := by
  -- express every weight as a power of the base `b = 2^w`; then `ring` normalises
  -- `bⁱ·bʲ = bⁱ⁺ʲ` and closes the distributive identity.
  simp only [wpow_eq_pow]
  ring

/-- **C5 core, 2-limb schoolbook = product.** The 2×2 specialisation, stated
    directly over an abstract base `B` (instantiated at `2^w`): the four partial
    products `xᵢ·yⱼ` accumulate at weights `1, B, B, B²`. The stepping stone for
    the forward driver (`mul24Block`); the 4-limb version is `schoolbook_eq_mul4`.
    `B²` is written `B*B` so the identity is pure `ring` over `Nat`. -/
theorem schoolbook_eq_mul2 (B x0 x1 y0 y1 : Nat) :
    (x0 + B * x1) * (y0 + B * y1)
      = x0 * y0 + B * (x0 * y1 + x1 * y0) + B * B * (x1 * y1) := by
  ring

/-! ## 4. Symbolic stepping kit for `runBlock` traces

`runBlock` over a straight-line block builds a deeply nested state term; reading
a single word back by unfolding the whole history blows up. These `@[simp]`
lemmas resolve a `get`/`load`/flag read against the **immediately preceding**
instruction, keeping the prior state `s` symbolic — so a trace simplifies in
size linear in its length rather than quadratically. They are the structured
analogue of stepping a Hoare triple instruction-by-instruction (the DECARRY
trace discipline), and are reused by every kernel that runs `runBlock`. -/

section Stepping
variable {w : Nat}

/-- `mulxMem` writes `dstLo`/`dstHi`, no flags, no memory. -/
@[simp] theorem get_mulxMem (s : JState w) (dstHi dstLo : String) (a : JOperand)
    (base : String) (off : Int) (r : String) :
    (evalInstr s (.mulxMem dstHi dstLo a base off)).get r
      = if r = dstHi then (wumul (a.eval s) (s.load base off)).1
        else if r = dstLo then (wumul (a.eval s) (s.load base off)).2
        else s.get r := by
  simp only [evalInstr, x86_MULX_lo_hi, wumul, JState.get, JState.setReg]

@[simp] theorem load_mulxMem (s : JState w) (dstHi dstLo : String) (a : JOperand)
    (base : String) (off : Int) (b : String) (o : Int) :
    (evalInstr s (.mulxMem dstHi dstLo a base off)).load b o = s.load b o := rfl

@[simp] theorem cf_mulxMem (s : JState w) (dstHi dstLo : String) (a : JOperand)
    (base : String) (off : Int) :
    (evalInstr s (.mulxMem dstHi dstLo a base off)).flags.cf = s.flags.cf := by
  simp [evalInstr, x86_MULX_lo_hi, JState.setReg]

@[simp] theorem of_mulxMem (s : JState w) (dstHi dstLo : String) (a : JOperand)
    (base : String) (off : Int) :
    (evalInstr s (.mulxMem dstHi dstLo a base off)).flags.of = s.flags.of := by
  simp [evalInstr, x86_MULX_lo_hi, JState.setReg]

/-- `adcx`: writes `dst` and `CF`. -/
@[simp] theorem get_adcx (s : JState w) (dst : String) (src : JOperand) (r : String) :
    (evalInstr s (.adcx dst src)).get r
      = if r = dst then (waddcarry (s.get dst) (src.eval s) (s.flagB (·.cf))).2
        else s.get r := by
  simp only [evalInstr, x86_ADCX, JState.get]

@[simp] theorem cf_adcx (s : JState w) (dst : String) (src : JOperand) :
    (evalInstr s (.adcx dst src)).flags.cf
      = some (waddcarry (s.get dst) (src.eval s) (s.flagB (·.cf))).1 := by
  simp [evalInstr, x86_ADCX]

@[simp] theorem of_adcx (s : JState w) (dst : String) (src : JOperand) :
    (evalInstr s (.adcx dst src)).flags.of = s.flags.of := by
  simp [evalInstr, x86_ADCX]

@[simp] theorem load_adcx (s : JState w) (dst : String) (src : JOperand)
    (b : String) (o : Int) :
    (evalInstr s (.adcx dst src)).load b o = s.load b o := rfl

/-- `adox`: writes `dst` and `OF` (carry-in from `OF`). -/
@[simp] theorem get_adox (s : JState w) (dst : String) (src : JOperand) (r : String) :
    (evalInstr s (.adox dst src)).get r
      = if r = dst then (waddcarry (s.get dst) (src.eval s) (s.flagB (·.of))).2
        else s.get r := by
  simp only [evalInstr, x86_ADCX, JState.get]

@[simp] theorem of_adox (s : JState w) (dst : String) (src : JOperand) :
    (evalInstr s (.adox dst src)).flags.of
      = some (waddcarry (s.get dst) (src.eval s) (s.flagB (·.of))).1 := by
  simp [evalInstr, x86_ADCX]

@[simp] theorem cf_adox (s : JState w) (dst : String) (src : JOperand) :
    (evalInstr s (.adox dst src)).flags.cf = s.flags.cf := by
  simp [evalInstr, x86_ADCX]

@[simp] theorem load_adox (s : JState w) (dst : String) (src : JOperand)
    (b : String) (o : Int) :
    (evalInstr s (.adox dst src)).load b o = s.load b o := rfl

/-- `loadMem`: register write, no flags, no memory change. -/
@[simp] theorem get_loadMem (s : JState w) (dst base : String) (off : Int) (r : String) :
    (evalInstr s (.loadMem dst base off)).get r
      = if r = dst then s.load base off else s.get r := by
  simp only [evalInstr, x86_MOV, JState.get, JState.setReg]

@[simp] theorem load_loadMem (s : JState w) (dst base : String) (off : Int)
    (b : String) (o : Int) :
    (evalInstr s (.loadMem dst base off)).load b o = s.load b o := rfl

@[simp] theorem cf_loadMem (s : JState w) (dst base : String) (off : Int) :
    (evalInstr s (.loadMem dst base off)).flags.cf = s.flags.cf := rfl

@[simp] theorem of_loadMem (s : JState w) (dst base : String) (off : Int) :
    (evalInstr s (.loadMem dst base off)).flags.of = s.flags.of := rfl

/-- `storeMem`: memory write, registers and flags unchanged. -/
@[simp] theorem get_storeMem (s : JState w) (base : String) (off : Int)
    (src : JOperand) (r : String) :
    (evalInstr s (.storeMem base off src)).get r = s.get r := rfl

@[simp] theorem load_storeMem (s : JState w) (base : String) (off : Int)
    (src : JOperand) (b : String) (o : Int) :
    (evalInstr s (.storeMem base off src)).load b o
      = if b = base ∧ o = off then x86_MOV (src.eval s) else s.load b o := by
  simp only [evalInstr, JState.store, JState.load]

@[simp] theorem cf_storeMem (s : JState w) (base : String) (off : Int) (src : JOperand) :
    (evalInstr s (.storeMem base off src)).flags.cf = s.flags.cf := rfl

@[simp] theorem of_storeMem (s : JState w) (base : String) (off : Int) (src : JOperand) :
    (evalInstr s (.storeMem base off src)).flags.of = s.flags.of := rfl

/-- `mov`: register write, no flags. -/
@[simp] theorem get_mov (s : JState w) (dst : String) (src : JOperand) (r : String) :
    (evalInstr s (.mov dst src)).get r
      = if r = dst then src.eval s else s.get r := by
  simp only [evalInstr, x86_MOV, JState.get, JState.setReg]

@[simp] theorem load_mov (s : JState w) (dst : String) (src : JOperand)
    (b : String) (o : Int) :
    (evalInstr s (.mov dst src)).load b o = s.load b o := rfl

@[simp] theorem cf_mov (s : JState w) (dst : String) (src : JOperand) :
    (evalInstr s (.mov dst src)).flags.cf = s.flags.cf := rfl

@[simp] theorem of_mov (s : JState w) (dst : String) (src : JOperand) :
    (evalInstr s (.mov dst src)).flags.of = s.flags.of := rfl

/-- `xor_`: bitwise; clears `CF` and `OF` (the carry-chain reset). -/
@[simp] theorem get_xor (s : JState w) (dst : String) (src : JOperand) (r : String) :
    (evalInstr s (.xor_ dst src)).get r
      = if r = dst then x86_XOR (s.get dst) (src.eval s) |>.word else s.get r := by
  simp only [evalInstr, JState.get, JState.writeB5W]

@[simp] theorem cf_xor (s : JState w) (dst : String) (src : JOperand) :
    (evalInstr s (.xor_ dst src)).flags.cf = some false := by
  simp [evalInstr, x86_XOR, rflags_of_bwop, JState.writeB5W]

@[simp] theorem of_xor (s : JState w) (dst : String) (src : JOperand) :
    (evalInstr s (.xor_ dst src)).flags.of = some false := by
  simp [evalInstr, x86_XOR, rflags_of_bwop, JState.writeB5W]

@[simp] theorem load_xor (s : JState w) (dst : String) (src : JOperand)
    (b : String) (o : Int) :
    (evalInstr s (.xor_ dst src)).load b o = s.load b o := by
  simp [evalInstr, JState.writeB5W, JState.load]

/-- `runBlock` over a concatenation runs the prefix then the suffix. Lets a long
    trace be chunked (e.g. per schoolbook row) with `generalize` of the
    intermediate state, keeping each chunk's symbolic term small. -/
theorem runBlock_append (s : JState w) (l₁ l₂ : List (JInstr w)) :
    runBlock s (l₁ ++ l₂) = runBlock (runBlock s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runBlock_cons, ih]

end Stepping

/-! ## 5. The genuine-reasoning bignum lemma library (SB-finish, #340)

The s2n-bignum-bench "reasoning fraction" (the ~16 % of obligations that a blunt
`bv_decide`/`omega`/`grind` cascade does **not** close on its own — see
`bench/s2n_bignum_bench_sample/SampleLarge.lean`) splits into three reusable
families, each of which is a single generic lemma that the concrete obligations
are instances of:

* **Carry / borrow characterizations** — the `ADD`/`SUB` no-overflow iff over a
  wrapped `mod`. The `<` and `≥` directions each need a separate
  `Nat.mod_eq_of_lt` argument, which is why the cascade cannot synthesize them.
* **Lexicographic comparison** — `B·h + l ⋚ B·h' + l'` with `l, l' < B`,
  needing trichotomy + the `B·(h+1) ≤ B·h'` monotonicity step.
* **Overflow bounds** — a manual "the product fits in the word" bound supplied
  *before* `omega`/`nlinarith` discharges.
* **Recursive-codec induction** — round-trip / bound / append for the
  little-endian limb codec; structural induction over the recursive definition.

These are stated width- and base-generic so every concrete kernel obligation
(`bignum_mul_4_8`, montmul, the wordlist codec, ...) is one `exact`/`simpa`
away. The `bignum_reason` tactic (`CatCrypt/Tactic/BignumReason.lean`) packages
them into a single `@[grind]`/`@[simp]` database plus the bv↔Nat bridge. -/

section ReasoningLibrary

/-! ### 5a. Carry / borrow (the `NOCARRY_*`/`CARRY_*` family) -/

/-- **No-overflow add, generic width.** `x + y = (x + y) mod 2^w` iff the sum
    has not wrapped. The reassembly of `waddcarry_decompose` for the carry-out
    `= false` case; the additive analogue of the limb-codec identities. -/
theorem nocarry_add_iff {w : Nat} (x y : BitVec w) :
    (x.toNat + y.toNat = (x + y).toNat) ↔ (x.toNat + y.toNat < 2 ^ w) := by
  rw [BitVec.toNat_add]
  have hx := x.isLt; have hy := y.isLt
  constructor
  · intro h; omega
  · intro h; rw [Nat.mod_eq_of_lt h]

/-- **Carry-out add, generic width.** Negation of `nocarry_add_iff`: a carry
    occurs iff the unbounded sum reaches `2^w`. -/
theorem carry_add_iff {w : Nat} (x y : BitVec w) :
    ¬ (x.toNat + y.toNat = (x + y).toNat) ↔ (2 ^ w ≤ x.toNat + y.toNat) := by
  rw [nocarry_add_iff]; omega

/-- **No-borrow sub, generic width** (the `NOCARRY_WORD_SUB` ℤ form). The signed
    integer difference equals the wrapped word difference iff `y ≤ x`; the `<`
    direction relies on the wrapped value `2^w - (y-x)` being large. -/
theorem noborrow_sub_iff {w : Nat} (x y : BitVec w) :
    ((x.toNat : ℤ) - y.toNat = ((x - y).toNat : ℤ)) ↔ y.toNat ≤ x.toNat := by
  rw [BitVec.toNat_sub]
  have hx := x.isLt; have hy := y.isLt
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw; simp_all [Nat.lt_one_iff]
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    rw [Nat.mod_eq_of_lt (by omega : 2 ^ w - y.toNat + x.toNat < 2 ^ w)] at h
    push_cast [Nat.sub_add_comm (le_of_lt hy)] at h
    omega
  · intro h
    rw [show 2 ^ w - y.toNat + x.toNat = 2 ^ w + (x.toNat - y.toNat) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : x.toNat - y.toNat < 2 ^ w)]
    push_cast [h]; omega

/-! ### 5b. Lexicographic comparison of two-limb numbers -/

/-- **Lexicographic `<`.** With both low parts `< B`, the radix-`B` pair compares
    lexicographically: `B·h + l < B·h' + l' ↔ h < h' ∨ (h = h' ∧ l < l')`. The
    `←` direction needs the `B·(h+1) ≤ B·h'` monotonicity step (not an `omega`
    fact, since `B` is a variable). The carry of `num_of_wordlist`-comparison. -/
theorem lexicographic_lt (B h l h' l' : Nat) (hl : l < B) (hl' : l' < B) :
    (B * h + l < B * h' + l') ↔ (h < h' ∨ (h = h' ∧ l < l')) := by
  constructor
  · intro hlt
    rcases lt_trichotomy h h' with hh | hh | hh
    · exact Or.inl hh
    · subst hh; right; exact ⟨rfl, by omega⟩
    · exfalso
      have : B * h' + B ≤ B * h := by
        have : B * (h' + 1) ≤ B * h := Nat.mul_le_mul_left B hh
        simpa [Nat.mul_add] using this
      omega
  · rintro (hh | ⟨rfl, hh⟩)
    · have : B * (h + 1) ≤ B * h' := Nat.mul_le_mul_left B hh
      have hexp : B * h + B ≤ B * h' := by simpa [Nat.mul_add] using this
      omega
    · omega

/-- **Lexicographic `=`.** With both low parts `< B`, equality of the radix-`B`
    pairs forces both components equal. -/
theorem lexicographic_eq (B h l h' l' : Nat) (hl : l < B) (hl' : l' < B) :
    (B * h + l = B * h' + l') ↔ (h = h' ∧ l = l') := by
  constructor
  · intro heq
    rcases lt_trichotomy h h' with hh | hh | hh
    · exfalso
      have : B * (h + 1) ≤ B * h' := Nat.mul_le_mul_left B hh
      have : B * h + B ≤ B * h' := by simpa [Nat.mul_add] using this
      omega
    · subst hh; exact ⟨rfl, by omega⟩
    · exfalso
      have : B * (h' + 1) ≤ B * h := Nat.mul_le_mul_left B hh
      have : B * h' + B ≤ B * h := by simpa [Nat.mul_add] using this
      omega
  · rintro ⟨rfl, rfl⟩; rfl

/-! ### 5c. Overflow / "fits in the word" bounds -/

/-- **Product fits.** `0 < m, a < m, b < m, c ≤ m ⇒ c·a + b < m²`: the
    fused-multiply-add bound the cascade needs supplied before `nlinarith`. -/
theorem mul_add_lt (a b c m : Nat) (_h0 : 0 < m) (ha : a < m) (hb : b < m)
    (hc : c ≤ m) : c * a + b < m * m := by
  have h1 : c * a ≤ m * a := Nat.mul_le_mul_right a hc
  have h2 : m * a + m ≤ m * m := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left m ha
  omega

/-- **A `wᵢ`-bit × `wⱼ`-bit product fits in `wᵢ+wⱼ` bits.** The no-overflow side
    condition for `MULX`/`MADDL`-style fused products before the `mod` drops. -/
theorem mul_lt_pow_add {wx wy : Nat} (x : BitVec wx) (y : BitVec wy) :
    x.toNat * y.toNat < 2 ^ (wx + wy) := by
  have hx := x.isLt; have hy := y.isLt
  calc x.toNat * y.toNat < 2 ^ wx * 2 ^ wy :=
        Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (Nat.two_pow_pos _)
    _ = 2 ^ (wx + wy) := (Nat.pow_add 2 wx wy).symm

/-! ### 5d. The recursive limb codec, the inductive core (round-trip both ways)

`limbsToNat` / `toLimbs` (§2) are the base-generic version of s2n's
`num_of_wordlist` / `wordlist_of_num`. `limbsToNat_append` (§2) is
`NUM_OF_WORDLIST_APPEND`, `limbsToNat_lt` is `NUM_OF_WORDLIST_BOUND`, and
`limbsToNat_toLimbs` is the forward round-trip. The reverse round-trip
(`WORDLIST_OF_NUM_OF_WORDLIST`, the H1 case) is the missing list induction. -/

/-- One limb of a value reads off the head: the `MOD 2^w` digit. -/
theorem limbsToNat_cons_mod {w : Nat} (a : BitVec w) (ℓ : List (BitVec w)) :
    limbsToNat (a :: ℓ) % 2 ^ w = a.toNat := by
  simp only [limbsToNat_cons]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]

/-- Dropping the head limb is integer division by `2^w`. -/
theorem limbsToNat_cons_div {w : Nat} (a : BitVec w) (ℓ : List (BitVec w)) :
    limbsToNat (a :: ℓ) / 2 ^ w = limbsToNat ℓ := by
  simp only [limbsToNat_cons]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos w),
    Nat.div_eq_of_lt a.isLt, Nat.zero_add]

/-- **Reverse codec round-trip (H1 core), the list induction.** Serializing a
    limb list to its `Nat` and re-reading `|ℓ|` limbs recovers `ℓ` exactly.
    `limbsToNat` and `toLimbs` are mutually inverse on lists. -/
theorem toLimbs_limbsToNat {w : Nat} (ℓ : List (BitVec w)) :
    toLimbs (limbsToNat ℓ) ℓ.length = ℓ := by
  induction ℓ with
  | nil => rfl
  | cons a ℓ ih =>
    simp only [List.length_cons, toLimbs, List.cons.injEq]
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, limbsToNat_cons_mod]
    · rw [limbsToNat_cons_div]; exact ih

/-- **Cons round-trip on `Nat` (`WORDLIST_OF_NUM` step).** Building the codec of
    `n` at length `k+1` peels the low limb then recurses on `n / 2^w`. -/
theorem limbsToNat_eq_cons {w : Nat} (n k : Nat) :
    limbsToNat (toLimbs (w := w) n (k + 1))
      = (BitVec.ofNat w n).toNat + 2 ^ w * limbsToNat (toLimbs (w := w) (n / 2 ^ w) k) := by
  simp only [toLimbs, limbsToNat_cons]

/-- **Mod-invariance of the codec** (`WORDLIST_OF_NUM_MOD`): reading `k` limbs
    only sees `n mod 2^(w·k)`, so reducing `n` first is a no-op. -/
theorem toLimbs_mod {w : Nat} (n k : Nat) :
    toLimbs (w := w) (n % 2 ^ (w * k)) k = toLimbs (w := w) n k := by
  have h := toLimbs_limbsToNat (toLimbs (w := w) n k)
  rw [toLimbs_length, limbsToNat_toLimbs] at h
  exact h

/-- **Cons-equality via lexicographic_eq (H2 core).** Two limb lists with equal
    heads-and-tails iff equal as numbers, head-first. -/
theorem limbsToNat_cons_eq_iff {w : Nat} (a b : BitVec w) (ℓ₁ ℓ₂ : List (BitVec w)) :
    (limbsToNat (a :: ℓ₁) = limbsToNat (b :: ℓ₂))
      ↔ (a = b ∧ limbsToNat ℓ₁ = limbsToNat ℓ₂) := by
  simp only [limbsToNat_cons]
  rw [add_comm a.toNat, add_comm b.toNat,
    lexicographic_eq (2 ^ w) _ _ _ _ a.isLt b.isLt]
  constructor
  · rintro ⟨hl, hv⟩; exact ⟨BitVec.eq_of_toNat_eq hv, hl⟩
  · rintro ⟨rfl, hl⟩; exact ⟨hl, rfl⟩

/-- **Cons-`<` via lexicographic_lt (H3 core).** Comparison of two limb lists
    reduces (tail-first, MSB-dominant) to their head/tail comparison. -/
theorem limbsToNat_cons_lt_iff {w : Nat} (a b : BitVec w) (ℓ₁ ℓ₂ : List (BitVec w)) :
    (limbsToNat (a :: ℓ₁) < limbsToNat (b :: ℓ₂))
      ↔ (limbsToNat ℓ₁ < limbsToNat ℓ₂ ∨
          (limbsToNat ℓ₁ = limbsToNat ℓ₂ ∧ a.toNat < b.toNat)) := by
  simp only [limbsToNat_cons]
  rw [add_comm a.toNat, add_comm b.toNat]
  exact lexicographic_lt (2 ^ w) _ _ _ _ a.isLt b.isLt

end ReasoningLibrary

end CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
