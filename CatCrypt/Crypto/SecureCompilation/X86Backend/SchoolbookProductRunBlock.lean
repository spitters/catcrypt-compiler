/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import Mathlib.Data.List.GetD

public import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookRunBlock

/-!
# The full 256×256 schoolbook product over a single `runBlock`

`SchoolbookRunBlock.lean` proves one emitted schoolbook *row* `t += x·c` over
`runBlock` equals the abstract `Cios4LimbProven.addmul1`
(`emitRowBlock_runBlock_value`, flag-resetting, axiom-clean). It left the
inter-row combine — the accumulation of successive rows into the full
schoolbook product `mulLimbs x y` — as the named remainder.

This file closes that remainder. It emits the full schoolbook product as a
sequence of rows over a *single* shared accumulator register file
(`emitProductBlock`), accumulating row `j` (`x · y_j`) into the accumulator at
word offset `j`, and proves by induction over the multiplier-limb list that the
emitted block's `runBlock` output, read out of the accumulator registers,
recombines (`valLimbs`) to `valLimbs x · valLimbs y` — and hence to
`valLimbs (mulLimbs x y)` via the proven `mulLimbs_reconstruct`.

## The offset-accumulation emit (genuine inter-row combine over `runBlock`)

The schoolbook product is `T := 0; for each y-limb j: T[j ..] += x · y_j`. Each
inner `T[j ..] += x · y_j` is exactly one emitted row (`emitRowBlock`), entered
flag-clear, writing its result limbs back into the accumulator register slice
`accs.drop j` and its carry-out word into the next free accumulator register
`accs[j + |x|]` (the row's carry, materialised by `emitColumnReset`'s gadget and
copied into that register). Because each row resets the carry flags and routes
its carry into a *distinct* accumulator register, the rows compose over one
`runBlock` trace with NO persistent-flag induction — the same flag-resetting
idiom as the single row.

The accumulation invariant proven is

  `valLimbs (accs after rows 0..j-1)  =  valLimbs x · valLimbs (y.take j)`

so after all `|y|` rows the accumulator holds `valLimbs x · valLimbs y`.

## What is proven (genuine `runBlock(emitted) = spec`)

* `emitProductBlock` / `emitProductBlock_runBlock_value` — the full schoolbook
  product as one emitted `List (JInstr 64)`; its `runBlock` output, read out of
  the accumulator registers, recombines to `valLimbs x · valLimbs y`
  (= `valLimbs (mulLimbs x y)` by `mulLimbs_reconstruct`). The genuine full
  multiply over `runBlock`.
* `sm2_emit_montmul_runBlock_full` — with reduced 4-limb inputs, the emitted
  256×256 product over `runBlock` fed to the proven SM2 4-word Montgomery
  reduction (`montRedc4`, `n' = 1`) lands `< 2·p_sm2` and
  `· 2^256 ≡ valLimbs x · valLimbs y (mod p_sm2)` — the full
  `runBlock(emitted) = SM2 mont-mul spec` (Tier A for SM2).

## Scope (honest)

This is the **flag-resetting** full product (each row re-enters `CF = OF = 0`,
one `ADCX`/`ADOX imm0` pair per column). The persistent-flag / full-ILP ADX
schedule (no per-column reset, marginally faster) is a separate
*perf-equivalence* increment; it does not change the value spec proven here.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MulxSelect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookRunBlock

/-! ## 1. The full schoolbook product as offset-accumulated emitted rows

`emitProductBlock accs as ys hi lo` emits one schoolbook row per `y`-limb,
accumulating into the shared accumulator register file `accs`. The recursion is
on the `y`-limb register list `ys`: at each step the head `y`-limb's row writes
into the length-`|as|` slice `accs.take |as|`, threading its carry-out word into
the register `accs[|as|]` (used as the row's `cy`); the recursive call shifts
the accumulator window by one (`accs.tail`), realising the word offset. -/

/-- The full emitted schoolbook product `T += Σⱼ x · y_j · 2^{64j}`: one
    `emitRowBlock` per `y`-limb over the shared accumulator file `accs`. The head
    row accumulates `x · y_head` into `accs.take |as|`, with the carry register
    `accs[|as|]` (the next free accumulator word); the recursion shifts to
    `accs.tail`, giving the per-limb word offset. `as` are the `x`-limb sources,
    `ys` the `y`-limb scalar registers, `hi`/`lo` the `MULX` scratch. -/
def emitProductBlock : List String → List String → List String → String → String →
    List (JInstr 64)
  | _, _, [], _, _ => []
  | accs, as, y :: ys, hi, lo =>
      emitRowBlock (accs.take as.length) as y (accs.getD as.length default) hi lo
        ++ emitProductBlock accs.tail as ys hi lo

/-! ## 2. Register-layout freshness for the full product

`ProdFresh accs as cy0 hi lo` packages the register distinctness needed for the
multi-row product over the shared accumulator file `accs`: the `x`-limb sources
`as`, the `MULX` scratch `hi`/`lo`, and the accumulator file (whose tail words
double as the per-row carry registers). It strengthens `RowFresh` to the whole
file: `accs` is `Nodup`, disjoint from `as`/`hi`/`lo`, and every contiguous
length-`|as|` window of `accs` (one per `y`-limb) satisfies the per-row
`RowFresh` together with the next accumulator word as its carry register. -/

/-- The freshness predicate for the full product over the accumulator file
    `accs`, the `x`-sources `as`, the `y`-scalar registers `ys`, and the `MULX`
    scratch `hi`/`lo`. The accumulator file is `Nodup`, every accumulator register
    is distinct from each `x`-source, each `y`-scalar, and the scratch; the data
    register classes are mutually disjoint. This is enough to derive each row's
    `RowFresh` (the carry register being the next accumulator word, distinct from
    the window by `Nodup`). -/
structure ProdFresh (accs as ys : List String) (hi lo : String) : Prop where
  /-- scratch words distinct -/
  lo_hi : lo ≠ hi
  /-- every accumulator register avoids the scratch words -/
  acc_hi : ∀ r ∈ accs, r ≠ hi
  acc_lo : ∀ r ∈ accs, r ≠ lo
  /-- every `x`-source avoids the scratch words -/
  a_hi : ∀ r ∈ as, r ≠ hi
  a_lo : ∀ r ∈ as, r ≠ lo
  /-- every `y`-scalar register avoids the scratch and accumulators -/
  y_hi : ∀ r ∈ ys, r ≠ hi
  y_lo : ∀ r ∈ ys, r ≠ lo
  y_acc : ∀ r ∈ ys, ∀ q ∈ accs, r ≠ q
  /-- the accumulator file is duplicate-free -/
  accs_nodup : accs.Nodup
  /-- accumulator and `x`-source registers are disjoint -/
  acc_a : ∀ r ∈ accs, ∀ q ∈ as, r ≠ q

/-! ## 3. The head row's `RowFresh` and the carry register

For the head `y`-limb the row operates on the window `accs.take |as|` with carry
register `accs[|as|]` (the next accumulator word). `prodFresh_head_rowFresh`
derives the per-row `RowFresh` from `ProdFresh`; the carry register being the
next accumulator word is distinct from the whole window (and from `as`) by
`Nodup` / disjointness. -/

/-- The carry register `accs[|as|]` is a member of `accs` (when there are enough
    accumulator words). -/
theorem cyReg_mem (accs as : List String) (h : as.length < accs.length) :
    accs.getD as.length default ∈ accs := by
  rw [List.getD_eq_getElem accs default h]
  exact List.getElem_mem h

/-- A register in the head window `accs.take |as|` is distinct from the carry
    register `accs[|as|]`, because the file is `Nodup` and the indices differ. -/
theorem window_ne_cyReg (accs as : List String) (hnodup : accs.Nodup)
    (h : as.length < accs.length) (r : String) (hr : r ∈ accs.take as.length) :
    r ≠ accs.getD as.length default := by
  rw [List.getD_eq_getElem accs default h]
  -- r is at some index i < as.length in accs; the carry word is at index as.length
  obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hr
  rw [List.length_take] at hi
  have hi' : i < as.length := by omega
  have hilt : i < accs.length := by omega
  rw [List.getElem_take] at hri
  intro hcontra
  rw [← hri] at hcontra
  -- accs[i] = accs[as.length] with i ≠ as.length contradicts Nodup
  have := (List.Nodup.getElem_inj_iff hnodup (i := i) (j := as.length)).mp hcontra
  omega

/-- **The head row's `RowFresh`.** From `ProdFresh` and matching lengths
    (`|as| = |window|`, `|as| < |accs|`, `|ys| ≥ 1`), the head `y`-limb's row —
    window `accs.take |as|`, scalar `y` (the head of `ys`), carry register
    `accs[|as|]`, scratch `hi`/`lo` — satisfies `RowFresh`. -/
theorem prodFresh_head_rowFresh (accs as ys : List String) (hi lo : String)
    (y : String) (hy : y ∈ ys)
    (hfresh : ProdFresh accs as ys hi lo)
    (hlt : as.length < accs.length) :
    RowFresh (accs.take as.length) as y (accs.getD as.length default) hi lo where
  lo_hi := hfresh.lo_hi
  cy_lo := hfresh.acc_lo _ (cyReg_mem accs as hlt)
  cy_hi := hfresh.acc_hi _ (cyReg_mem accs as hlt)
  cReg_hi := hfresh.y_hi y hy
  cReg_lo := hfresh.y_lo y hy
  cReg_cy := hfresh.y_acc y hy _ (cyReg_mem accs as hlt)
  cReg_acc := fun r hr => hfresh.y_acc y hy r (List.mem_of_mem_take hr)
  acc_lo := fun r hr => hfresh.acc_lo r (List.mem_of_mem_take hr)
  acc_hi := fun r hr => hfresh.acc_hi r (List.mem_of_mem_take hr)
  acc_cy := fun r hr => window_ne_cyReg accs as hfresh.accs_nodup hlt r hr
  a_acc_hd := fun r hr => hfresh.a_hi r hr
  a_lo := fun r hr => hfresh.a_lo r hr
  a_cy := fun r hr => Ne.symm (hfresh.acc_a _ (cyReg_mem accs as hlt) r hr)
  accs_nodup := hfresh.accs_nodup.sublist (List.take_sublist _ _)
  acc_a := fun r hr q hq => hfresh.acc_a r (List.mem_of_mem_take hr) q hq

/-- Split a limb value at index `n`: low part plus the shifted high part. -/
theorem valLimbs_split (l : List (BitVec 64)) (n : Nat) :
    valLimbs l = valLimbs (l.take n)
      + (2 ^ 64) ^ (l.take n).length * valLimbs (l.drop n) := by
  rw [← valLimbs_append, List.take_append_drop]

/-! ## 4. One row accumulates into the whole file

The head row writes its result limbs into the window `accs.take |as|` and its
carry-out into `accs[|as|]`, leaving every higher accumulator word untouched.
With the carry zone (`accs.drop |as|`) cleared on entry, the row's incoming
carry is `0`, so the row adds exactly `valLimbs x · y_head` to the file value
`valLimbs (accs.map ·.get)`. This is the per-row increment of the product
invariant, proven over `runBlock` via `emitRowBlock_valLimbs`. -/

/-- A register at index `≥ |as| + 1` in `accs` (the carry zone beyond the head
    row's carry word) is preserved across the head row, since the row only writes
    the window, the carry register `accs[|as|]`, and the scratch `hi`/`lo`. -/
theorem head_row_preserves_high (accs as : List String) (y cyReg hi lo : String)
    (hnodup : accs.Nodup)
    (hacc_hi : ∀ r ∈ accs, r ≠ hi) (hacc_lo : ∀ r ∈ accs, r ≠ lo)
    (hlt : as.length < accs.length)
    (hcy : cyReg = accs.getD as.length default) (s : JState 64) (r : String)
    (hr : r ∈ accs.drop (as.length + 1)) :
    (runBlock s (emitRowBlock (accs.take as.length) as y cyReg hi lo)).get r = s.get r := by
  have hrmem : r ∈ accs := List.mem_of_mem_drop hr
  -- r is at index ≥ |as|+1; distinct from the window (idx < |as|) and cyReg (idx = |as|)
  obtain ⟨i, hi_lt, hri⟩ := List.getElem_of_mem hr
  rw [List.length_drop] at hi_lt
  rw [List.getElem_drop] at hri
  apply emitRowBlock_preserves
  · -- r ∉ window: window member is at index < |as|, r at index ≥ |as|+1
    intro q hq he
    subst he
    obtain ⟨j, hj_lt, hqj⟩ := List.getElem_of_mem hq
    rw [List.length_take] at hj_lt
    rw [List.getElem_take] at hqj
    have : (as.length + 1 + i) = j := by
      have := (List.Nodup.getElem_inj_iff hnodup
        (i := as.length + 1 + i) (j := j)).mp (by rw [hri, hqj])
      exact this
    omega
  · -- r ≠ cyReg = accs[|as|]
    rw [hcy, List.getD_eq_getElem accs default hlt]
    intro he
    have : (as.length + 1 + i) = as.length :=
      (List.Nodup.getElem_inj_iff hnodup
        (i := as.length + 1 + i) (j := as.length)).mp (by rw [hri, ← he])
    omega
  · exact hacc_hi r hrmem
  · exact hacc_lo r hrmem

/-- **One row accumulates `valLimbs x · y_head` into the file.** With the carry
    zone `accs.drop |as|` cleared on entry (so the row's incoming carry is `0`),
    matching lengths, and `RowFresh`/`ProdFresh` register layout, the head
    `y`-limb's row leaves the accumulator file holding
    `valLimbs (accs.map s.get) + valLimbs x · (s.get y).toNat`, read out of the
    same registers over `runBlock`. This is the per-row increment of the product
    invariant. -/
theorem head_row_file_value (accs as : List String) (x : List (BitVec 64))
    (y cyReg hi lo : String) (s : JState 64)
    (hnodup : accs.Nodup)
    (hacc_hi : ∀ r ∈ accs, r ≠ hi) (hacc_lo : ∀ r ∈ accs, r ≠ lo)
    (hlen : as.length = x.length) (hlt : as.length < accs.length)
    (hcy : cyReg = accs.getD as.length default)
    (hrowfresh : RowFresh (accs.take as.length) as y cyReg hi lo)
    (hx : as.map s.get = x)
    (hclear : ∀ r ∈ accs.drop as.length, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    valLimbs (accs.map (runBlock s (emitRowBlock (accs.take as.length) as y cyReg hi lo)).get)
      = valLimbs (accs.map s.get) + valLimbs x * (s.get y).toNat := by
  set blk := emitRowBlock (accs.take as.length) as y cyReg hi lo with hblk
  set s1 := runBlock s blk with hs1
  -- length facts
  have hwinlen : (accs.take as.length).length = as.length := by
    rw [List.length_take]; omega
  have hxlen : x.length = as.length := hlen.symm
  have htlen : ((accs.take as.length).map s.get).length = (accs.take as.length).length := by
    rw [List.length_map]
  -- the row's `emitRowBlock_valLimbs` with t = window.map s.get, carry = s.get cyReg
  have hcarry0 : s.get cyReg = 0 := by
    rw [hcy, List.getD_eq_getElem accs default hlt]
    exact hclear _ (by
      rw [List.drop_eq_getElem_cons hlt]; exact List.mem_cons_self)
  have hrow := emitRowBlock_valLimbs (accs.take as.length) as x
    ((accs.take as.length).map s.get) (s.get y) y cyReg hi lo s (s.get cyReg)
    hwinlen.symm hxlen htlen hrowfresh hx rfl rfl rfl hcf hof
  -- t.take |x| = t  (since |t| = |window| = |as| = |x|)
  have httake : ((accs.take as.length).map s.get).take x.length
      = (accs.take as.length).map s.get := by
    apply List.take_of_length_le; rw [List.length_map, hwinlen]; omega
  rw [httake, hcarry0] at hrow
  rw [show ((0 : BitVec 64).toNat) = 0 from rfl, Nat.add_zero] at hrow
  -- decompose valLimbs (accs.map s1.get) at index |as|
  have hsplit1 := valLimbs_split (accs.map s1.get) as.length
  have hsplit0 := valLimbs_split (accs.map s.get) as.length
  rw [← List.map_take, ← List.map_drop] at hsplit1 hsplit0
  rw [List.length_map, List.length_take] at hsplit1 hsplit0
  have hmin : min as.length accs.length = as.length := by omega
  rw [hmin] at hsplit1 hsplit0
  -- drop |as| = cyReg :: drop (|as|+1)  (under map)
  have hdrop1 : (accs.drop as.length).map s1.get
      = s1.get cyReg :: (accs.drop (as.length + 1)).map s1.get := by
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, ← List.getD_eq_getElem accs default hlt,
      ← hcy]
  have hdrop0 : (accs.drop as.length).map s.get
      = s.get cyReg :: (accs.drop (as.length + 1)).map s.get := by
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, ← List.getD_eq_getElem accs default hlt,
      ← hcy]
  rw [hdrop1, valLimbs_cons] at hsplit1
  rw [hdrop0, valLimbs_cons, hcarry0] at hsplit0
  -- high zone preserved across the row
  have hhigh : (accs.drop (as.length + 1)).map s1.get
      = (accs.drop (as.length + 1)).map s.get := by
    apply List.map_congr_left
    intro r hr
    exact head_row_preserves_high accs as y cyReg hi lo hnodup hacc_hi hacc_lo hlt hcy s r hr
  rw [hhigh] at hsplit1
  -- the window value after the row = (window.map s1.get); pull from emitRowBlock_valLimbs
  -- hrow : valLimbs (window.map s1.get) + 2^(64·|x|)·(s1.get cyReg) = valLimbs (window.map s.get) + valLimbs x · (s.get y)
  rw [← hblk, ← hs1] at hrow
  -- assemble
  rw [hsplit1, hsplit0]
  -- goal now purely arithmetic in: V_win1, c1 := s1.get cyReg, H := valLimbs(drop(|as|+1) s),
  -- V_win0, and hrow relating V_win1 + 2^(64|x|)·c1 = V_win0 + valLimbs x · y
  set Vwin1 := valLimbs ((accs.take as.length).map s1.get) with hVwin1
  set Vwin0 := valLimbs ((accs.take as.length).map s.get) with hVwin0
  set c1 := (s1.get cyReg).toNat with hc1
  set H := valLimbs ((accs.drop (as.length + 1)).map s.get) with hH
  -- hrow : Vwin1 + (2^64)^|x| * c1 = Vwin0 + valLimbs x * (s.get y).toNat
  rw [hxlen] at hrow
  -- BitVec.toNat 0 = 0; the goal is then linear in hrow after distributing the (2^64)^|as| factor
  rw [show ((0 : BitVec 64).toNat) = 0 from rfl]
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_zero]
  -- goal: Vwin1 + (P*c1 + P*(2^64*H)) = Vwin0 + (0 + P*(2^64*H)) + valLimbs x * y
  omega

/-! ## 5. The full product over `runBlock`

The product block preserves any register outside the accumulator file and the
`MULX` scratch (`emitProductBlock_preserves`). The main theorem
(`emitProductBlock_value`) inducts over the `y`-limb register list: each step
applies `head_row_file_value` (the row accumulates `valLimbs x · y_j` into the
file) and the induction hypothesis on the shifted accumulator window
(`accs.tail`), with the head accumulator word frozen by preservation. -/

/-- The product block writes only the accumulator file `accs` and the scratch
    `hi`/`lo`: a register distinct from every accumulator word and from `hi`/`lo`
    is preserved across the whole emitted product. -/
theorem emitProductBlock_preserves :
    ∀ (accs as ys : List String) (hi lo r : String) (s : JState 64),
      as.length + ys.length ≤ accs.length →
      (∀ q ∈ accs, r ≠ q) → r ≠ hi → r ≠ lo →
      (runBlock s (emitProductBlock accs as ys hi lo)).get r = s.get r := by
  intro accs as ys
  induction ys generalizing accs with
  | nil => intro hi lo r s _ _ _ _; simp [emitProductBlock]
  | cons y ys ih =>
      intro hi lo r s hcap hracc hrhi hrlo
      have hlt : as.length < accs.length := by
        simp only [List.length_cons] at hcap; omega
      rw [emitProductBlock, runBlock_append]
      -- the tail block is over accs.tail
      have hrtail : ∀ q ∈ accs.tail, r ≠ q :=
        fun q hq => hracc q (List.mem_of_mem_tail hq)
      have hcaptail : as.length + ys.length ≤ accs.tail.length := by
        rw [List.length_tail]; simp only [List.length_cons] at hcap; omega
      rw [ih accs.tail hi lo r _ hcaptail hrtail hrhi hrlo]
      -- the head row writes window (⊆ accs), cyReg (∈ accs), hi, lo
      apply emitRowBlock_preserves
      · intro q hq; exact hracc q (List.mem_of_mem_take hq)
      · rw [List.getD_eq_getElem accs default hlt]; exact hracc _ (List.getElem_mem hlt)
      · exact hrhi
      · exact hrlo

/-- Derive the tail `ProdFresh` (drop the head accumulator word and the head
    `y`-scalar) from the full `ProdFresh`. -/
theorem prodFresh_tail (accs as : List String) (y : String) (ys : List String)
    (hi lo : String) (hfresh : ProdFresh accs as (y :: ys) hi lo) :
    ProdFresh accs.tail as ys hi lo where
  lo_hi := hfresh.lo_hi
  acc_hi := fun r hr => hfresh.acc_hi r (List.mem_of_mem_tail hr)
  acc_lo := fun r hr => hfresh.acc_lo r (List.mem_of_mem_tail hr)
  a_hi := hfresh.a_hi
  a_lo := hfresh.a_lo
  y_hi := fun r hr => hfresh.y_hi r (List.mem_cons_of_mem _ hr)
  y_lo := fun r hr => hfresh.y_lo r (List.mem_cons_of_mem _ hr)
  y_acc := fun r hr q hq =>
    hfresh.y_acc r (List.mem_cons_of_mem _ hr) q (List.mem_of_mem_tail hq)
  accs_nodup := hfresh.accs_nodup.sublist (List.tail_sublist _)
  acc_a := fun r hr q hq => hfresh.acc_a r (List.mem_of_mem_tail hr) q hq

/-- **The full schoolbook product over `runBlock`.** Emitting one row per
    `y`-limb into the shared accumulator file `accs` (cleared in its carry zone
    `accs.drop |as|` on entry), with `x = as.map s.get`, `yv = ys.map s.get`,
    matching lengths, enough accumulator words (`|as| + |ys| ≤ |accs|`), the
    `ProdFresh` register layout, and both carry flags clear, the emitted product
    block leaves the accumulator file holding
    `valLimbs (accs.map s.get) + valLimbs x · valLimbs yv`, read out of the same
    registers over `runBlock`. Each row is `head_row_file_value` (the
    flag-resetting emitted row of `SchoolbookRunBlock`); the induction over the
    `y`-limb list threads the running partial product through `accs`. -/
theorem emitProductBlock_value :
    ∀ (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
      (s : JState 64),
      as.length = x.length → ys.length = yv.length →
      as.length + ys.length ≤ accs.length →
      ProdFresh accs as ys hi lo →
      as.map s.get = x → ys.map s.get = yv →
      (∀ r ∈ accs.drop as.length, s.get r = 0) →
      s.flagB (·.cf) = false → s.flagB (·.of) = false →
      valLimbs (accs.map (runBlock s (emitProductBlock accs as ys hi lo)).get)
        = valLimbs (accs.map s.get) + valLimbs x * valLimbs yv := by
  intro accs as ys
  induction ys generalizing accs with
  | nil =>
      intro x yv hi lo s _ hyslen _ _ _ hy _ _ _
      -- empty multiplier: block empty, valLimbs yv = 0
      have hyv : yv = [] := by
        cases yv with
        | nil => rfl
        | cons => simp at hyslen
      subst hyv
      simp only [emitProductBlock, runBlock_nil, valLimbs_nil, Nat.mul_zero, Nat.add_zero]
  | cons y ys ih =>
      intro x yv hi lo s haslen hyslen hcap hfresh hx hy hclear hcf hof
      have hlt : as.length < accs.length := by
        simp only [List.length_cons] at hcap; omega
      -- yv = y0 :: yv'
      cases yv with
      | nil => simp at hyslen
      | cons y0 yv' =>
        simp only [List.map_cons, List.cons.injEq] at hy
        obtain ⟨hyhd, hytl⟩ := hy
        set cyReg := accs.getD as.length default with hcyReg
        set blkHead := emitRowBlock (accs.take as.length) as y cyReg hi lo with hblkHead
        rw [emitProductBlock, runBlock_append]
        set s1 := runBlock s blkHead with hs1
        -- the head-row RowFresh
        have hrowfresh : RowFresh (accs.take as.length) as y cyReg hi lo :=
          prodFresh_head_rowFresh accs as (y :: ys) hi lo y List.mem_cons_self hfresh hlt
        -- the head row's file-accumulation
        have hheadfile : valLimbs (accs.map s1.get)
            = valLimbs (accs.map s.get) + valLimbs x * (s.get y).toNat := by
          rw [hs1, hblkHead]
          exact head_row_file_value accs as x y cyReg hi lo s hfresh.accs_nodup
            hfresh.acc_hi hfresh.acc_lo haslen hlt hcyReg hrowfresh hx hclear hcf hof
        -- preservation facts across the head row for the tail-block hypotheses
        have hpres : ∀ r : String, (∀ q ∈ accs.take as.length, r ≠ q) →
            r ≠ cyReg → r ≠ hi → r ≠ lo → s1.get r = s.get r := by
          intro r h1 h2 h3 h4
          rw [hs1, hblkHead]; exact emitRowBlock_preserves _ _ _ _ _ _ _ _ h1 h2 h3 h4
        -- as-registers survive
        have hxs1 : as.map s1.get = x := by
          rw [← hx]; apply List.map_congr_left; intro r hr
          refine hpres r (fun q hq => Ne.symm (hfresh.acc_a q (List.mem_of_mem_take hq) r hr))
            ?_ (hfresh.a_hi r hr) (hfresh.a_lo r hr)
          rw [hcyReg, List.getD_eq_getElem accs default hlt]
          exact Ne.symm (hfresh.acc_a _ (List.getElem_mem hlt) r hr)
        -- ys-registers survive
        have hys1 : ys.map s1.get = yv' := by
          rw [← hytl]; apply List.map_congr_left; intro r hr
          refine hpres r
            (fun q hq => hfresh.y_acc r (List.mem_cons_of_mem _ hr) q
              (List.mem_of_mem_take hq))
            ?_ (hfresh.y_hi r (List.mem_cons_of_mem _ hr))
            (hfresh.y_lo r (List.mem_cons_of_mem _ hr))
          rw [hcyReg, List.getD_eq_getElem accs default hlt]
          exact hfresh.y_acc r (List.mem_cons_of_mem _ hr) _ (List.getElem_mem hlt)
        -- carry zone of accs.tail still clear in s1
        have htaildrop : accs.tail.drop as.length = accs.drop (as.length + 1) := by
          rw [← List.drop_one, List.drop_drop, Nat.add_comm]
        have hclear1 : ∀ r ∈ accs.tail.drop as.length, s1.get r = 0 := by
          intro r hr
          rw [htaildrop] at hr
          have hpreserve : s1.get r = s.get r := by
            rw [hs1, hblkHead]
            exact head_row_preserves_high accs as y cyReg hi lo hfresh.accs_nodup
              hfresh.acc_hi hfresh.acc_lo hlt hcyReg s r hr
          rw [hpreserve]
          have hmemorig : r ∈ accs.drop as.length := by
            have : accs.drop (as.length + 1) = (accs.drop as.length).drop 1 := by
              rw [List.drop_drop]
            rw [this] at hr; exact List.mem_of_mem_drop hr
          exact hclear r hmemorig
        -- flags clear in s1: the head row resets both (RowFresh value theorem)
        have hflags1 := emitRowBlock_runBlock_value (accs.take as.length) as x
          ((accs.take as.length).map s.get) (s.get y) y cyReg hi lo s (s.get cyReg)
          (by rw [List.length_take]; omega) haslen.symm (by rw [List.length_map])
          hrowfresh hx rfl rfl rfl hcf hof
        obtain ⟨_, _, hs1cf, hs1of⟩ := hflags1
        rw [← hblkHead, ← hs1] at hs1cf hs1of
        -- apply IH on the tail block over accs.tail, from state s1
        have hcaptail : as.length + ys.length ≤ accs.tail.length := by
          rw [List.length_tail]; simp only [List.length_cons] at hcap; omega
        have hihtail := ih accs.tail x yv' hi lo s1 haslen
          (by simp only [List.length_cons] at hyslen; omega) hcaptail
          (prodFresh_tail accs as y ys hi lo hfresh) hxs1 hys1 hclear1 hs1cf hs1of
        -- the final state of the whole block
        set sf := runBlock s1 (emitProductBlock accs.tail as ys hi lo) with hsf
        -- decompose accs = head :: tail (accs is nonempty since |accs| > |as| ≥ 0)
        obtain ⟨a0, acctl, haccs⟩ : ∃ a0 acctl, accs = a0 :: acctl :=
          List.exists_cons_of_ne_nil (by
            intro h; rw [h] at hlt; simp at hlt)
        -- the head accumulator word is frozen through the tail block
        have hhead_acctl : a0 ∉ acctl := by
          have := hfresh.accs_nodup; rw [haccs] at this
          exact (List.nodup_cons.mp this).1
        have htail_eq : accs.tail = acctl := by rw [haccs]; rfl
        have hheadpres : (sf.get a0) = s1.get a0 := by
          rw [hsf, htail_eq]
          refine emitProductBlock_preserves acctl as ys hi lo a0 s1 ?_ ?_ ?_ ?_
          · rw [htail_eq] at hcaptail; exact hcaptail
          · intro q hq he; subst he; exact hhead_acctl hq
          · exact hfresh.acc_hi a0 (by rw [haccs]; exact List.mem_cons_self)
          · exact hfresh.acc_lo a0 (by rw [haccs]; exact List.mem_cons_self)
        -- IH (over accs.tail = acctl) into the final state sf
        rw [htail_eq] at hihtail
        -- the head-row file accumulation, with (s.get y) = y0
        rw [hyhd] at hheadfile
        -- recombination of the head word and tail value at both states
        have hrecombine_s1 : (s1.get a0).toNat + 2 ^ 64 * valLimbs (acctl.map s1.get)
            = valLimbs (accs.map s1.get) := by
          rw [haccs]; simp only [List.map_cons, valLimbs_cons]
        -- goal
        rw [haccs]
        simp only [List.map_cons, valLimbs_cons]
        rw [hheadpres, hihtail]
        -- s1.get a0 + 2^64·(valLimbs(acctl s1) + valLimbs x·valLimbs yv')
        --   = valLimbs(a0::acctl map s) + valLimbs x·(y0 + 2^64·valLimbs yv')
        -- via hheadfile (valLimbs(accs s1)=valLimbs(accs s)+valLimbs x·y0) and hrecombine_s1
        have hrecombine_s : (s.get a0).toNat + 2 ^ 64 * valLimbs (acctl.map s.get)
            = valLimbs (accs.map s.get) := by
          rw [haccs]; simp only [List.map_cons, valLimbs_cons]
        -- linear assembly: expand y0 + 2^64·yv' and use the two recombinations + hheadfile
        rw [Nat.mul_add, Nat.mul_add]
        -- goal: a0_s1 + 2^64·V1_s1 + 2^64·(x·yv') = a0_s + 2^64·V_s + (x·y0 + x·(2^64·yv'))
        nlinarith [hheadfile, hrecombine_s1, hrecombine_s]

/-- The little-endian value the emitted product leaves in the accumulator file
    `accs`, read out of `runBlock` — the value the emitted block computes. -/
def runBlockProductValue (accs as ys : List String) (hi lo : String)
    (s : JState 64) : Nat :=
  valLimbs (accs.map (runBlock s (emitProductBlock accs as ys hi lo)).get)

/-- **The full schoolbook product over `runBlock` equals `valLimbs x · valLimbs y`.**
    Starting from a cleared accumulator file (`accs` all hold `0`), with
    `x = as.map s.get`, `yv = ys.map s.get`, matching lengths, enough accumulator
    words, the `ProdFresh` register layout, and both carry flags clear, the emitted
    product block leaves the accumulator registers holding the value
    `valLimbs x · valLimbs yv` (= `valLimbs (mulLimbs x yv)` by the proven
    `mulLimbs_reconstruct`). This is the genuine full 256×256 multiply over
    `runBlock` of a real emitted `List (JInstr 64)`. -/
theorem emitProductBlock_runBlock_value
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv := by
  have hclear : ∀ r ∈ accs.drop as.length, s.get r = 0 :=
    fun r hr => hacc0 r (List.mem_of_mem_drop hr)
  have hzero : valLimbs (accs.map s.get) = 0 := by
    have hrepl : accs.map s.get = List.replicate accs.length 0 := by
      rw [List.eq_replicate_iff]
      refine ⟨by rw [List.length_map], ?_⟩
      intro b hb
      obtain ⟨r, hr, hrb⟩ := List.mem_map.mp hb
      rw [← hrb]; exact hacc0 r hr
    rw [hrepl, valLimbs_replicate_zero]
  rw [runBlockProductValue]
  rw [emitProductBlock_value accs as ys x yv hi lo s haslen hyslen hcap hfresh hx hy
    hclear hcf hof, hzero, Nat.zero_add]

/-- The emitted full product over `runBlock` recombines to `valLimbs (mulLimbs x y)`
    — the proven `Cios4LimbProven` schoolbook. Direct corollary of
    `emitProductBlock_runBlock_value` and `mulLimbs_reconstruct`. -/
theorem emitProductBlock_runBlock_mulLimbs
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv) (hyne : yv ≠ [])
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    runBlockProductValue accs as ys hi lo s = valLimbs (mulLimbs x yv) := by
  rw [emitProductBlock_runBlock_value accs as ys x yv hi lo s haslen hyslen hcap hfresh
    hx hy hacc0 hcf hof, mulLimbs_reconstruct x yv hyne]

/-! ## 6. SM2 full Tier A: the emitted product over `runBlock` into the reduction

`emitProductBlock_runBlock_value` proves the emitted product block computes
`valLimbs x · valLimbs y` over `runBlock` (a real emitted `List (JInstr 64)`).
Feeding that genuine `runBlock`-produced value to the proven SM2 Montgomery
reduction (`Number.montgomeryMul`/`montgomeryReduce` at the full radix
`R = 2^256`, the SM2 constant `Nprime256`) gives the full
`runBlock(emitted) = SM2 mont-mul spec`: the result lands `< 2·p_sm2` and
`· 2^256 ≡ valLimbs x · valLimbs y (mod p_sm2)`. This is Tier A for SM2 — the
256×256 product is a single emitted `runBlock`, not a `Nat` alias. -/

/-- **SM2 full Montgomery-multiply over `runBlock` (Tier A).** With reduced
    4-limb inputs (`valLimbs x, valLimbs y < p_sm2`), a cleared accumulator file,
    the `ProdFresh` register layout, matching lengths, and the full-radix SM2
    Montgomery constant `Nprime256` (`p_sm2 · Nprime256 ≡ -1 mod 2^256`):

    * the emitted product block's `runBlock` value is exactly
      `valLimbs x · valLimbs y` (`emitProductBlock_runBlock_value`); and
    * `montgomeryReduce p_sm2 (2^256) Nprime256` of that genuine `runBlock` value
      (= `montgomeryMul p_sm2 (2^256) Nprime256 (valLimbs x) (valLimbs y)`) lies in
      `[0, 2·p_sm2)` and `· 2^256 ≡ valLimbs x · valLimbs y (mod p_sm2)`.

    The product is a single emitted `runBlock` of a real `List (JInstr 64)`; the
    reduction law is the prime-parametric `Number.montgomeryMul_correct` at the
    canonical SM2 prime. This is the full `runBlock(emitted) = SM2 mont-mul spec`
    — Tier A. -/
theorem sm2_emit_montmul_runBlock_full
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs sm2Limbs)
    (hy_red : valLimbs yv < valLimbs sm2Limbs)
    (hNprime : (valLimbs sm2Limbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs sm2Limbs) (2 ^ 256) Nprime256
        (runBlockProductValue accs as ys hi lo s) < 2 * valLimbs sm2Limbs ∧
    (Number.montgomeryReduce (valLimbs sm2Limbs) (2 ^ 256) Nprime256
        (runBlockProductValue accs as ys hi lo s)) * 2 ^ 256
      ≡ valLimbs x * valLimbs yv [MOD valLimbs sm2Limbs] := by
  -- the genuine runBlock product value
  have hval : runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv :=
    emitProductBlock_runBlock_value accs as ys x yv hi lo s haslen hyslen hcap hfresh
      hx hy hacc0 hcf hof
  refine ⟨hval, ?_, ?_⟩
  -- SM2 modulus facts
  · have hN : 0 < valLimbs sm2Limbs := by rw [sm2Limbs_value]; norm_num
    have hNleR : valLimbs sm2Limbs ≤ 2 ^ 256 := by rw [sm2Limbs_value]; norm_num
    obtain ⟨hrange, _⟩ := Number.montgomeryMul_correct (valLimbs sm2Limbs) (2 ^ 256)
      Nprime256 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    -- montgomeryMul N R Nprime a b = montgomeryReduce N R Nprime (a*b)
    simpa only [Number.montgomeryMul] using hrange
  · have hN : 0 < valLimbs sm2Limbs := by rw [sm2Limbs_value]; norm_num
    have hNleR : valLimbs sm2Limbs ≤ 2 ^ 256 := by rw [sm2Limbs_value]; norm_num
    obtain ⟨_, hcong⟩ := Number.montgomeryMul_correct (valLimbs sm2Limbs) (2 ^ 256)
      Nprime256 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hcong

/-! ## 7. The 4-limb (256×256) SM2/curve instance

For the SM2/secp256k1 layout the multiplicand and multiplier are four 64-bit
limbs and the product file is eight words. `emitProductBlock4` names that
instance; `sm2_emit_montmul_runBlock_full4` is the SM2 Tier A headline at the
concrete 4-limb shape. -/

/-- The 4-limb (256×256) emitted schoolbook product: 8 accumulator words
    (`accs`), 4 `x`-limb sources (`as`), 4 `y`-limb scalars (`ys`), scratch
    `hi`/`lo`. A thin instance of `emitProductBlock`. -/
def emitProductBlock4 (accs as ys : List String) (hi lo : String) : List (JInstr 64) :=
  emitProductBlock accs as ys hi lo

/-- **SM2 full Montgomery-multiply over `runBlock`, 4-limb instance (Tier A).**
    The 256×256 emitted product (`emitProductBlock4`, 4 `x`-limbs, 4 `y`-limbs,
    8-word file) over `runBlock` fed to the proven SM2 reduction at `R = 2^256`:
    the product value is `valLimbs x · valLimbs y` and its reduction lands
    `< 2·p_sm2` with `· 2^256 ≡ valLimbs x · valLimbs y (mod p_sm2)`. The concrete
    SM2 curve shape of `sm2_emit_montmul_runBlock_full`. -/
theorem sm2_emit_montmul_runBlock_full4
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (hxlen : x.length = 4) (hylen : yv.length = 4)
    (haslen : as.length = 4) (hyslen : ys.length = 4)
    (hacclen : accs.length = 8)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs sm2Limbs)
    (hy_red : valLimbs yv < valLimbs sm2Limbs)
    (hNprime : (valLimbs sm2Limbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get)
        = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs sm2Limbs) (2 ^ 256) Nprime256
        (valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get))
        < 2 * valLimbs sm2Limbs ∧
    (Number.montgomeryReduce (valLimbs sm2Limbs) (2 ^ 256) Nprime256
        (valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get))) * 2 ^ 256
      ≡ valLimbs x * valLimbs yv [MOD valLimbs sm2Limbs] := by
  have := sm2_emit_montmul_runBlock_full accs as ys x yv hi lo s Nprime256
    (by omega) (by omega) (by omega) hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  simpa only [emitProductBlock4, runBlockProductValue] using this

end CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
