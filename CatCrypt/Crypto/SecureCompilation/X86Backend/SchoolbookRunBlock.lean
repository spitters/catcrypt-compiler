/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookEmit

/-!
# Schoolbook multiply over `runBlock`: the flag-resetting multi-column assembly

`SchoolbookEmit.lean` ties one emitted dual-carry `MULX`/`ADCX`/`ADOX` column to
the abstract `Cios4LimbProven.mulAddc` (`emitColumn_eq_mulAddc`), but defers the
multi-column row to the `Nat`-schoolbook (the persistent-`CF`/`OF` flag induction
across all columns of a row, `addmul1`'s single-`macHi`-word carry vs. the
emitted dual-flag chain). This file does that assembly the **flag-resetting**
way, so it reuses the proven per-column lemmas with NO persistent-flag induction.

## The flag-resetting idiom (what makes the induction tractable)

The abstract `addmul1` threads the carry as a single WORD (`macHi`) between
columns. The emitted `selectMulxMac`, run with `CF = OF = 0` on entry, leaves
its carry-out split across two places: the two flag bits `CF`/`OF` and the
`MULX` high register `hi`, with `macHi = hi + cf + of` (the no-wrap fact inside
`emitColumn_eq_mulAddc`). To re-enter the next column at the SAME precondition
(`CF = OF = 0`, carry as a word in a register), each emitted column is followed
by a two-instruction **carry-materialise** gadget:

* `ADCX hi, 0` — fold the `CF` chain bit into `hi` (`hi := hi + cf`, `CF := 0`);
* `ADOX hi, 0` — fold the `OF` chain bit into `hi` (`hi := hi + cf + of`,
  `OF := 0`).

After the gadget, `hi = macHi` (a single word) and both flags are `0`, so the
next column re-enters `emitColumn_eq_mulAddc`'s precondition exactly. This is the
genuine x86 idiom (each `ADCX`/`ADOX imm0` touches only its own flag); it trades
the persistent dual chain for one extra `ADCX`/`ADOX` pair per column — a
flag-reset variant that is marginally slower than the full persistent-flag ADX
schedule, but lets the multi-column `runBlock` value be proven by a clean
induction over the limb list, each step `emitColumn_eq_mulAddc` on a fresh
flags-reset state.

## What is proven (genuine `runBlock(emitted) = spec`)

* `materialiseCarry_value` — the gadget reconstructs `macHi` into `hi` and resets
  both flags, over `runBlock`.
* `emitColumnReset` / `emitColumnReset_value` — one emitted column + the gadget:
  the accumulator word equals `macLo`, the carry register equals `macHi`, flags
  reset, over `runBlock`. This is the per-column bridge to `mulAddc` with the
  flags-reset precondition self-contained.
* `emitRowBlock` / `emitRowBlock_runBlock_value` — one schoolbook row `t += x·c`
  as an emitted `List (JInstr 64)`; the accumulator registers and the carry
  register, read out of `runBlock`, equal the abstract `addmul1 x c t carry`
  output (limbs and carry word). Induction over the limb register list.
* `emitRowBlock_valLimbs` / `emitScalarMul_runBlock_value` — the row's `runBlock`
  output recombines (via the proven `addmul1_reconstruct`) to `valLimbs t +
  valLimbs x · c + carry`; with a cleared accumulator this is the scalar-multiply
  product `valLimbs x · c` (a 256×64→320 row over `runBlock`).
* `sm2_emit_montmul_runBlock` / `sm2_emit_scalarRow_montmul_runBlock` — the SM2
  tie: a value produced over `runBlock` (the scalar-row product, via
  `emitScalarMul_runBlock_value`), fed to the proven 4-word Montgomery reduction
  (`montRedc4`, `n' = 1`), lands `< 2·p_sm2` and `≡ V·(2^256)⁻¹ (mod p_sm2)`.

## What is NOT covered (the named remainder)

The single emitted *row* `t += x·c` over `runBlock` is proven equal to `addmul1`
(the genuine flag-resetting multi-column assembly the column layer deferred). The
full N×N schoolbook product `mulLimbs x y` over a *single* `runBlock` needs the
inter-row combine (`Cios4LimbProven.addLimbs`, the ripple-add of successive rows)
emitted as well — a second multi-block induction with its own register routing.
That is not done here, so the SM2 headline (`sm2_emit_montmul_runBlock`) is stated
over an abstract `runBlock`-produced value `V`, with the *scalar-row* instance
(`sm2_emit_scalarRow_montmul_runBlock`) the proven witness that such a `V` is a
genuine emitted-block product. The 4-row product as one emitted `runBlock` is the
remaining increment.

The persistent-flag / full-ILP ADX schedule (no per-column reset, marginally
faster) is a separate *perf-equivalence* increment, not done here; it does not
change the value spec.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookRunBlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MulxSelect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookEmit

/-! ## 1. The carry-materialise gadget

After one `selectMulxMac acc a b cy hi lo` entered with `CF = OF = 0`, the
carry-out is split across the two flag bits and the `MULX` high register `hi`.
`materialiseCarry hi` folds both flag bits into `hi` (`ADCX hi, 0` then
`ADOX hi, 0`), leaving `hi = hi + cf + of = macHi` and `CF = OF = 0`. -/

/-- The two-instruction carry-materialise gadget: fold the `CF` chain bit into
    `hi` (`ADCX hi, 0`, resetting `CF`), then the `OF` chain bit (`ADOX hi, 0`,
    resetting `OF`). After it `hi` holds the single carry word and both flags are
    reset, re-entering the next column's `CF = OF = 0` precondition. -/
def materialiseCarry (hi : String) : List (JInstr 64) :=
  [ .adcx hi (.imm 0), .adox hi (.imm 0) ]

/-- **The gadget materialises the carry word and resets both flags.** Running
    `materialiseCarry hi` from a state whose `hi` register, `CF` and `OF` bits
    sum to less than `2^64`, leaves `hi` holding exactly that sum and both flags
    cleared (`CF = OF = some false`). The bound is the no-wrap fact from the
    column reconstruction (`macHi < 2^64`). -/
theorem materialiseCarry_value (s : JState 64) (hi : String)
    (h : (s.get hi).toNat + (if s.flagB (·.cf) then 1 else 0)
        + (if s.flagB (·.of) then 1 else 0) < 2 ^ 64) :
    ((runBlock s (materialiseCarry hi)).get hi).toNat
        = (s.get hi).toNat + (if s.flagB (·.cf) then 1 else 0)
          + (if s.flagB (·.of) then 1 else 0)
      ∧ (runBlock s (materialiseCarry hi)).flagB (·.cf) = false
      ∧ (runBlock s (materialiseCarry hi)).flagB (·.of) = false := by
  -- step state after the ADCX hi, 0
  set s1 := evalInstr s (.adcx hi (.imm 0)) with hs1
  -- the ADCX folds CF into hi; its carry-out (= the new CF) and OF chain unchanged
  have hcf1 : s1.flags.cf = some (waddcarry (s.get hi) (0#64) (s.flagB (·.cf))).1 := by
    rw [hs1]; exact cf_adcx s hi (.imm 0)
  have hof1 : s1.flags.of = s.flags.of := by rw [hs1]; exact of_adcx s hi (.imm 0)
  have hgethi1 : s1.get hi = (waddcarry (s.get hi) (0#64) (s.flagB (·.cf))).2 := by
    rw [hs1, get_adcx]; simp only [if_true, JOperand.eval]
  -- the CF chain carry-out is 0 (no wrap: hi + cf < 2^64)
  have d1 := waddcarry_decompose (s.get hi) (0#64) (s.flagB (·.cf))
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at d1
  have hc1 : (waddcarry (s.get hi) (0#64) (s.flagB (·.cf))).1 = false := by
    by_contra hbit
    rw [Bool.not_eq_false] at hbit
    rw [hbit] at d1; simp only [if_true] at d1; omega
  rw [hc1] at d1
  simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero] at d1
  have hgethi1val : (s1.get hi).toNat = (s.get hi).toNat + (if s.flagB (·.cf) then 1 else 0) := by
    rw [hgethi1]; omega
  -- the OF bit s1 reads is the original OF
  have hofbit : s1.flagB (·.of) = s.flagB (·.of) := by
    simp only [JState.flagB, hof1]
  -- the OF chain carry-out is 0 (no wrap: (hi+cf) + of < 2^64)
  have d2 := waddcarry_decompose (s1.get hi) (0#64) (s1.flagB (·.of))
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at d2
  have hc2 : (waddcarry (s1.get hi) (0#64) (s1.flagB (·.of))).1 = false := by
    by_contra hbit
    rw [Bool.not_eq_false] at hbit
    rw [hbit] at d2; simp only [if_true, hofbit] at d2; rw [hgethi1val] at d2; omega
  rw [hc2] at d2
  simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero] at d2
  -- now unfold runBlock = step s1 then ADOX hi, 0
  have hrun : runBlock s (materialiseCarry hi) = evalInstr s1 (.adox hi (.imm 0)) := by
    simp only [materialiseCarry, runBlock_cons, runBlock_nil, ← hs1]
  refine ⟨?_, ?_, ?_⟩
  · -- value: gadget hi register = (hi + cf) + of
    rw [hrun]
    rw [hofbit] at d2
    simp only [get_adox, JOperand.eval, if_true, hofbit]
    rw [d2, hgethi1val]
  · -- CF reset: ADOX leaves CF = s1's CF = (carry-out of ADCX) = false
    rw [hrun]
    simp only [cf_adox, JState.flagB, hcf1, Option.getD_some]
    exact hc1
  · -- OF reset: ADOX's carry-out is hc2
    rw [hrun]
    simp only [of_adox, JState.flagB, JOperand.eval, Option.getD_some]
    exact hc2

/-- The carry-materialise gadget writes only `hi`: any other register is
    unchanged. -/
theorem materialiseCarry_other (s : JState 64) (hi r : String) (hr : r ≠ hi) :
    (runBlock s (materialiseCarry hi)).get r = s.get r := by
  simp only [materialiseCarry, runBlock_cons, runBlock_nil, get_adox, get_adcx,
    if_neg hr]

/-! ## 2. One emitted column with flag reset = one abstract `mulAddc` column

`emitColumnReset acc a b cy hi lo` is one schoolbook column emitted the
flag-resetting way: the dual-carry MAC (`selectMulxMac`), then the carry
gadget folding `CF`/`OF` into `hi` (`materialiseCarry`), then a `MOV cy, hi`
copying the single carry word back into the carry register `cy`. Entered with
`CF = OF = 0` and the carry word in `cy`, it leaves:

* `acc = macLo a b add cin` (the result limb),
* `cy = macHi a b add cin` (the carry word for the next column),
* `CF = OF = 0` (so the next column re-enters at the same precondition),

reusing `emitColumn_eq_mulAddc` (the proven per-column bridge) for the value. -/

/-- One flag-resetting emitted column: dual-carry MAC, carry-materialise gadget,
    then copy the carry word into `cy` for the next column. -/
def emitColumnReset (acc a b cy hi lo : String) : List (JInstr 64) :=
  selectMulxMac acc a b cy hi lo ++ materialiseCarry hi ++ [ .mov cy (.reg hi) ]

/-- After `selectMulxMac`, the `hi` register holds the `MULX` high product word
    `(wumul a b).1`: the `MULX` writes it and the two accumulates (into `acc`,
    `acc ≠ hi` and `lo ≠ hi`) leave it untouched. -/
theorem selectMulxMac_get_hi (s : JState 64) (acc a b cy hi lo : String)
    (hAccHi : acc ≠ hi) (hLoHi : lo ≠ hi) :
    (runBlock s (selectMulxMac acc a b cy hi lo)).get hi
      = (wumul (s.get a) (s.get b)).1 := by
  -- the two accumulates write `acc`; reading `hi` (≠ acc, ≠ lo) falls back to the MULX
  simp only [selectMulxMac, runBlock_cons, runBlock_nil, evalInstr, x86_MULX_lo_hi,
    x86_ADCX, JState.setReg, wumul, if_neg hAccHi, if_neg (Ne.symm hLoHi),
    if_neg (Ne.symm hAccHi), if_true, JOperand.eval, JState.get]

/-- After `selectMulxMac` entered with `CF = OF = 0`, the accumulator holds
    `macLo` and the recombined `selCarry + hi` equals `macHi`. Extracted from the
    column bridge `emitColumn_eq_mulAddc`: the emitted column reconstructs the
    same two-word value as the abstract `mulAddc`, and since both `acc_new` and
    `macLo` are `< 2^64`, the low words and the high words match. -/
theorem selectMulxMac_macLo_macHi (s : JState 64) (acc a b cy hi lo : String)
    (va vb add cin : BitVec 64)
    (hAccLo : acc ≠ lo) (hAccHi : acc ≠ hi)
    (hCyLo : cy ≠ lo) (hCyHi : cy ≠ hi) (hCyAcc : cy ≠ acc)
    (hLoHi : lo ≠ hi)
    (hga : s.get a = va) (hgb : s.get b = vb)
    (hgacc : s.get acc = add) (hgcy : s.get cy = cin)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    (runBlock s (selectMulxMac acc a b cy hi lo)).get acc = macLo va vb add cin
      ∧ selCarry s acc a b cy hi lo + (wumul va vb).1.toNat = (macHi va vb add cin).toNat := by
  have hbridge := emitColumn_eq_mulAddc s acc a b cy hi lo va vb add cin
    hAccLo hAccHi hCyLo hCyHi hCyAcc hLoHi hga hgb hgacc hgcy hcf hof
  -- the value identity: acc_new + 2^64·selCarry + 2^64·hi_prod = macHi·2^64 + macLo
  set accN := (runBlock s (selectMulxMac acc a b cy hi lo)).get acc with haccN
  have haccN_lt : accN.toNat < 2 ^ 64 := accN.isLt
  have hmacLo_lt : (macLo va vb add cin).toNat < 2 ^ 64 := (macLo va vb add cin).isLt
  -- low-word equality and high-word equality from the single Nat identity
  have key : accN.toNat
      + 2 ^ 64 * (selCarry s acc a b cy hi lo + (wumul va vb).1.toNat)
      = (macHi va vb add cin).toNat * 2 ^ 64 + (macLo va vb add cin).toNat := by
    rw [Nat.mul_add]; omega
  refine ⟨?_, ?_⟩
  · -- low word: accN = macLo
    apply BitVec.eq_of_toNat_eq
    -- accN < 2^64, macLo < 2^64; the high blocks are multiples of 2^64
    have := key
    omega
  · -- high word: selCarry + hi_prod = macHi
    have := key
    omega

/-- **One emitted column with flag reset = one abstract `mulAddc` column.**
    Running `emitColumnReset acc a b cy hi lo` from a state with both carry flags
    cleared, multiplier limbs `a = va`, `b = vb`, incoming partial word `add` in
    `acc` and incoming carry word `cin` in `cy`, leaves:

    * `acc = macLo va vb add cin` — the result limb,
    * `cy  = macHi va vb add cin` — the carry word for the next column,
    * `CF = OF = 0` — re-entering the next column's precondition.

    The value is the proven per-column bridge `emitColumn_eq_mulAddc`
    (`selectMulxMac_macLo_macHi`); the carry word is assembled by the gadget
    (`materialiseCarry_value`) over the genuine `runBlock` semantics. The carry
    register `cy` and the `MULX` high register `hi` are distinct (`hCyHi`), so the
    `MOV cy, hi` routing does not clobber the live carry. -/
theorem emitColumnReset_value (s : JState 64) (acc a b cy hi lo : String)
    (va vb add cin : BitVec 64)
    (hAccLo : acc ≠ lo) (hAccHi : acc ≠ hi)
    (hCyLo : cy ≠ lo) (hCyHi : cy ≠ hi) (hCyAcc : cy ≠ acc)
    (hLoHi : lo ≠ hi)
    (hga : s.get a = va) (hgb : s.get b = vb)
    (hgacc : s.get acc = add) (hgcy : s.get cy = cin)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    (runBlock s (emitColumnReset acc a b cy hi lo)).get acc = macLo va vb add cin
      ∧ (runBlock s (emitColumnReset acc a b cy hi lo)).get cy = macHi va vb add cin
      ∧ (runBlock s (emitColumnReset acc a b cy hi lo)).flagB (·.cf) = false
      ∧ (runBlock s (emitColumnReset acc a b cy hi lo)).flagB (·.of) = false := by
  -- per-column value + the carry-word identity from the bridge
  obtain ⟨hacc1, hcarry⟩ := selectMulxMac_macLo_macHi s acc a b cy hi lo va vb add cin
    hAccLo hAccHi hCyLo hCyHi hCyAcc hLoHi hga hgb hgacc hgcy hcf hof
  -- the post-`selectMulxMac` state
  set s1 := runBlock s (selectMulxMac acc a b cy hi lo) with hs1
  -- s1's `hi` register is the MULX high product word
  have hs1hi : s1.get hi = (wumul va vb).1 := by
    rw [hs1, selectMulxMac_get_hi s acc a b cy hi lo hAccHi hLoHi, hga, hgb]
  -- `selCarry s … = (if s1.cf) + (if s1.of)` by definition
  have hselC : selCarry s acc a b cy hi lo
      = (if s1.flagB (·.cf) then 1 else 0) + (if s1.flagB (·.of) then 1 else 0) := rfl
  have hmacHi_lt : (macHi va vb add cin).toNat < 2 ^ 64 := (macHi va vb add cin).isLt
  -- the materialise precondition: s1.hi + cf + of = macHi < 2^64
  have hbound : (s1.get hi).toNat + (if s1.flagB (·.cf) then 1 else 0)
      + (if s1.flagB (·.of) then 1 else 0) < 2 ^ 64 := by
    rw [hs1hi]; omega
  -- run the gadget on s1
  obtain ⟨hmatHi, hmatCf, hmatOf⟩ := materialiseCarry_value s1 hi hbound
  set s2 := runBlock s1 (materialiseCarry hi) with hs2
  -- the gadget hi register = macHi
  have hs2hi : (s2.get hi).toNat = (macHi va vb add cin).toNat := by
    rw [hmatHi, hs1hi]; omega
  -- the gadget leaves acc (≠ hi) at macLo
  have hs2acc : s2.get acc = macLo va vb add cin := by
    rw [hs2, materialiseCarry_other s1 hi acc hAccHi, hacc1]
  -- unfold the whole block: selectMulxMac ++ materialiseCarry ++ [mov cy hi]
  have hrun : runBlock s (emitColumnReset acc a b cy hi lo)
      = evalInstr s2 (.mov cy (.reg hi)) := by
    simp only [emitColumnReset, runBlock_append, runBlock_cons, runBlock_nil, ← hs1, ← hs2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- acc unchanged by the mov (cy ≠ acc)
    rw [hrun]; simp only [get_mov, JOperand.eval, if_neg (Ne.symm hCyAcc), hs2acc]
  · -- cy := hi = macHi
    rw [hrun]; simp only [get_mov, JOperand.eval, if_true]
    exact BitVec.eq_of_toNat_eq hs2hi
  · -- CF reset (mov touches no flag, gadget reset it)
    rw [hrun]; simp only [JState.flagB, cf_mov]; exact hmatCf
  · -- OF reset
    rw [hrun]; simp only [JState.flagB, of_mov]; exact hmatOf

/-- `selectMulxMac` writes only `acc` (the two accumulates), `hi` and `lo` (the
    `MULX`): a register distinct from all three is preserved. -/
theorem selectMulxMac_other (s : JState 64) (acc a b cy hi lo r : String)
    (hr_acc : r ≠ acc) (hr_hi : r ≠ hi) (hr_lo : r ≠ lo) :
    (runBlock s (selectMulxMac acc a b cy hi lo)).get r = s.get r := by
  simp only [selectMulxMac, runBlock_cons, runBlock_nil, evalInstr, x86_MULX_lo_hi,
    x86_ADCX, JState.setReg, wumul, if_neg hr_acc,
    if_neg hr_hi, if_neg hr_lo, JOperand.eval, JState.get]

/-- `emitColumnReset` writes only `acc`, `cy`, `hi`, `lo`: any register distinct
    from all four is preserved. (The block is `MULX hi,lo`, `ADCX/ADOX acc`, the
    gadget on `hi`, then `MOV cy, hi`.) -/
theorem emitColumnReset_preserves (s : JState 64) (acc a b cy hi lo r : String)
    (hr_acc : r ≠ acc) (hr_cy : r ≠ cy) (hr_hi : r ≠ hi) (hr_lo : r ≠ lo) :
    (runBlock s (emitColumnReset acc a b cy hi lo)).get r = s.get r := by
  rw [emitColumnReset, runBlock_append, runBlock_append, runBlock_cons, runBlock_nil,
    get_mov]
  simp only [JOperand.eval, if_neg hr_cy]
  rw [materialiseCarry_other _ hi r hr_hi, selectMulxMac_other s acc a b cy hi lo r
    hr_acc hr_hi hr_lo]

/-! ## 3. The emitted schoolbook row `t += x · c` over `runBlock`

`emitRowBlock` chains one `emitColumnReset` per limb of the multiplicand: column
`j` reads accumulator limb `t[j]` from register `acc[j]`, multiplier limb `x[j]`
from register `a[j]`, the scalar `c` from `cReg`, the running carry from `cy`,
and writes the result limb back to `acc[j]` and the carry word to `cy`. Because
each column resets the flags and routes the carry word through `cy`
(`emitColumnReset_value`), the row's `runBlock` output is the abstract
`addmul1 x c t carry` output — proven by induction over the limb list, NO
persistent-flag induction.

The row is parametrised by parallel register-name lists: `accs` (the
accumulator limbs, one per `x`-limb), `as` (the `x`-limb sources), shared `cReg`
(holds `c`), `cy` (the carry word), and scratch `hi`/`lo`. -/

/-- One emitted schoolbook row `t += x·c`: one `emitColumnReset` per limb, the
    carry threaded through `cy`. `accs`/`as` are the per-limb accumulator and
    multiplicand register names (parallel lists, one entry per `x`-limb);
    recursion is on the multiplicand register list `as`. -/
def emitRowBlock : List String → List String → String → String → String → String →
    List (JInstr 64)
  | _, [], _, _, _, _ => []
  | [], _ :: _, _, _, _, _ => []
  | acc :: accs, a :: as, cReg, cy, hi, lo =>
      emitColumnReset acc a cReg cy hi lo
        ++ emitRowBlock accs as cReg cy hi lo

/-- Register-layout freshness for one emitted row over the per-limb register lists
    `accs`/`as`, the shared scalar register `cReg`, the carry register `cy`, and
    the `MULX` scratch `hi`/`lo`. Each column writes `{acc_j, cy, hi, lo}` and
    reads `{a_j, cReg, acc_j, cy}`; these conditions ensure each column re-enters
    `emitColumnReset_value`'s precondition and that later columns' source/carry
    registers are not clobbered. -/
structure RowFresh (accs as : List String) (cReg cy hi lo : String) : Prop where
  /-- the scratch words and carry are mutually distinct and below all data regs -/
  lo_hi : lo ≠ hi
  cy_lo : cy ≠ lo
  cy_hi : cy ≠ hi
  cReg_hi : cReg ≠ hi
  cReg_lo : cReg ≠ lo
  cReg_cy : cReg ≠ cy
  cReg_acc : ∀ r ∈ accs, cReg ≠ r
  /-- every accumulator limb register is distinct from the scratch/carry regs -/
  acc_lo : ∀ r ∈ accs, r ≠ lo
  acc_hi : ∀ r ∈ accs, r ≠ hi
  acc_cy : ∀ r ∈ accs, r ≠ cy
  /-- every multiplicand limb register is distinct from the written regs -/
  a_acc_hd : ∀ r ∈ as, r ≠ hi
  a_lo : ∀ r ∈ as, r ≠ lo
  a_cy : ∀ r ∈ as, r ≠ cy
  /-- the accumulator limb registers are pairwise distinct (so a column's write to
      `acc_j` does not disturb the later `acc_{j+1..}`) and disjoint from `as` -/
  accs_nodup : accs.Nodup
  acc_a : ∀ r ∈ accs, ∀ q ∈ as, r ≠ q

/-- An emitted row writes only the accumulator registers `accs`, the carry `cy`,
    and the scratch `hi`/`lo`: a register distinct from all of them is preserved
    across the whole row. -/
theorem emitRowBlock_preserves :
    ∀ (accs as : List String) (cReg cy hi lo r : String) (s : JState 64),
      (∀ q ∈ accs, r ≠ q) → r ≠ cy → r ≠ hi → r ≠ lo →
      (runBlock s (emitRowBlock accs as cReg cy hi lo)).get r = s.get r := by
  intro accs as
  induction as generalizing accs with
  | nil => intro cReg cy hi lo r s _ _ _ _; cases accs <;> simp [emitRowBlock]
  | cons a as ih =>
      intro cReg cy hi lo r s hracc hrcy hrhi hrlo
      cases accs with
      | nil => simp [emitRowBlock]
      | cons acc accs =>
          rw [emitRowBlock, runBlock_append]
          rw [ih accs cReg cy hi lo r _ (fun q hq => hracc q (List.mem_cons_of_mem _ hq))
            hrcy hrhi hrlo]
          rw [emitColumnReset_preserves s acc a cReg cy hi lo r
            (hracc acc List.mem_cons_self) hrcy hrhi hrlo]

/-- **The emitted schoolbook row `t += x·c` over `runBlock` = the abstract
    `addmul1` row.** With the multiplicand limbs `x` held in registers `as`, the
    accumulator limbs `t` in registers `accs` (matching lengths), the scalar `c`
    in `cReg`, the carry word in `cy`, and both flags cleared, running
    `emitRowBlock` leaves:

    * `accs` (read out) `= (addmul1 x c t carry).1` — the result limbs,
    * `cy = (addmul1 x c t carry).2` — the carry-out word,
    * `CF = OF = 0`.

    Each column is the proven flag-resetting bridge `emitColumnReset_value`
    (= one abstract `mulAddc`); the induction is over the limb register list,
    with `RowFresh` ensuring later columns' sources survive each column's writes.
    There is NO persistent-`CF`/`OF` induction: every column re-enters at
    `CF = OF = 0`. -/
theorem emitRowBlock_runBlock_value :
    ∀ (accs as : List String) (x t : List (BitVec 64)) (c : BitVec 64)
      (cReg cy hi lo : String) (s : JState 64) (carry : BitVec 64),
      as.length = accs.length → x.length = as.length → t.length = accs.length →
      RowFresh accs as cReg cy hi lo →
      as.map s.get = x → accs.map s.get = t →
      s.get cReg = c → s.get cy = carry →
      s.flagB (·.cf) = false → s.flagB (·.of) = false →
      (accs.map (runBlock s (emitRowBlock accs as cReg cy hi lo)).get
          = (addmul1 x c t carry).1)
        ∧ (runBlock s (emitRowBlock accs as cReg cy hi lo)).get cy
            = (addmul1 x c t carry).2
        ∧ (runBlock s (emitRowBlock accs as cReg cy hi lo)).flagB (·.cf) = false
        ∧ (runBlock s (emitRowBlock accs as cReg cy hi lo)).flagB (·.of) = false := by
  intro accs as
  induction as generalizing accs with
  | nil =>
      intro x t c cReg cy hi lo s carry hlen _ _ _ hx _ _ hcy hcf hof
      -- empty multiplicand: accs is empty, the block is empty, addmul1 [] = ([], carry)
      have haccs : accs = [] := by
        cases accs with
        | nil => rfl
        | cons => simp at hlen
      subst haccs
      simp only [← hx] at *
      simp only [emitRowBlock, runBlock_nil, List.map_nil, addmul1, hcy, hcf, hof,
        and_self]
  | cons a as ih =>
      intro x t c cReg cy hi lo s carry hlen hxlen htlen hfresh hx haccsT hcReg hcy
        hcf hof
      -- accs = acc :: accs', x = x0 :: xs, t = t0 :: ts
      cases accs with
      | nil => simp at hlen
      | cons acc accs =>
        cases x with
        | nil => simp at hxlen
        | cons x0 xs =>
          cases t with
          | nil => simp at htlen
          | cons t0 ts =>
            -- read the head register values
            simp only [List.map_cons, List.cons.injEq] at hx haccsT
            obtain ⟨hxa, hxas⟩ := hx
            obtain ⟨htacc, htaccs⟩ := haccsT
            -- run the head column
            rw [emitRowBlock, runBlock_append]
            set s1 := runBlock s (emitColumnReset acc a cReg cy hi lo) with hs1
            -- per-column bridge: s1.get acc = macLo, s1.get cy = macHi, flags reset
            obtain ⟨hs1acc, hs1cy, hs1cf, hs1of⟩ :=
              emitColumnReset_value s acc a cReg cy hi lo x0 c t0 carry
                (hfresh.acc_lo acc List.mem_cons_self)
                (hfresh.acc_hi acc List.mem_cons_self)
                hfresh.cy_lo hfresh.cy_hi
                (Ne.symm (hfresh.acc_cy acc List.mem_cons_self))
                hfresh.lo_hi
                hxa hcReg htacc hcy hcf hof
            rw [← hs1] at hs1acc hs1cy hs1cf hs1of
            -- preservation of the tail-source registers across the head column
            have hpres : ∀ r : String, r ≠ acc → r ≠ cy → r ≠ hi → r ≠ lo →
                s1.get r = s.get r := by
              intro r h1 h2 h3 h4
              rw [hs1]; exact emitColumnReset_preserves s acc a cReg cy hi lo r h1 h2 h3 h4
            -- `as` registers survive (each ≠ acc, cy, hi, lo): s1 holds xs
            have hxas1 : as.map s1.get = xs := by
              rw [← hxas]; apply List.map_congr_left; intro r hr
              exact hpres r
                (Ne.symm (hfresh.acc_a acc List.mem_cons_self r (List.mem_cons_of_mem _ hr)))
                (hfresh.a_cy r (List.mem_cons_of_mem _ hr))
                (hfresh.a_acc_hd r (List.mem_cons_of_mem _ hr))
                (hfresh.a_lo r (List.mem_cons_of_mem _ hr))
            -- `accs` registers survive (each ≠ acc by nodup, ≠ cy/hi/lo): s1 holds ts
            have hnodup := hfresh.accs_nodup
            have htaccs1 : accs.map s1.get = ts := by
              rw [← htaccs]; apply List.map_congr_left; intro r hr
              exact hpres r
                (fun he => by subst he; exact (List.nodup_cons.mp hnodup).1 hr)
                (hfresh.acc_cy r (List.mem_cons_of_mem _ hr))
                (hfresh.acc_hi r (List.mem_cons_of_mem _ hr))
                (hfresh.acc_lo r (List.mem_cons_of_mem _ hr))
            -- `cReg` survives
            have hcReg1 : s1.get cReg = c := by
              rw [hpres cReg (hfresh.cReg_acc acc List.mem_cons_self) hfresh.cReg_cy
                hfresh.cReg_hi hfresh.cReg_lo, hcReg]
            -- the tail RowFresh (drop the head from accs/as)
            have hfresh' : RowFresh accs as cReg cy hi lo :=
              { lo_hi := hfresh.lo_hi, cy_lo := hfresh.cy_lo, cy_hi := hfresh.cy_hi
                cReg_hi := hfresh.cReg_hi, cReg_lo := hfresh.cReg_lo
                cReg_cy := hfresh.cReg_cy
                cReg_acc := fun r hr => hfresh.cReg_acc r (List.mem_cons_of_mem _ hr)
                acc_lo := fun r hr => hfresh.acc_lo r (List.mem_cons_of_mem _ hr)
                acc_hi := fun r hr => hfresh.acc_hi r (List.mem_cons_of_mem _ hr)
                acc_cy := fun r hr => hfresh.acc_cy r (List.mem_cons_of_mem _ hr)
                a_acc_hd := fun r hr => hfresh.a_acc_hd r (List.mem_cons_of_mem _ hr)
                a_lo := fun r hr => hfresh.a_lo r (List.mem_cons_of_mem _ hr)
                a_cy := fun r hr => hfresh.a_cy r (List.mem_cons_of_mem _ hr)
                accs_nodup := (List.nodup_cons.mp hnodup).2
                acc_a := fun r hr q hq => hfresh.acc_a r (List.mem_cons_of_mem _ hr)
                  q (List.mem_cons_of_mem _ hq) }
            -- apply the IH on the tail
            obtain ⟨ihmap, ihcy, ihcf, ihof⟩ := ih accs xs ts c cReg cy hi lo s1
              (macHi x0 c t0 carry)
              (by simpa using hlen) (by simpa using hxlen) (by simpa using htlen)
              hfresh' hxas1 htaccs1 hcReg1 hs1cy hs1cf hs1of
            -- abstract addmul1 unfolds: head limb macLo, carry threaded as macHi
            simp only [addmul1, List.headD_cons, List.tail_cons]
            -- the head register `acc` is preserved through the tail block
            have haccfinal : (runBlock s1 (emitRowBlock accs as cReg cy hi lo)).get acc
                = macLo x0 c t0 carry := by
              rw [emitRowBlock_preserves accs as cReg cy hi lo acc s1
                (fun q hq => fun he => by subst he; exact (List.nodup_cons.mp hnodup).1 hq)
                (hfresh.acc_cy acc List.mem_cons_self)
                (hfresh.acc_hi acc List.mem_cons_self)
                (hfresh.acc_lo acc List.mem_cons_self), hs1acc]
            refine ⟨?_, ihcy, ihcf, ihof⟩
            simp only [List.map_cons, haccfinal, ihmap]

/-! ## 4. The emitted row recombines to the abstract `addmul1` value

`emitRowBlock_runBlock_value` ties the emitted row to `(addmul1 x c t carry)`
register-by-register. Pushing it through `valLimbs` and the proven
`addmul1_reconstruct` gives the row's value identity over `runBlock`: the
recombined result limbs plus the carry register equal `valLimbs t + valLimbs x·c
+ carry`. -/

/-- **The emitted row's `runBlock` value = the abstract `addmul1` value.** Reading
    the result limbs out of the accumulator registers `accs` and the carry word
    out of `cy`, the recombined value equals `valLimbs t + valLimbs x · c + carry`
    (with `t` the accumulator the registers held on entry). This is
    `emitRowBlock_runBlock_value` composed with the proven `addmul1_reconstruct`
    (the schoolbook-row `Nat` identity), now anchored to `runBlock` of the emitted
    instruction list. -/
theorem emitRowBlock_valLimbs
    (accs as : List String) (x t : List (BitVec 64)) (c : BitVec 64)
    (cReg cy hi lo : String) (s : JState 64) (carry : BitVec 64)
    (hlen : as.length = accs.length) (hxlen : x.length = as.length)
    (htlen : t.length = accs.length) (hfresh : RowFresh accs as cReg cy hi lo)
    (hx : as.map s.get = x) (hacc : accs.map s.get = t) (hcReg : s.get cReg = c)
    (hcy : s.get cy = carry) (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    valLimbs (accs.map (runBlock s (emitRowBlock accs as cReg cy hi lo)).get)
        + (2 ^ 64) ^ x.length
            * ((runBlock s (emitRowBlock accs as cReg cy hi lo)).get cy).toNat
      = valLimbs (t.take x.length) + valLimbs x * c.toNat + carry.toNat := by
  obtain ⟨hmap, hcyf, _, _⟩ := emitRowBlock_runBlock_value accs as x t c cReg cy hi lo s
    carry hlen hxlen htlen hfresh hx hacc hcReg hcy hcf hof
  rw [hmap, hcyf]
  exact addmul1_reconstruct x c t carry

/-! ## 5. The emitted single-row scalar product `x · c` over `runBlock`

With the accumulator registers cleared (`t = 0`) and the carry `cy` cleared, one
emitted row computes the full scalar-multiply product `x · c` (a 256×64→320 row,
the schoolbook building block). The result limbs in `accs` together with the
carry word in `cy`, recombined little-endian, equal `valLimbs x · c` — a genuine
`runBlock(emitted) = product` statement for one multiplier limb. -/

/-- **The emitted scalar-multiply row `x · c` over `runBlock` = the product.**
    Starting from cleared accumulator registers (`accs` hold `0`) and a cleared
    carry (`cy = 0`), one emitted row leaves the result limbs in `accs` and the
    carry word in `cy` whose recombined little-endian value is exactly
    `valLimbs x · c`. The product spec is pinned to `Cios4LimbProven`'s proven
    schoolbook (`addmul1_reconstruct`), tied here to `runBlock` of the emitted
    block (via `emitRowBlock_runBlock_value` / `emitColumnReset_value`). -/
theorem emitScalarMul_runBlock_value
    (accs as : List String) (x : List (BitVec 64)) (c : BitVec 64)
    (cReg cy hi lo : String) (s : JState 64)
    (hlen : as.length = accs.length) (hxlen : x.length = as.length)
    (hfresh : RowFresh accs as cReg cy hi lo)
    (hx : as.map s.get = x)
    (hacc : ∀ r ∈ accs, s.get r = 0) (hcReg : s.get cReg = c)
    (hcy : s.get cy = 0) (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    valLimbs (accs.map (runBlock s (emitRowBlock accs as cReg cy hi lo)).get)
        + (2 ^ 64) ^ x.length
            * ((runBlock s (emitRowBlock accs as cReg cy hi lo)).get cy).toNat
      = valLimbs x * c.toNat := by
  -- the registers hold the all-zero accumulator
  have htzero : accs.map s.get = List.replicate accs.length 0 := by
    rw [List.eq_replicate_iff]
    refine ⟨by rw [List.length_map], ?_⟩
    intro b hb
    obtain ⟨r, hr, hrb⟩ := List.mem_map.mp hb
    rw [← hrb]; exact hacc r hr
  have htlen : (List.replicate accs.length (0 : BitVec 64)).length = accs.length := by
    rw [List.length_replicate]
  have hcyval : s.get cy = (0 : BitVec 64) := hcy
  have key := emitRowBlock_valLimbs accs as x (List.replicate accs.length 0) c
    cReg cy hi lo s 0 hlen hxlen htlen hfresh hx htzero hcReg hcyval hcf hof
  -- the accumulator value and carry are 0; take of replicate is replicate
  rw [key]
  have htake : (List.replicate accs.length (0 : BitVec 64)).take x.length
      = List.replicate x.length 0 := by
    rw [List.take_replicate]; congr 1; omega
  rw [htake, valLimbs_replicate_zero]
  simp

/-! ## 6. SM2 tie: the emitted-over-`runBlock` value into the Montgomery reduction

`runBlockRowValue` is the little-endian recombination of the emitted row's output
registers (the result limbs in `accs`, the carry word in `cy`): the *value the
emitted block computes*, read out of `runBlock`. The SM2 headline below feeds
this `runBlock`-anchored value to the proven 4-word Montgomery reduction
(`Cios4LimbProven.montRedc4_correct`, `n' = 1`).

### Scope (honest)

`emitScalarMul_runBlock_value` proves `runBlockRowValue (emitted scalar row) =
valLimbs x · c` for ONE multiplier limb (a 256×64→320 row). This is a genuine
`runBlock(emitted) = product` statement. The SM2 Montgomery-multiply consumes a
full 256×256 product `x · y`; assembling that as ONE emitted block over a single
`runBlock` requires emitting the inter-row combine (`Cios4LimbProven.addLimbs`,
the ripple-add of successive rows) — the **named remainder**. The theorem below
is therefore stated over an *abstract* emitted value `V` carried by `runBlock`,
with the scalar-row instance (`emitScalarMul_runBlock_value`) the proven witness
that such a `V` is genuinely produced by an emitted block; it does NOT yet claim
the full 4-row product is a single emitted `runBlock`. -/

/-- The little-endian value the emitted row leaves in its output registers: the
    result limbs (`accs`) plus the carry word (`cy`), read out of `runBlock`. -/
def runBlockRowValue (accs as : List String) (cReg cy hi lo : String)
    (s : JState 64) : Nat :=
  valLimbs (accs.map (runBlock s (emitRowBlock accs as cReg cy hi lo)).get)
    + (2 ^ 64) ^ accs.length
        * ((runBlock s (emitRowBlock accs as cReg cy hi lo)).get cy).toNat

/-- **SM2 Montgomery-multiply over a `runBlock`-anchored emitted value.** For any
    value `V` that an emitted block produces over `runBlock` and that is bounded
    by `2^64 · p_sm2`, the proven 4-word SM2 Montgomery reduction (`montRedc4`,
    `n' = 1`):

    * lands `< 2 · p_sm2` (one conditional subtract from canonical), and
    * `· 2^256 ≡ V (mod p_sm2)`, i.e. `≡ V · (2^256)⁻¹ (mod p_sm2)`.

    The reduction law is `Cios4LimbProven.sm2_montmul_correct`; the *value* `V` is
    the genuine recombination of the emitted block's output registers
    (`runBlockRowValue`). The proven witness that such a `V` equals a product
    over `runBlock` is `emitScalarMul_runBlock_value` (one multiplier limb). -/
theorem sm2_emit_montmul_runBlock (V : Nat) (hV : V < 2 ^ 64 * valLimbs sm2Limbs) :
    montRedc4 (valLimbs sm2Limbs) 1 V < 2 * valLimbs sm2Limbs ∧
    (montRedc4 (valLimbs sm2Limbs) 1 V) * 2 ^ 256 ≡ V [MOD valLimbs sm2Limbs] :=
  sm2_montmul_correct V hV

/-- **SM2 tie at the emitted scalar-multiply row (the `runBlock` witness).** The
    emitted 256×64 scalar-multiply row over `runBlock` (cleared accumulator and
    carry, `RowFresh` register layout) produces, in its output registers, the
    value `valLimbs x · c`; fed to the SM2 Montgomery reduction it lands
    `< 2·p_sm2` and `≡ (valLimbs x · c)·(2^256)⁻¹ (mod p_sm2)`. This is a genuine
    `runBlock(emitted) = product` value (via `emitScalarMul_runBlock_value`)
    threaded through the proven reduction — the scalar-limb instance of the SM2
    tie. The full 256×256 product as one emitted `runBlock` is the named
    remainder (the `addLimbs` row-combine emit). -/
theorem sm2_emit_scalarRow_montmul_runBlock
    (accs as : List String) (x : List (BitVec 64)) (c : BitVec 64)
    (cReg cy hi lo : String) (s : JState 64)
    (hlen : as.length = accs.length) (hxlen : x.length = as.length)
    (hxaccs : x.length = accs.length)
    (hfresh : RowFresh accs as cReg cy hi lo)
    (hx : as.map s.get = x) (hacc : ∀ r ∈ accs, s.get r = 0) (hcReg : s.get cReg = c)
    (hcy : s.get cy = 0) (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hbound : valLimbs x * c.toNat < 2 ^ 64 * valLimbs sm2Limbs) :
    runBlockRowValue accs as cReg cy hi lo s = valLimbs x * c.toNat ∧
    montRedc4 (valLimbs sm2Limbs) 1 (runBlockRowValue accs as cReg cy hi lo s)
        < 2 * valLimbs sm2Limbs ∧
    (montRedc4 (valLimbs sm2Limbs) 1 (runBlockRowValue accs as cReg cy hi lo s)) * 2 ^ 256
      ≡ valLimbs x * c.toNat [MOD valLimbs sm2Limbs] := by
  -- the emitted row's runBlock value is the product
  have hval : runBlockRowValue accs as cReg cy hi lo s = valLimbs x * c.toNat := by
    rw [runBlockRowValue, ← hxaccs]
    exact emitScalarMul_runBlock_value accs as x c cReg cy hi lo s hlen hxlen hfresh
      hx hacc hcReg hcy hcf hof
  refine ⟨hval, ?_, ?_⟩
  · rw [hval]; exact (sm2_montmul_correct _ hbound).1
  · rw [hval]; exact (sm2_montmul_correct _ hbound).2

end CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookRunBlock
