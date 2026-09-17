/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CarryMulCorres
public import CatCrypt.Crypto.SecureCompilation.Ascent.CarryMulSpec
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Zify

/-!
# Functional correctness of CryptOpt's `carry_mul`

`CarryMulBlock.carryMulBlock` is CryptOpt's `fiat_curve25519_carry_mul`.
`CarryMulCorres.lean` proves that its two memory-stable segments refine their abstract
runs. This module proves that those abstract runs compute fiat-crypto's `mul_correct`
congruence (`CarryMulSpec`) and transports the result to the machine.

The abstract runs are evaluated instruction by instruction, as in
`SolinasSquareCorrect.lean`: the abstract state is kept in the form
`mkS base V cf of m`, the thirteen registers the kernel writes in a record `V`, every
other register from the valuation `base`; one transport lemma per instruction form
names the words the instruction computes and records their arithmetic. The limb
arithmetic is closed over `Nat`.

## Main results

* `absRunMem_carryMulMid_spec`: from inputs below `2^54` whose limbs are apart from the
  frame slots, the abstract run of instructions 5–146 leaves the three carried limbs,
  the fourth limb, the low word of the fifth column and the multiple `19 q` of its
  carry in registers whose weighted sum is congruent to the product of the inputs.
* `absRunMem_carryMulTail_spec`: the abstract run of instructions 148–166 stores limbs
  whose value is that weighted sum.
* `carryMul_correct`: for every machine state whose input limbs are below `2^54`, whose
  tracked cells have separated addresses, and whose memory bank `%rax` agrees with
  `%rdx` on the second input, the five words `runBlock st carryMulBlock` writes at
  `[r10 + 8i]` meet `CarryMulSpec` against the input words at `[rsi + 8i]` and
  `[rdx + 8i]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.CarryMul

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.CarryMulBlock
open CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## A flat register valuation -/

/-- The values of the thirteen registers `carry_mul` writes after its first four
    instructions. -/
structure RegCM where
  /-- `%rbx`. -/
  rbx : BitVec 64
  /-- `%rcx`. -/
  rcx : BitVec 64
  /-- `%rdx`. -/
  rdx : BitVec 64
  /-- `%rbp`. -/
  rbp : BitVec 64
  /-- `%rdi`. -/
  rdi : BitVec 64
  /-- `%r8`. -/
  r8 : BitVec 64
  /-- `%r9`. -/
  r9 : BitVec 64
  /-- `%r10`. -/
  r10 : BitVec 64
  /-- `%r11`. -/
  r11 : BitVec 64
  /-- `%r12`. -/
  r12 : BitVec 64
  /-- `%r13`. -/
  r13 : BitVec 64
  /-- `%r14`. -/
  r14 : BitVec 64
  /-- `%r15`. -/
  r15 : BitVec 64

/-- The register valuation with the thirteen written registers from `v` and every
    other register from `base`. -/
def regsOf (v : RegCM) (base : String → BitVec 64) (r : String) : BitVec 64 :=
  if r = "%rbx" then v.rbx else if r = "%rcx" then v.rcx else if r = "%rdx" then v.rdx
  else if r = "%rbp" then v.rbp else if r = "%rdi" then v.rdi else if r = "%r8" then v.r8
  else if r = "%r9" then v.r9 else if r = "%r10" then v.r10 else if r = "%r11" then v.r11
  else if r = "%r12" then v.r12 else if r = "%r13" then v.r13 else if r = "%r14" then v.r14
  else if r = "%r15" then v.r15 else base r

/-- The abstract state with registers `regsOf v base`, carry flags `cf`, `of` and
    memory `m`. -/
def mkS (base : String → BitVec 64) (v : RegCM) (cf of : Bool) (m : BitVec 64 → BitVec 64) :
    AMemX :=
  ⟨⟨regsOf v base, cf, of⟩, m⟩

/-- A register read of `regsOf`. -/
class RegRead (d : String) where
  /-- The value read. -/
  get : RegCM → (String → BitVec 64) → BitVec 64
  /-- The read agrees with `regsOf`. -/
  get_eq : ∀ v base, regsOf v base d = get v base

/-- A register write of `regsOf`. -/
class RegWrite (d : String) where
  /-- The updated valuation. -/
  set : RegCM → BitVec 64 → RegCM
  /-- The update is a pointwise write at `d`. -/
  set_eq : ∀ v w base, regsOf (set v w) base = fun r => if r = d then w else regsOf v base r

instance instReadRax : RegRead "%rax" := ⟨fun _ base => base "%rax", fun _ _ => by simp [regsOf]⟩
instance instReadRsi : RegRead "%rsi" := ⟨fun _ base => base "%rsi", fun _ _ => by simp [regsOf]⟩
instance instReadRsp : RegRead "%rsp" := ⟨fun _ base => base "%rsp", fun _ _ => by simp [regsOf]⟩
instance instReadRbx : RegRead "%rbx" := ⟨fun v _ => v.rbx, fun _ _ => by simp [regsOf]⟩
instance instReadRcx : RegRead "%rcx" := ⟨fun v _ => v.rcx, fun _ _ => by simp [regsOf]⟩
instance instReadRdx : RegRead "%rdx" := ⟨fun v _ => v.rdx, fun _ _ => by simp [regsOf]⟩
instance instReadRbp : RegRead "%rbp" := ⟨fun v _ => v.rbp, fun _ _ => by simp [regsOf]⟩
instance instReadRdi : RegRead "%rdi" := ⟨fun v _ => v.rdi, fun _ _ => by simp [regsOf]⟩
instance instReadR8 : RegRead "%r8" := ⟨fun v _ => v.r8, fun _ _ => by simp [regsOf]⟩
instance instReadR9 : RegRead "%r9" := ⟨fun v _ => v.r9, fun _ _ => by simp [regsOf]⟩
instance instReadR10 : RegRead "%r10" := ⟨fun v _ => v.r10, fun _ _ => by simp [regsOf]⟩
instance instReadR11 : RegRead "%r11" := ⟨fun v _ => v.r11, fun _ _ => by simp [regsOf]⟩
instance instReadR12 : RegRead "%r12" := ⟨fun v _ => v.r12, fun _ _ => by simp [regsOf]⟩
instance instReadR13 : RegRead "%r13" := ⟨fun v _ => v.r13, fun _ _ => by simp [regsOf]⟩
instance instReadR14 : RegRead "%r14" := ⟨fun v _ => v.r14, fun _ _ => by simp [regsOf]⟩
instance instReadR15 : RegRead "%r15" := ⟨fun v _ => v.r15, fun _ _ => by simp [regsOf]⟩

/-- The write instances share one proof: split on the written register. -/
macro "regwrite_cm_tac" d:str : tactic =>
  `(tactic| (funext r; by_cases h : r = $d
             · subst h; simp [regsOf]
             · simp only [regsOf, h, if_false]))

instance instWriteRbx : RegWrite "%rbx" := ⟨fun v w => { v with rbx := w },
  fun _ _ _ => by regwrite_cm_tac "%rbx"⟩
instance instWriteRcx : RegWrite "%rcx" := ⟨fun v w => { v with rcx := w },
  fun _ _ _ => by regwrite_cm_tac "%rcx"⟩
instance instWriteRdx : RegWrite "%rdx" := ⟨fun v w => { v with rdx := w },
  fun _ _ _ => by regwrite_cm_tac "%rdx"⟩
instance instWriteRbp : RegWrite "%rbp" := ⟨fun v w => { v with rbp := w },
  fun _ _ _ => by regwrite_cm_tac "%rbp"⟩
instance instWriteRdi : RegWrite "%rdi" := ⟨fun v w => { v with rdi := w },
  fun _ _ _ => by regwrite_cm_tac "%rdi"⟩
instance instWriteR8 : RegWrite "%r8" := ⟨fun v w => { v with r8 := w },
  fun _ _ _ => by regwrite_cm_tac "%r8"⟩
instance instWriteR9 : RegWrite "%r9" := ⟨fun v w => { v with r9 := w },
  fun _ _ _ => by regwrite_cm_tac "%r9"⟩
instance instWriteR10 : RegWrite "%r10" := ⟨fun v w => { v with r10 := w },
  fun _ _ _ => by regwrite_cm_tac "%r10"⟩
instance instWriteR11 : RegWrite "%r11" := ⟨fun v w => { v with r11 := w },
  fun _ _ _ => by regwrite_cm_tac "%r11"⟩
instance instWriteR12 : RegWrite "%r12" := ⟨fun v w => { v with r12 := w },
  fun _ _ _ => by regwrite_cm_tac "%r12"⟩
instance instWriteR13 : RegWrite "%r13" := ⟨fun v w => { v with r13 := w },
  fun _ _ _ => by regwrite_cm_tac "%r13"⟩
instance instWriteR14 : RegWrite "%r14" := ⟨fun v w => { v with r14 := w },
  fun _ _ _ => by regwrite_cm_tac "%r14"⟩
instance instWriteR15 : RegWrite "%r15" := ⟨fun v w => { v with r15 := w },
  fun _ _ _ => by regwrite_cm_tac "%r15"⟩

/-! ## Word facts -/

/-- The carry-out form of `add_carry` with a carry-in at most one. -/
theorem add_carry_fact (x y : BitVec 64) (c : Nat) (hc : c ≤ 1) :
    (add_carry x y c).toNat + 2 ^ 64 * (if decide (2 ^ 64 ≤ x.toNat + y.toNat + c) then 1 else 0)
      = x.toNat + y.toNat + c := by
  rw [add_carry, BitVec.toNat_ofNat]
  have := x.isLt
  have := y.isLt
  split
  · simp_all; omega
  · simp_all

/-- The carry-out form of a two-word sum. -/
theorem add_fact (x y : BitVec 64) :
    (x + y).toNat + 2 ^ 64 * (if decide (2 ^ 64 ≤ x.toNat + y.toNat) then 1 else 0)
      = x.toNat + y.toNat := by
  rw [BitVec.toNat_add]
  have := x.isLt
  have := y.isLt
  split
  · simp_all; omega
  · simp_all

/-- The high and low words of a 128-bit product recompose it. -/
theorem mulx_fact (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 (x * y / 2 ^ 64)).toNat * 2 ^ 64 + (BitVec.ofNat 64 (x * y)).toNat
      = x * y := by
  have hxy : x * y < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
  have hq : x * y / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hxy
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  have := Nat.div_add_mod (x * y) (2 ^ 64)
  rw [Nat.mul_comm] at this
  exact this

/-- A carry flag read as a number is at most one. -/
theorem bit_le (b : Bool) : (if b then 1 else 0 : Nat) ≤ 1 := by
  cases b <;> simp

/-- The word of `shrd x, y, 51` is the low 64 bits of the 128-bit value `y:x` shifted
    right by 51. -/
theorem shrd51_toNat (x y : BitVec 64) :
    (x86_SHRD x y (BitVec.ofNat 64 51)).word.toNat = (y.toNat * 2 ^ 64 + x.toNat) / 2 ^ 51 % 2 ^ 64 := by
  have e : (x86_SHRD x y (BitVec.ofNat 64 51)).word = x >>> 51 ||| y <<< 13 := by
    simp [x86_SHRD, shiftCount, wshr, wshl, rflags_OF]
  have hand : x >>> 51 &&& y <<< 13 = 0#64 := by
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft,
      BitVec.getElem_zero]
    by_cases h13 : i < 13
    · simp [h13]
    · have : ¬ (51 + i < 64) := by omega
      simp [BitVec.getLsbD_of_ge x (51 + i) (by omega)]
  have h : x >>> 51 ||| y <<< 13 = x >>> 51 + y <<< 13 :=
    (BitVec.add_eq_or_of_and_eq_zero _ _ hand).symm
  rw [e, h, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have := x.isLt
  have := y.isLt
  omega

/-- The word of `bzhi x, 51` is `x` modulo `2^51`. -/
theorem bzhi51_toNat (x : BitVec 64) :
    (x86_BZHI x (BitVec.ofNat 64 51)).word.toNat = x.toNat % 2 ^ 51 := by
  simp only [x86_BZHI, BitVec.toNat_ofNat]
  rw [if_pos (by norm_num), BitVec.toNat_and, BitVec.toNat_ofNat,
    show (51 : Nat) % 2 ^ 64 % 256 = 51 by norm_num,
    Nat.mod_eq_of_lt (show 2 ^ 51 - 1 < 2 ^ 64 by norm_num), Nat.and_two_pow_sub_one_eq_mod]

/-- The word of `shr x, 51` is `x` divided by `2^51`. -/
theorem shr51_toNat (x : BitVec 64) :
    (x86_SHR x (BitVec.ofNat 64 51)).word.toNat = x.toNat / 2 ^ 51 := by
  simp [x86_SHR, shiftCount, wshr, rflags_OF, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-! ## One transport lemma per instruction form

Each lemma rewrites `Q (absRunMem (i :: rest) (mkS base V cf of m))` to a goal about
`rest`, naming the words the instruction computes and recording their arithmetic. A
memory operand `[b + o]` is read at `RegRead.get b V base + o`. -/

section Transport

variable {Q : AMemX → Prop} {rest : List (JInstr 64)} {base : String → BitVec 64}
  {V : RegCM} {cf of : Bool} {m : BitVec 64 → BitVec 64}

/-- One step of the abstract run, from the step's result. -/
theorem run_step {i : JInstr 64} {s t : AMemX} (hst : absStepMem i s = t)
    (h : Q (absRunMem rest t)) : Q (absRunMem (i :: rest) s) := by
  subst hst; exact h

/-- `loadMem d b o`: `d` receives the memory word at `[b + o]`. -/
theorem run_loadMem (d b : String) (o : Int) [RegWrite d] [RegRead b] (x : BitVec 64)
    (hm : m (RegRead.get b V base + BitVec.ofInt 64 o) = x)
    (h : Q (absRunMem rest (mkS base (RegWrite.set d V x) cf of m))) :
    Q (absRunMem (.loadMem d b o :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ h
  simp only [mkS, absStepMem, loadStepM, RegWrite.set_eq, cellAddr, RegRead.get_eq, hm]

/-- `mov d, k`: `d` receives the word `k`. -/
theorem run_mov_imm (d : String) (k : Nat) [RegWrite d]
    (h : Q (absRunMem rest (mkS base (RegWrite.set d V (BitVec.ofNat 64 k)) cf of m))) :
    Q (absRunMem (.mov d (.imm k) :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, movStep2, RegWrite.set_eq, evalX]) h

/-- `mov d, src`: `d` receives the word in `src`. -/
theorem run_mov_reg (d src : String) [RegWrite d] [RegRead src]
    (h : Q (absRunMem rest (mkS base (RegWrite.set d V (RegRead.get src V base)) cf of m))) :
    Q (absRunMem (.mov d (.reg src) :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, movStep2, RegWrite.set_eq, evalX, RegRead.get_eq]) h

/-- `storeMem b o src`: the new memory holds `src` at `[b + o]` and agrees with the old
    one elsewhere. -/
theorem run_storeMem (b : String) (o : Int) (src : String) [RegRead b] [RegRead src]
    (h : ∀ m' : BitVec 64 → BitVec 64,
      m' (RegRead.get b V base + BitVec.ofInt 64 o) = RegRead.get src V base →
      (∀ p, p ≠ RegRead.get b V base + BitVec.ofInt 64 o → m' p = m p) →
      Q (absRunMem rest (mkS base V cf of m'))) :
    Q (absRunMem (.storeMem b o (.reg src) :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h (fun p => if p = RegRead.get b V base + BitVec.ofInt 64 o then
    RegRead.get src V base else m p) (if_pos rfl) (fun p hp => if_neg hp))
  simp only [mkS, absStepMem, storeStepM, cellAddr, RegRead.get_eq, evalX]

/-- `mulx dHi, dLo, [b + o]` with `%rdx` as the implicit operand: `dHi` and `dLo` receive
    the high and low words of the 128-bit product. -/
theorem run_mulxMem (dHi dLo b : String) (o : Int) [RegWrite dHi] [RegWrite dLo] [RegRead b]
    (x : BitVec 64) (hm : m (RegRead.get b V base + BitVec.ofInt 64 o) = x)
    (h : ∀ hi lo : BitVec 64,
      hi.toNat * 2 ^ 64 + lo.toNat = (RegRead.get "%rdx" V base).toNat * x.toNat →
      Q (absRunMem rest (mkS base (RegWrite.set dHi (RegWrite.set dLo V lo) hi) cf of m))) :
    Q (absRunMem (.mulxMem dHi dLo (.reg "%rdx") b o :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h _ _ (mulx_fact _ _ (RegRead.get "%rdx" V base).isLt x.isLt))
  simp only [mkS, absStepMem, mulxMemStepM, RegWrite.set_eq, cellAddr, evalX,
    RegRead.get_eq, hm]

/-- Register-operand `mulx`: `dHi` and `dLo` receive the high and low words of the
    product. -/
theorem run_mulx (dHi dLo ra rb : String) [RegWrite dHi] [RegWrite dLo] [RegRead ra]
    [RegRead rb]
    (h : ∀ hi lo : BitVec 64, hi.toNat * 2 ^ 64 + lo.toNat =
      (RegRead.get ra V base).toNat * (RegRead.get rb V base).toNat →
      Q (absRunMem rest (mkS base (RegWrite.set dHi (RegWrite.set dLo V lo) hi) cf of m))) :
    Q (absRunMem (.mulx dHi dLo (.reg ra) (.reg rb) :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h _ _ (mulx_fact _ _ (RegRead.get ra V base).isLt
    (RegRead.get rb V base).isLt))
  simp only [mkS, absStepMem, mulxStep2, RegWrite.set_eq, RegRead.get_eq]

/-- `add d, src`: `d` and `CF` receive the sum word and carry-out of `d + src`; the new
    `OF` is a name `o'` with no recorded value. -/
theorem run_add (d src : String) [RegWrite d] [RegRead d] [RegRead src]
    (h : ∀ (w : BitVec 64) (c o' : Bool),
      w.toNat + 2 ^ 64 * (if c then 1 else 0) =
        (RegRead.get d V base).toNat + (RegRead.get src V base).toNat →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) c o' m))) :
    Q (absRunMem (.add d (.reg src) :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, addStep2, RegWrite.set_eq, RegRead.get_eq, evalX]; rfl)
    (h _ _ _ (add_fact _ _))

/-- `add d, [b + o]`: as `run_add` with the memory word as source. -/
theorem run_addMem (d b : String) (o : Int) [RegWrite d] [RegRead d] [RegRead b]
    (x : BitVec 64) (hm : m (RegRead.get b V base + BitVec.ofInt 64 o) = x)
    (h : ∀ (w : BitVec 64) (c o' : Bool),
      w.toNat + 2 ^ 64 * (if c then 1 else 0) = (RegRead.get d V base).toNat + x.toNat →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) c o' m))) :
    Q (absRunMem (.addMem d b o :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, addMemStepM, addStep2, RegWrite.set_eq,
    RegRead.get_eq, evalX, cellAddr, hm, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl)
    (h _ _ _ (add_fact _ _))

/-- `adcx d, src`: `d` and `CF` receive the sum word and carry-out of `d + src + CF`. -/
theorem run_adcx (d src : String) [RegWrite d] [RegRead d] [RegRead src]
    (h : ∀ (w : BitVec 64) (c : Bool),
      w.toNat + 2 ^ 64 * (if c then 1 else 0) =
        (RegRead.get d V base).toNat + (RegRead.get src V base).toNat + (if cf then 1 else 0) →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) c of m))) :
    Q (absRunMem (.adcx d (.reg src) :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h _ _ (add_carry_fact _ _ _ (bit_le cf)))
  simp only [mkS, absStepMem, adcxStep2, RegWrite.set_eq, RegRead.get_eq]
  rfl

/-- `adox d, src`: `d` and `OF` receive the sum word and carry-out of `d + src + OF`. -/
theorem run_adox (d src : String) [RegWrite d] [RegRead d] [RegRead src]
    (h : ∀ (w : BitVec 64) (c : Bool),
      w.toNat + 2 ^ 64 * (if c then 1 else 0) =
        (RegRead.get d V base).toNat + (RegRead.get src V base).toNat + (if of then 1 else 0) →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) cf c m))) :
    Q (absRunMem (.adox d (.reg src) :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h _ _ (add_carry_fact _ _ _ (bit_le of)))
  simp only [mkS, absStepMem, adoxStep2, RegWrite.set_eq, RegRead.get_eq]
  rfl

/-- `adcx d, [b + o]`: as `run_adcx` with the memory word as source. -/
theorem run_adcxMem (d b : String) (o : Int) [RegWrite d] [RegRead d] [RegRead b]
    (x : BitVec 64) (hm : m (RegRead.get b V base + BitVec.ofInt 64 o) = x)
    (h : ∀ (w : BitVec 64) (c : Bool),
      w.toNat + 2 ^ 64 * (if c then 1 else 0) =
        (RegRead.get d V base).toNat + x.toNat + (if cf then 1 else 0) →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) c of m))) :
    Q (absRunMem (.adcxMem d b o :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h _ _ (add_carry_fact _ _ _ (bit_le cf)))
  simp only [mkS, absStepMem, adcxMemStepM, adcxImmStep2, RegWrite.set_eq, RegRead.get_eq,
    cellAddr, hm, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-- `adox d, [b + o]`: as `run_adox` with the memory word as source. -/
theorem run_adoxMem (d b : String) (o : Int) [RegWrite d] [RegRead d] [RegRead b]
    (x : BitVec 64) (hm : m (RegRead.get b V base + BitVec.ofInt 64 o) = x)
    (h : ∀ (w : BitVec 64) (c : Bool),
      w.toNat + 2 ^ 64 * (if c then 1 else 0) =
        (RegRead.get d V base).toNat + x.toNat + (if of then 1 else 0) →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) cf c m))) :
    Q (absRunMem (.adoxMem d b o :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h _ _ (add_carry_fact _ _ _ (bit_le of)))
  simp only [mkS, absStepMem, adoxMemStepM, adoxImmStep2, RegWrite.set_eq, RegRead.get_eq,
    cellAddr, hm, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-- `adc d, k`: `d` and `CF` receive the sum word and carry-out of `d + k + CF`; the new
    `OF` is a name `o'` with no recorded value. -/
theorem run_adc_imm (d : String) (k : Nat) [RegWrite d] [RegRead d]
    (h : ∀ (w : BitVec 64) (c o' : Bool),
      w.toNat + 2 ^ 64 * (if c then 1 else 0) =
        (RegRead.get d V base).toNat + (BitVec.ofNat 64 k).toNat + (if cf then 1 else 0) →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) c o' m))) :
    Q (absRunMem (.adc d (.imm k) :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, adcStep2, RegWrite.set_eq, RegRead.get_eq, evalX]; rfl)
    (h _ _ _ (add_carry_fact _ _ _ (bit_le cf)))

/-- `test` at any operand size: both carry flags are cleared. -/
theorem run_testN (sz : Nat) (x : String) (o : JOperand)
    (h : Q (absRunMem rest (mkS base V false false m))) :
    Q (absRunMem (.testN sz x o :: rest) (mkS base V cf of m)) :=
  run_step rfl h

/-- `xor d, d`: `d` becomes `0` and both carry flags are cleared. -/
theorem run_xor_self (d : String) [RegWrite d] [RegRead d]
    (h : Q (absRunMem rest (mkS base (RegWrite.set d V 0) false false m))) :
    Q (absRunMem (.xor_ d (.reg d) :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, xorStep2, RegWrite.set_eq, evalX, BitVec.xor_self]; rfl) h

/-- `imul d, [b + o], 19`: `d` receives the low word of `19` times the memory word; the
    two carry flags receive one name `c`. -/
theorem run_imulriMem19 (d b : String) (o : Int) [RegWrite d] [RegRead b] (x : BitVec 64)
    (hm : m (RegRead.get b V base + BitVec.ofInt 64 o) = x)
    (h : ∀ (w : BitVec 64) (c : Bool), w.toNat = x.toNat * 19 % 2 ^ 64 →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) c c m))) :
    Q (absRunMem (.imulriMem d b o 19 :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h (x * BitVec.ofNat 64 19) (imulOverflow x (BitVec.ofNat 64 19))
    (by rw [BitVec.toNat_mul]; rfl))
  simp only [mkS, absStepMem, imulriMemStepM, imulStep2, movStep2, RegWrite.set_eq,
    RegRead.get_eq, cellAddr, hm, evalX, BitVec.ofNat_toNat, BitVec.setWidth_eq, if_pos]
  congr 2
  funext r
  split <;> simp_all

/-- `imul d, s, 19`: `d` receives the low word of `19` times `s`; the new carry flags are
    names with no recorded value. -/
theorem run_imulri19 (d s : String) [RegWrite d] [RegRead s]
    (h : ∀ (w : BitVec 64) (c o' : Bool), w.toNat = (RegRead.get s V base).toNat * 19 % 2 ^ 64 →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) c o' m))) :
    Q (absRunMem (.imulri d s 19 :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, imulriStep2, writeStep2, RegWrite.set_eq,
    RegRead.get_eq]; rfl) (h _ _ _ (by simp only [x86_IMULt, rflags_of_mul]; rw [BitVec.toNat_mul]; rfl))

/-- `shrd d, s, 51`: `d` receives the low word of `s:d` shifted right by `51`; the new
    carry flags are names with no recorded value. -/
theorem run_shrd51 (d s : String) [RegWrite d] [RegRead d] [RegRead s]
    (h : ∀ (w : BitVec 64) (c o' : Bool),
      w.toNat = ((RegRead.get s V base).toNat * 2 ^ 64 + (RegRead.get d V base).toNat) /
        2 ^ 51 % 2 ^ 64 →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) c o' m))) :
    Q (absRunMem (.shrd d s (.imm 51) :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, shrdStep2, writeStep2, RegWrite.set_eq,
    RegRead.get_eq, evalX]; rfl) (h _ _ _ (shrd51_toNat _ _))

/-- `bzhi d, s, i` with `i = 51`: `d` receives `s` modulo `2^51`; both carry flags are
    cleared. -/
theorem run_bzhi51 (d s i : String) [RegWrite d] [RegRead s] [RegRead i]
    (hi : RegRead.get i V base = BitVec.ofNat 64 51)
    (h : ∀ w : BitVec 64, w.toNat = (RegRead.get s V base).toNat % 2 ^ 51 →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) false false m))) :
    Q (absRunMem (.bzhi d s i :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h _ (bzhi51_toNat _))
  simp only [mkS, absStepMem, bzhiStep2, writeStep2, RegWrite.set_eq, RegRead.get_eq, hi]
  simp [x86_BZHI]

/-- `shr d, 51`: `d` receives `d` divided by `2^51`; the new carry flags are names with no
    recorded value. -/
theorem run_shr51 (d : String) [RegWrite d] [RegRead d]
    (h : ∀ (w : BitVec 64) (c o' : Bool), w.toNat = (RegRead.get d V base).toNat / 2 ^ 51 →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) c o' m))) :
    Q (absRunMem (.shr d (.imm 51) :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, shrStep2, writeStep2, RegWrite.set_eq,
    RegRead.get_eq, evalX]; rfl) (h _ _ _ (shr51_toNat _))

/-- `lea d, [b + i]`: `d` receives `b + i` modulo `2^64`. -/
theorem run_lea (d b i : String) [RegWrite d] [RegRead b] [RegRead i]
    (h : ∀ w : BitVec 64,
      w.toNat = ((RegRead.get b V base).toNat + (RegRead.get i V base).toNat) % 2 ^ 64 →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) cf of m))) :
    Q (absRunMem (.lea d b i 1 0 :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h (RegRead.get b V base + RegRead.get i V base) (BitVec.toNat_add _ _))
  have h0 : BitVec.ofInt 64 0 = 0#64 := rfl
  simp only [mkS, absStepMem, leaStep2, RegWrite.set_eq, RegRead.get_eq, BitVec.mul_one, h0,
    BitVec.add_zero]

end Transport

/-! ## The layouts and the interface between the segments -/

/-- The radix-`2^51` value of five words. -/
abbrev val5 (x0 x1 x2 x3 x4 : BitVec 64) : Nat :=
  x0.toNat + 2 ^ 51 * x1.toNat + 2 ^ 102 * x2.toNat + 2 ^ 153 * x3.toNat + 2 ^ 204 * x4.toNat

/-- The memory `m` holds the input limbs `a0 … a4` at `[rsi + 8i]` and `b0 … b4` at
    `[rax + 8i]`, the base registers read from `base`. -/
structure MidIn (m : BitVec 64 → BitVec 64) (base : String → BitVec 64)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64) : Prop where
  ha0 : m (base "%rsi" + BitVec.ofInt 64 0) = a0
  ha1 : m (base "%rsi" + BitVec.ofInt 64 8) = a1
  ha2 : m (base "%rsi" + BitVec.ofInt 64 16) = a2
  ha3 : m (base "%rsi" + BitVec.ofInt 64 24) = a3
  ha4 : m (base "%rsi" + BitVec.ofInt 64 32) = a4
  hb0 : m (base "%rax" + BitVec.ofInt 64 0) = b0
  hb1 : m (base "%rax" + BitVec.ofInt 64 8) = b1
  hb2 : m (base "%rax" + BitVec.ofInt 64 16) = b2
  hb3 : m (base "%rax" + BitVec.ofInt 64 24) = b3
  hb4 : m (base "%rax" + BitVec.ofInt 64 32) = b4

/-- A store to a frame slot of `carryMulMidCells` keeps the input limbs, when the cells
    are separated under `base`. -/
theorem midIn_store {m m' : BitVec 64 → BitVec 64} {base : String → BitVec 64}
    (hsep : CellsSeparated carryMulMidCells base) (o : Int)
    (ho : ("%rsp", o) ∈ carryMulMidCells)
    (f : ∀ p, p ≠ base "%rsp" + BitVec.ofInt 64 o → m' p = m p)
    {a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64}
    (h : MidIn m base a0 a1 a2 a3 a4 b0 b1 b2 b3 b4) :
    MidIn m' base a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 := by
  have ne : ∀ c ∈ carryMulMidCells, c.1 ≠ "%rsp" →
      cellAddr base c ≠ base "%rsp" + BitVec.ofInt 64 o := by
    intro c hc h1 he
    exact h1 (congrArg Prod.fst (hsep c hc _ ho he))
  obtain ⟨h0, h1, h2, h3, h4, g0, g1, g2, g3, g4⟩ := h
  exact ⟨(f _ (ne ("%rsi", 0) (by decide) (by decide))).trans h0,
    (f _ (ne ("%rsi", 8) (by decide) (by decide))).trans h1,
    (f _ (ne ("%rsi", 16) (by decide) (by decide))).trans h2,
    (f _ (ne ("%rsi", 24) (by decide) (by decide))).trans h3,
    (f _ (ne ("%rsi", 32) (by decide) (by decide))).trans h4,
    (f _ (ne ("%rax", 0) (by decide) (by decide))).trans g0,
    (f _ (ne ("%rax", 8) (by decide) (by decide))).trans g1,
    (f _ (ne ("%rax", 16) (by decide) (by decide))).trans g2,
    (f _ (ne ("%rax", 24) (by decide) (by decide))).trans g3,
    (f _ (ne ("%rax", 32) (by decide) (by decide))).trans g4⟩

/-- Two frame slots at distinct displacements have distinct addresses. -/
theorem slot_ne (x : BitVec 64) {o o' : Int} (h : BitVec.ofInt 64 o ≠ BitVec.ofInt 64 o') :
    x + BitVec.ofInt 64 o ≠ x + BitVec.ofInt 64 o' := fun he =>
  h (by simpa using he)

/-- The facts instructions 148–166 need from instructions 5–146, stated on the abstract
    state `s` after instruction 146: `%rdi` holds `51`, `%rsp` is unchanged, the three
    carried limbs in `%r13`, `%r11`, `%r12` are below `2^51`, the word `19 q` in `%rbx`
    leaves room for a limb, the frame slot `[rsp - 0x50]` holds the output pointer
    `outp`, and the weighted sum of the limb registers with `19 q` is congruent to the
    product of the inputs modulo `2^255 - 19`. -/
def MidOut (base : String → BitVec 64) (outp a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64)
    (s : AMemX) : Prop :=
  s.c.regs "%rdi" = 51#64 ∧ s.c.regs "%rsp" = base "%rsp" ∧
  (s.c.regs "%r13").toNat < 2 ^ 51 ∧ (s.c.regs "%r11").toNat < 2 ^ 51 ∧
  (s.c.regs "%r12").toNat < 2 ^ 51 ∧ (s.c.regs "%rbx").toNat + 2 ^ 51 ≤ 2 ^ 64 ∧
  s.mem (base "%rsp" + BitVec.ofInt 64 (-80)) = outp ∧
  ((s.c.regs "%r13").toNat + 2 ^ 51 * (s.c.regs "%r11").toNat +
      2 ^ 102 * (s.c.regs "%r12").toNat + 2 ^ 153 * (s.c.regs "%r14").toNat +
      2 ^ 204 * ((s.c.regs "%rbp").toNat % 2 ^ 51) + (s.c.regs "%rbx").toNat) % carryMulP
    = (val5 a0 a1 a2 a3 a4 * val5 b0 b1 b2 b3 b4) % carryMulP

/-- The output condition of instructions 148–166 on the abstract state `s`: `%r10` is
    unchanged, and the five words at `[r10 + 8i]` have as value the weighted sum of the
    limb registers of `V` with `%rbx`. -/
def TailOut (V : RegCM) (s : AMemX) : Prop :=
  s.c.regs "%r10" = V.r10 ∧
  val5 (s.mem (V.r10 + BitVec.ofInt 64 0)) (s.mem (V.r10 + BitVec.ofInt 64 8))
      (s.mem (V.r10 + BitVec.ofInt 64 16)) (s.mem (V.r10 + BitVec.ofInt 64 24))
      (s.mem (V.r10 + BitVec.ofInt 64 32))
    = V.r13.toNat + 2 ^ 51 * V.r11.toNat + 2 ^ 102 * V.r12.toNat + 2 ^ 153 * V.r14.toNat +
      2 ^ 204 * (V.rbp.toNat % 2 ^ 51) + V.rbx.toNat

/-! ## The limb arithmetic of the kernel

Instructions 5–146 sum the twenty-five partial products `a_i b_j`, those with
`i + j ≥ 5` multiplied by `19 = 2^255 mod (2^255 - 19)`, into five 128-bit columns along
`adcx`/`adox`/`add` chains, and carry each column into the next by `shrd`/`bzhi` at
bit `51`. `col0` … `col4` state each column over `Nat`, with the partial products as
atoms; `mul_mod_p` is the field congruence of the carried limbs. -/

section Arithmetic

set_option exponentiation.threshold 600

/-- Two 128-bit words added along a carry chain whose top carry-out is dropped: the
    result is the sum when the sum is below `2^128`. -/
theorem acc128 {x0 y0 x1 y1 s0 s1 c c' : Nat} (e0 : s0 + 2 ^ 64 * c = x0 + y0)
    (e1 : s1 + 2 ^ 64 * c' = x1 + y1 + c) (hb : x1 * 2 ^ 64 + y1 * 2 ^ 64 + x0 + y0 < 2 ^ 128) :
    s1 * 2 ^ 64 + s0 = x1 * 2 ^ 64 + y1 * 2 ^ 64 + x0 + y0 := by
  omega

/-- `acc128` with the sum named: the two-word result is `T` when the four summands add up
    to `T < 2^128`. -/
theorem acc128S {x0 y0 x1 y1 s0 s1 c c' T : Nat} (e0 : s0 + 2 ^ 64 * c = x0 + y0)
    (e1 : s1 + 2 ^ 64 * c' = x1 + y1 + c) (hT : x1 * 2 ^ 64 + y1 * 2 ^ 64 + x0 + y0 = T)
    (hb : T < 2 ^ 128) :
    s1 * 2 ^ 64 + s0 = T := by
  subst hT
  exact acc128 e0 e1 hb

/-- The carry of a 128-bit column below `2^115` at bit `51`: the `bzhi` limb and the
    `shrd` carry recompose the column. -/
theorem carry51 {hi lo S q c : Nat} (hS : hi * 2 ^ 64 + lo = S)
    (hq : q = (hi * 2 ^ 64 + lo) / 2 ^ 51 % 2 ^ 64) (hc : c = lo % 2 ^ 51) (hb : S < 2 ^ 115) :
    c + 2 ^ 51 * q = S := by
  omega

/-- A product of two numbers below `2^54` is below `2^108`. -/
theorem lt108 {x y : Nat} (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) : x * y < 2 ^ 108 :=
  lt_of_lt_of_eq (Nat.mul_lt_mul'' hx hy) (by norm_num)

/-- A product with a factor `19` of two numbers below `2^54` is below `19 * 2^108`. -/
theorem lt19l {x y : Nat} (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) : x * 19 * y < 19 * 2 ^ 108 := by
  have := lt108 hx hy
  calc x * 19 * y = 19 * (x * y) := by ring
    _ < 19 * 2 ^ 108 := by omega

/-- `lt19l` with the factors swapped. -/
theorem lt19r {x y : Nat} (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) : y * (x * 19) < 19 * 2 ^ 108 := by
  have := lt108 hx hy
  calc y * (x * 19) = 19 * (x * y) := by ring
    _ < 19 * 2 ^ 108 := by omega

/-- Column 0 of `carry_mul` (instructions 34–91): the carried limb and carry of
    `a0 b0 + 19 (a1 b4 + a2 b3 + a3 b2 + a4 b1)`. -/
theorem col0 {P6 P7 P10 P9 P17 h6 l6 h7 l7 h10 l10 h9 l9 h17 l17 : Nat}
    {w34 w35 w52 w53 w58 w59 w80 w81 c34 c35 c52 c53 c58 c59 c80 c81 q89 c0 : Nat}
    (m6 : h6 * 2 ^ 64 + l6 = P6) (m7 : h7 * 2 ^ 64 + l7 = P7) (m10 : h10 * 2 ^ 64 + l10 = P10)
    (m9 : h9 * 2 ^ 64 + l9 = P9) (m17 : h17 * 2 ^ 64 + l17 = P17)
    (b6 : P6 < 19 * 2 ^ 108) (b7 : P7 < 19 * 2 ^ 108) (b10 : P10 < 19 * 2 ^ 108)
    (b9 : P9 < 19 * 2 ^ 108) (b17 : P17 < 2 ^ 108)
    (e34 : w34 + 2 ^ 64 * c34 = l6 + l7) (e35 : w35 + 2 ^ 64 * c35 = h7 + h6 + c34)
    (e52 : w52 + 2 ^ 64 * c52 = w34 + l10) (e53 : w53 + 2 ^ 64 * c53 = h10 + w35 + c52)
    (e58 : w58 + 2 ^ 64 * c58 = w52 + l9) (e59 : w59 + 2 ^ 64 * c59 = h9 + w53 + c58)
    (e80 : w80 + 2 ^ 64 * c80 = w58 + l17) (e81 : w81 + 2 ^ 64 * c81 = h17 + w59 + c80)
    (e89 : q89 = (w81 * 2 ^ 64 + w80) / 2 ^ 51 % 2 ^ 64) (e91 : c0 = w80 % 2 ^ 51) :
    c0 + 2 ^ 51 * q89 = P17 + P9 + P10 + P7 + P6 ∧ q89 < 2 ^ 64 := by
  have B := Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add b6 b7) b10) b9) b17
  have S34 := acc128S e34 e35 (T := P6 + P7) (by rw [← m6, ← m7]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add b6 b7) (by norm_num))
  have S52 := acc128S e52 e53 (T := P6 + P7 + P10) (by rw [← S34, ← m10]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add b6 b7) b10) (by norm_num))
  have S58 := acc128S e58 e59 (T := P6 + P7 + P10 + P9) (by rw [← S52, ← m9]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add b6 b7) b10) b9)
      (by norm_num))
  have F0 := acc128S e80 e81 (T := P6 + P7 + P10 + P9 + P17) (by rw [← S58, ← m17]; ac_rfl)
    (lt_of_lt_of_le B (by norm_num))
  have G0 := carry51 F0 e89 e91 (lt_of_lt_of_le B (by norm_num))
  exact ⟨G0.trans (by ac_rfl), e89 ▸ Nat.mod_lt _ (by norm_num)⟩

/-- Column 1 of `carry_mul` (instructions 36–107): the carried limb and carry of
    `a0 b1 + a1 b0 + 19 (a2 b4 + a3 b3 + a4 b2)` plus the carry of column 0. -/
theorem col1 {P1 P8 P13 P18 P3 h1 l1 h8 l8 h13 l13 h18 l18 h3 l3 : Nat}
    {w36 w37 w56 w57 w82 w83 w86 w87 w99 w100 c36 c37 c56 c57 c82 c83 c86 c87 c99 c100 : Nat}
    {q89 q107 c1 : Nat}
    (m1 : h1 * 2 ^ 64 + l1 = P1) (m8 : h8 * 2 ^ 64 + l8 = P8) (m13 : h13 * 2 ^ 64 + l13 = P13)
    (m18 : h18 * 2 ^ 64 + l18 = P18) (m3 : h3 * 2 ^ 64 + l3 = P3)
    (b1 : P1 < 19 * 2 ^ 108) (b8 : P8 < 19 * 2 ^ 108) (b13 : P13 < 19 * 2 ^ 108)
    (b18 : P18 < 2 ^ 108) (b3 : P3 < 2 ^ 108) (hq : q89 < 2 ^ 64)
    (e36 : w36 + 2 ^ 64 * c36 = l8 + l1) (e37 : w37 + 2 ^ 64 * c37 = h1 + h8 + c36)
    (e56 : w56 + 2 ^ 64 * c56 = w36 + l13) (e57 : w57 + 2 ^ 64 * c57 = h13 + w37 + c56)
    (e82 : w82 + 2 ^ 64 * c82 = w56 + l18) (e83 : w83 + 2 ^ 64 * c83 = h18 + w57 + c82)
    (e86 : w86 + 2 ^ 64 * c86 = w82 + l3) (e87 : w87 + 2 ^ 64 * c87 = w83 + h3 + c86)
    (e99 : w99 + 2 ^ 64 * c99 = w86 + q89) (e100 : w100 + 2 ^ 64 * c100 = w87 + c99)
    (e107 : q107 = (w100 * 2 ^ 64 + w99) / 2 ^ 51 % 2 ^ 64) (e106 : c1 = w99 % 2 ^ 51) :
    c1 + 2 ^ 51 * q107 = P3 + P18 + P13 + P1 + P8 + q89 ∧ q107 < 2 ^ 64 := by
  have B := Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add
    (Nat.add_lt_add b1 b8) b13) b18) b3) hq
  have S36 := acc128S e36 e37 (T := P1 + P8) (by rw [← m1, ← m8]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add b1 b8) (by norm_num))
  have S56 := acc128S e56 e57 (T := P1 + P8 + P13) (by rw [← S36, ← m13]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add b1 b8) b13) (by norm_num))
  have S82 := acc128S e82 e83 (T := P1 + P8 + P13 + P18) (by rw [← S56, ← m18]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add b1 b8) b13) b18)
      (by norm_num))
  have S86 := acc128S e86 e87 (T := P1 + P8 + P13 + P18 + P3) (by rw [← S82, ← m3]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add b1 b8)
      b13) b18) b3) (by norm_num))
  have F1 := acc128S (y1 := 0) e99 (by rw [Nat.add_zero]; exact e100)
    (T := P1 + P8 + P13 + P18 + P3 + q89) (by rw [← S86, Nat.zero_mul, Nat.add_zero])
    (lt_of_lt_of_le B (by norm_num))
  have G1 := carry51 F1 e107 e106 (lt_of_lt_of_le B (by norm_num))
  exact ⟨G1.trans (by ac_rfl), e107 ▸ Nat.mod_lt _ (by norm_num)⟩

/-- Column 2 of `carry_mul` (instructions 71–132): the carried limb and carry of
    `a0 b2 + a1 b1 + a2 b0 + 19 (a3 b4 + a4 b3)` plus the carry of column 1. -/
theorem col2 {P16 P4 P23 P21 P24 h16 l16 h4 l4 h23 l23 h21 l21 h24 l24 : Nat}
    {w71 w72 w113 w114 w115 w116 w119 w120 w121 w122 : Nat}
    {c71 c72 c113 c114 c115 c116 c119 c120 c121 c122 q107 q124 c2 : Nat}
    (m16 : h16 * 2 ^ 64 + l16 = P16) (m4 : h4 * 2 ^ 64 + l4 = P4)
    (m23 : h23 * 2 ^ 64 + l23 = P23) (m21 : h21 * 2 ^ 64 + l21 = P21)
    (m24 : h24 * 2 ^ 64 + l24 = P24)
    (b16 : P16 < 19 * 2 ^ 108) (b4 : P4 < 19 * 2 ^ 108) (b23 : P23 < 2 ^ 108)
    (b21 : P21 < 2 ^ 108) (b24 : P24 < 2 ^ 108) (hq : q107 < 2 ^ 64)
    (e71 : w71 + 2 ^ 64 * c71 = l16 + l4) (e72 : w72 + 2 ^ 64 * c72 = h16 + h4 + c71)
    (e113 : w113 + 2 ^ 64 * c113 = w71 + l23) (e114 : w114 + 2 ^ 64 * c114 = h23 + w72 + c113)
    (e115 : w115 + 2 ^ 64 * c115 = w113 + l21) (e116 : w116 + 2 ^ 64 * c116 = h21 + w114 + c115)
    (e119 : w119 + 2 ^ 64 * c119 = w115 + l24) (e120 : w120 + 2 ^ 64 * c120 = h24 + w116 + c119)
    (e121 : w121 + 2 ^ 64 * c121 = w119 + q107) (e122 : w122 + 2 ^ 64 * c122 = w120 + c121)
    (e124 : q124 = (w122 * 2 ^ 64 + w121) / 2 ^ 51 % 2 ^ 64) (e132 : c2 = w121 % 2 ^ 51) :
    c2 + 2 ^ 51 * q124 = P24 + P21 + P23 + P16 + P4 + q107 ∧ q124 < 2 ^ 64 := by
  have B := Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add
    (Nat.add_lt_add b16 b4) b23) b21) b24) hq
  have S71 := acc128S e71 e72 (T := P16 + P4) (by rw [← m16, ← m4]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add b16 b4) (by norm_num))
  have S113 := acc128S e113 e114 (T := P16 + P4 + P23) (by rw [← S71, ← m23]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add b16 b4) b23) (by norm_num))
  have S115 := acc128S e115 e116 (T := P16 + P4 + P23 + P21) (by rw [← S113, ← m21]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add b16 b4) b23) b21)
      (by norm_num))
  have S119 := acc128S e119 e120 (T := P16 + P4 + P23 + P21 + P24)
    (by rw [← S115, ← m24]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add b16 b4)
      b23) b21) b24) (by norm_num))
  have F2 := acc128S (y1 := 0) e121 (by rw [Nat.add_zero]; exact e122)
    (T := P16 + P4 + P23 + P21 + P24 + q107) (by rw [← S119, Nat.zero_mul, Nat.add_zero])
    (lt_of_lt_of_le B (by norm_num))
  have G2 := carry51 F2 e124 e132 (lt_of_lt_of_le B (by norm_num))
  exact ⟨G2.trans (by ac_rfl), e124 ▸ Nat.mod_lt _ (by norm_num)⟩

/-- Column 3 of `carry_mul` (instructions 50–141): the carried limb and carry of
    `a0 b3 + a1 b2 + a2 b1 + a3 b0 + 19 a4 b4` plus the carry of column 2. -/
theorem col3 {P12 P11 P14 P25 P5 h12 l12 h11 l11 h14 l14 h25 l25 h5 l5 : Nat}
    {w50 w51 w68 w69 w129 w130 w133 w134 w135 w136 : Nat}
    {c50 c51 c68 c69 c129 c130 c133 c134 c135 c136 q124 q141 c3 : Nat}
    (m12 : h12 * 2 ^ 64 + l12 = P12) (m11 : h11 * 2 ^ 64 + l11 = P11)
    (m14 : h14 * 2 ^ 64 + l14 = P14) (m25 : h25 * 2 ^ 64 + l25 = P25)
    (m5 : h5 * 2 ^ 64 + l5 = P5)
    (b12 : P12 < 19 * 2 ^ 108) (b11 : P11 < 2 ^ 108) (b14 : P14 < 2 ^ 108)
    (b25 : P25 < 2 ^ 108) (b5 : P5 < 2 ^ 108) (hq : q124 < 2 ^ 64)
    (e50 : w50 + 2 ^ 64 * c50 = l12 + l11) (e51 : w51 + 2 ^ 64 * c51 = h11 + h12 + c50)
    (e68 : w68 + 2 ^ 64 * c68 = w50 + l14) (e69 : w69 + 2 ^ 64 * c69 = h14 + w51 + c68)
    (e129 : w129 + 2 ^ 64 * c129 = l25 + w68) (e130 : w130 + 2 ^ 64 * c130 = h25 + w69 + c129)
    (e133 : w133 + 2 ^ 64 * c133 = w129 + l5) (e134 : w134 + 2 ^ 64 * c134 = w130 + h5 + c133)
    (e135 : w135 + 2 ^ 64 * c135 = w133 + q124) (e136 : w136 + 2 ^ 64 * c136 = w134 + c135)
    (e141 : q141 = (w136 * 2 ^ 64 + w135) / 2 ^ 51 % 2 ^ 64) (e140 : c3 = w135 % 2 ^ 51) :
    c3 + 2 ^ 51 * q141 = P5 + P25 + P14 + P11 + P12 + q124 ∧ q141 < 2 ^ 64 := by
  have B := Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add
    (Nat.add_lt_add b12 b11) b14) b25) b5) hq
  have S50 := acc128S e50 e51 (T := P12 + P11) (by rw [← m12, ← m11]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add b12 b11) (by norm_num))
  have S68 := acc128S e68 e69 (T := P12 + P11 + P14) (by rw [← S50, ← m14]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add b12 b11) b14) (by norm_num))
  have S129 := acc128S e129 e130 (T := P12 + P11 + P14 + P25) (by rw [← S68, ← m25]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add b12 b11) b14) b25)
      (by norm_num))
  have S133 := acc128S e133 e134 (T := P12 + P11 + P14 + P25 + P5)
    (by rw [← S129, ← m5]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add b12 b11)
      b14) b25) b5) (by norm_num))
  have F3 := acc128S (y1 := 0) e135 (by rw [Nat.add_zero]; exact e136)
    (T := P12 + P11 + P14 + P25 + P5 + q124) (by rw [← S133, Nat.zero_mul, Nat.add_zero])
    (lt_of_lt_of_le B (by norm_num))
  have G3 := carry51 F3 e141 e140 (lt_of_lt_of_le B (by norm_num))
  exact ⟨G3.trans (by ac_rfl), e141 ▸ Nat.mod_lt _ (by norm_num)⟩

/-- Column 4 of `carry_mul` (instructions 95–145): the low word and carry of
    `a0 b4 + a1 b3 + a2 b2 + a3 b1 + a4 b0` plus the carry of column 3; the carry leaves
    room for `19` times itself plus a limb. -/
theorem col4 {P15 P20 P19 P22 P2 h15 l15 h20 l20 h19 l19 h22 l22 h2 l2 : Nat}
    {w95 w96 w97 w98 w108 w109 w138 w139 w142 w143 : Nat}
    {c95 c96 c97 c98 c108 c109 c138 c139 c142 c143 q141 q145 : Nat}
    (m15 : h15 * 2 ^ 64 + l15 = P15) (m20 : h20 * 2 ^ 64 + l20 = P20)
    (m19 : h19 * 2 ^ 64 + l19 = P19) (m22 : h22 * 2 ^ 64 + l22 = P22)
    (m2 : h2 * 2 ^ 64 + l2 = P2)
    (b15 : P15 < 2 ^ 108) (b20 : P20 < 2 ^ 108) (b19 : P19 < 2 ^ 108)
    (b22 : P22 < 2 ^ 108) (b2 : P2 < 2 ^ 108) (hq : q141 < 2 ^ 64)
    (e95 : w95 + 2 ^ 64 * c95 = l15 + l20) (e96 : w96 + 2 ^ 64 * c96 = h20 + h15 + c95)
    (e97 : w97 + 2 ^ 64 * c97 = w95 + l19) (e98 : w98 + 2 ^ 64 * c98 = h19 + w96 + c97)
    (e108 : w108 + 2 ^ 64 * c108 = w97 + l22) (e109 : w109 + 2 ^ 64 * c109 = h22 + w98 + c108)
    (e138 : w138 + 2 ^ 64 * c138 = w108 + l2) (e139 : w139 + 2 ^ 64 * c139 = w109 + h2 + c138)
    (e142 : w142 + 2 ^ 64 * c142 = w138 + q141) (e143 : w143 + 2 ^ 64 * c143 = w139 + c142)
    (e145 : q145 = (w143 * 2 ^ 64 + w142) / 2 ^ 51 % 2 ^ 64) :
    w142 % 2 ^ 51 + 2 ^ 51 * q145 = P2 + P22 + P19 + P20 + P15 + q141 ∧
      19 * q145 + 2 ^ 51 ≤ 2 ^ 64 := by
  have B := Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add
    (Nat.add_lt_add b15 b20) b19) b22) b2) hq
  have S95 := acc128S e95 e96 (T := P15 + P20) (by rw [← m15, ← m20]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add b15 b20) (by norm_num))
  have S97 := acc128S e97 e98 (T := P15 + P20 + P19) (by rw [← S95, ← m19]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add b15 b20) b19) (by norm_num))
  have S108 := acc128S e108 e109 (T := P15 + P20 + P19 + P22) (by rw [← S97, ← m22]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add b15 b20) b19) b22)
      (by norm_num))
  have S138 := acc128S e138 e139 (T := P15 + P20 + P19 + P22 + P2)
    (by rw [← S108, ← m2]; ac_rfl)
    (lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add b15 b20)
      b19) b22) b2) (by norm_num))
  have F4 := acc128S (y1 := 0) e142 (by rw [Nat.add_zero]; exact e143)
    (T := P15 + P20 + P19 + P22 + P2 + q141) (by rw [← S138, Nat.zero_mul, Nat.add_zero])
    (lt_of_lt_of_le B (by norm_num))
  have G4 := (carry51 F4 e145 rfl (lt_of_lt_of_le B (by norm_num))).trans
    (show P15 + P20 + P19 + P22 + P2 + q141 = P2 + P22 + P19 + P20 + P15 + q141 by ac_rfl)
  refine ⟨G4, ?_⟩
  clear * - G4 hq b15 b20 b19 b22 b2
  omega

/-- The field congruence of the carried limbs: when `c0 … c4` and the carry `q` of the
    top column recompose the column sums of the partial products, `c0 … c4` together
    with `19 q` represent the product of the inputs modulo `2^255 - 19`. -/
theorem mul_mod_p (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 q : Nat)
    (h : c0 + 2 ^ 51 * c1 + 2 ^ 102 * c2 + 2 ^ 153 * c3 + 2 ^ 204 * c4 + 2 ^ 255 * q
      = (a0 * b0 + b4 * 19 * a1 + a2 * (b3 * 19) + a3 * (b2 * 19) + b1 * 19 * a4)
        + 2 ^ 51 * (b1 * a0 + b0 * a1 + b4 * 19 * a2 + b3 * 19 * a3 + b2 * 19 * a4)
        + 2 ^ 102 * (a0 * b2 + a1 * b1 + b0 * a2 + b4 * 19 * a3 + a4 * (b3 * 19))
        + 2 ^ 153 * (b3 * a0 + b2 * a1 + b1 * a2 + b0 * a3 + b4 * 19 * a4)
        + 2 ^ 204 * (a0 * b4 + b3 * a1 + a2 * b2 + b1 * a3 + a4 * b0)) :
    (c0 + 2 ^ 51 * c1 + 2 ^ 102 * c2 + 2 ^ 153 * c3 + 2 ^ 204 * c4 + 19 * q) % carryMulP
      = ((a0 + 2 ^ 51 * a1 + 2 ^ 102 * a2 + 2 ^ 153 * a3 + 2 ^ 204 * a4) *
          (b0 + 2 ^ 51 * b1 + 2 ^ 102 * b2 + 2 ^ 153 * b3 + 2 ^ 204 * b4)) % carryMulP := by
  have key : (c0 + 2 ^ 51 * c1 + 2 ^ 102 * c2 + 2 ^ 153 * c3 + 2 ^ 204 * c4 + 19 * q)
      + (2 ^ 255 - 19) * (q + (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1
        + 2 ^ 51 * (a2 * b4 + a3 * b3 + a4 * b2) + 2 ^ 102 * (a3 * b4 + a4 * b3)
        + 2 ^ 153 * (a4 * b4)))
      = (a0 + 2 ^ 51 * a1 + 2 ^ 102 * a2 + 2 ^ 153 * a3 + 2 ^ 204 * a4) *
          (b0 + 2 ^ 51 * b1 + 2 ^ 102 * b2 + 2 ^ 153 * b3 + 2 ^ 204 * b4) := by
    zify [show (19 : Nat) ≤ 2 ^ 255 by norm_num] at h ⊢
    linear_combination h
  rw [← key, carryMulP, Nat.add_mul_mod_self_left]

/-- The final carry of `carry_mul` (instructions 151–158): folding `r = 19 q` into the
    lowest limb and carrying twice recomposes the three low limbs exactly. -/
theorem tail_nat {c0 c1 c2 r x o0 y1 y2 o1 y3 o2 : Nat} (h0 : c0 < 2 ^ 51) (h1 : c1 < 2 ^ 51)
    (h2 : c2 < 2 ^ 51) (hr : r + 2 ^ 51 ≤ 2 ^ 64)
    (hx : x = (c0 + r) % 2 ^ 64) (ho0 : o0 = x % 2 ^ 51) (hy1 : y1 = x / 2 ^ 51)
    (hy2 : y2 = (y1 + c1) % 2 ^ 64) (ho1 : o1 = y2 % 2 ^ 51) (hy3 : y3 = y2 / 2 ^ 51)
    (ho2 : o2 = (y3 + c2) % 2 ^ 64) :
    o0 + 2 ^ 51 * o1 + 2 ^ 102 * o2 = c0 + r + 2 ^ 51 * c1 + 2 ^ 102 * c2 := by
  omega

end Arithmetic

/-! ## The abstract runs of the two segments -/

@[simp] theorem regsOf_rdi (v : RegCM) (base : String → BitVec 64) :
    regsOf v base "%rdi" = v.rdi := by simp [regsOf]
@[simp] theorem regsOf_rsp (v : RegCM) (base : String → BitVec 64) :
    regsOf v base "%rsp" = base "%rsp" := by simp [regsOf]
@[simp] theorem regsOf_r10 (v : RegCM) (base : String → BitVec 64) :
    regsOf v base "%r10" = v.r10 := by simp [regsOf]
@[simp] theorem regsOf_r11 (v : RegCM) (base : String → BitVec 64) :
    regsOf v base "%r11" = v.r11 := by simp [regsOf]
@[simp] theorem regsOf_r12 (v : RegCM) (base : String → BitVec 64) :
    regsOf v base "%r12" = v.r12 := by simp [regsOf]
@[simp] theorem regsOf_r13 (v : RegCM) (base : String → BitVec 64) :
    regsOf v base "%r13" = v.r13 := by simp [regsOf]
@[simp] theorem regsOf_r14 (v : RegCM) (base : String → BitVec 64) :
    regsOf v base "%r14" = v.r14 := by simp [regsOf]
@[simp] theorem regsOf_rbp (v : RegCM) (base : String → BitVec 64) :
    regsOf v base "%rbp" = v.rbp := by simp [regsOf]
@[simp] theorem regsOf_rbx (v : RegCM) (base : String → BitVec 64) :
    regsOf v base "%rbx" = v.rbx := by simp [regsOf]

/-- **The abstract run of instructions 5–146 meets `MidOut`.** From a state whose memory
    holds input limbs below `2^54` at `[rsi + 8i]` and `[rax + 8i]`, apart from the frame
    slots, and whose `%rdx` and `%r10` hold `19 b3` and `19 b2` (the two multiplies of
    `carryMulPre`), the run stores `%rdi` at `[rsp - 0x50]` and leaves the carried limbs
    and `19 q` in registers whose weighted sum is congruent to the product of the
    inputs modulo `2^255 - 19`. -/
theorem absRunMem_carryMulMid_spec (base : String → BitVec 64) (V : RegCM) (cf of : Bool)
    (mem : BitVec 64 → BitVec 64) (hsep : CellsSeparated carryMulMidCells base)
    {a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64}
    (hI : MidIn mem base a0 a1 a2 a3 a4 b0 b1 b2 b3 b4)
    (ha0 : a0.toNat < 2 ^ 54) (ha1 : a1.toNat < 2 ^ 54) (ha2 : a2.toNat < 2 ^ 54)
    (ha3 : a3.toNat < 2 ^ 54) (ha4 : a4.toNat < 2 ^ 54)
    (hb0 : b0.toNat < 2 ^ 54) (hb1 : b1.toNat < 2 ^ 54) (hb2 : b2.toNat < 2 ^ 54)
    (hb3 : b3.toNat < 2 ^ 54) (hb4 : b4.toNat < 2 ^ 54)
    (hrdx : V.rdx.toNat = b3.toNat * 19 % 2 ^ 64) (hr10 : V.r10.toNat = b2.toNat * 19 % 2 ^ 64) :
    MidOut base V.rdi a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
      (absRunMem carryMulMid (mkS base V cf of mem)) := by
  have hm19 : ∀ x : Nat, x < 2 ^ 54 → x * 19 % 2 ^ 64 = x * 19 := fun x hx =>
    Nat.mod_eq_of_lt (by omega)
  have hX : V.rdx.toNat = b3.toNat * 19 := by rw [hrdx, hm19 _ hb3]
  have hY : V.r10.toNat = b2.toNat * 19 := by rw [hr10, hm19 _ hb2]
  unfold carryMulMid carryMulMid1 carryMulMid2 carryMulMid3 carryMulMid4 carryMulMid5
  simp only [List.cons_append, List.nil_append]
  -- instructions 5–33: the partial products through `rsi`, `rax` and the frame spills
  refine run_mulxMem "%rcx" "%r11" "%rsi" 24 a3 hI.ha3 fun h1 l1 m1 => ?_
  refine run_mov_reg "%r8" "%rdx" ?_
  refine run_loadMem "%rdx" "%rsi" 0 a0 hI.ha0 ?_
  refine run_storeMem "%rsp" (-128) "%rbx" fun mm1 _ f1 => ?_
  replace hI := midIn_store hsep _ (by decide) f1 hI
  refine run_mulxMem "%rbx" "%r9" "%rax" 32 b4 hI.hb4 fun h2 l2 m2 => ?_
  refine run_loadMem "%rdx" "%rax" 8 b1 hI.hb1 ?_
  refine run_storeMem "%rsp" (-120) "%rbp" fun mm2 _ f2 => ?_
  replace hI := midIn_store hsep _ (by decide) f2 hI
  refine run_storeMem "%rsp" (-112) "%r12" fun mm3 _ f3 => ?_
  replace hI := midIn_store hsep _ (by decide) f3 hI
  refine run_mulxMem "%r12" "%rbp" "%rsi" 0 a0 hI.ha0 fun h3 l3 m3 => ?_
  refine run_loadMem "%rdx" "%rsi" 32 a4 hI.ha4 ?_
  refine run_storeMem "%rsp" (-104) "%r13" fun mm4 _ f4 => ?_
  replace hI := midIn_store hsep _ (by decide) f4 hI
  refine run_storeMem "%rsp" (-96) "%r14" fun mm5 _ f5 => ?_
  replace hI := midIn_store hsep _ (by decide) f5 hI
  refine run_mulx "%r14" "%r13" "%rdx" "%r8" fun h4 l4 m4 => ?_
  refine run_loadMem "%rdx" "%rax" 24 b3 hI.hb3 ?_
  refine run_storeMem "%rsp" (-88) "%r15" fun mm6 _ f6 => ?_
  replace hI := midIn_store hsep _ (by decide) f6 hI
  refine run_storeMem "%rsp" (-80) "%rdi" fun mm7 s7 f7 => ?_
  replace hI := midIn_store hsep _ (by decide) f7 hI
  refine run_mulxMem "%rdi" "%r15" "%rsi" 0 a0 hI.ha0 fun h5 l5 m5 => ?_
  refine run_imulriMem19 "%rdx" "%rax" 8 b1 hI.hb1 fun B1 _ eB1 => ?_
  refine run_storeMem "%rsp" (-72) "%rbx" fun mm8 s8 f8 => ?_
  replace hI := midIn_store hsep _ (by decide) f8 hI
  refine run_storeMem "%rsp" (-64) "%r9" fun mm9 s9 f9 => ?_
  replace hI := midIn_store hsep _ (by decide) f9 hI
  refine run_mulxMem "%r9" "%rbx" "%rsi" 32 a4 hI.ha4 fun h6 l6 m6 => ?_
  refine run_loadMem "%rdx" "%rsi" 24 a3 hI.ha3 ?_
  refine run_storeMem "%rsp" (-56) "%rdi" fun mm10 s10 f10 => ?_
  replace hI := midIn_store hsep _ (by decide) f10 hI
  refine run_storeMem "%rsp" (-48) "%r15" fun mm11 s11 f11 => ?_
  replace hI := midIn_store hsep _ (by decide) f11 hI
  refine run_mulx "%r15" "%rdi" "%rdx" "%r10" fun h7 l7 m7 => ?_
  refine run_mov_reg "%rdx" "%r10" ?_
  refine run_storeMem "%rsp" (-40) "%r12" fun mm12 s12 f12 => ?_
  replace hI := midIn_store hsep _ (by decide) f12 hI
  refine run_mulxMem "%r12" "%r10" "%rsi" 32 a4 hI.ha4 fun h8 l8 m8 => ?_
  refine run_imulriMem19 "%rdx" "%rax" 32 b4 hI.hb4 fun B4 _ eB4 => ?_
  -- instructions 34–63
  refine run_add "%rbx" "%rdi" fun w34 c34 _ e34 => ?_
  refine run_adcx "%r15" "%r9" fun w35 c35 e35 => ?_
  refine run_add "%r10" "%r11" fun w36 c36 _ e36 => ?_
  refine run_adcx "%rcx" "%r12" fun w37 c37 e37 => ?_
  refine run_mulxMem "%r9" "%r11" "%rsi" 8 a1 hI.ha1 fun h9 l9 m9 => ?_
  refine run_mov_reg "%rdi" "%rdx" ?_
  refine run_loadMem "%rdx" "%rsi" 16 a2 hI.ha2 ?_
  refine run_storeMem "%rsp" (-32) "%rbp" fun mm13 s13 f13 => ?_
  replace hI := midIn_store hsep _ (by decide) f13 hI
  refine run_mulx "%rbp" "%r12" "%rdx" "%r8" fun h10 l10 m10 => ?_
  refine run_loadMem "%rdx" "%rax" 0 b0 hI.hb0 ?_
  refine run_storeMem "%rsp" (-24) "%r14" fun mm14 s14 f14 => ?_
  replace hI := midIn_store hsep _ (by decide) f14 hI
  refine run_mulxMem "%r14" "%r8" "%rsi" 24 a3 hI.ha3 fun h11 l11 m11 => ?_
  refine run_mov_reg "%rdx" "%rdi" ?_
  refine run_storeMem "%rsp" (-16) "%r13" fun mm15 s15 f15 => ?_
  replace hI := midIn_store hsep _ (by decide) f15 hI
  refine run_mulxMem "%r13" "%rdi" "%rsi" 32 a4 hI.ha4 fun h12 l12 m12 => ?_
  refine run_testN 8 "%rax" (.reg "%rax") ?_
  refine run_adox "%rdi" "%r8" fun w50 c50 e50 => ?_
  refine run_adox "%r14" "%r13" fun w51 c51 e51 => ?_
  refine run_adcx "%rbx" "%r12" fun w52 c52 e52 => ?_
  refine run_adcx "%rbp" "%r15" fun w53 c53 e53 => ?_
  refine run_mulxMem "%r12" "%r15" "%rsi" 16 a2 hI.ha2 fun h13 l13 m13 => ?_
  refine run_xor_self "%r8" ?_
  refine run_adox "%r10" "%r15" fun w56 c56 e56 => ?_
  refine run_adox "%r12" "%rcx" fun w57 c57 e57 => ?_
  refine run_adcx "%rbx" "%r11" fun w58 c58 e58 => ?_
  refine run_adcx "%r9" "%rbp" fun w59 c59 e59 => ?_
  refine run_mov_reg "%rcx" "%rdx" ?_
  refine run_loadMem "%rdx" "%rax" 8 b1 hI.hb1 ?_
  refine run_mulxMem "%r13" "%r11" "%rsi" 16 a2 hI.ha2 fun h14 l14 m14 => ?_
  refine run_loadMem "%rdx" "%rsi" 32 a4 hI.ha4 ?_
  -- instructions 64–92
  refine run_mulxMem "%r15" "%rbp" "%rax" 0 b0 hI.hb0 fun h15 l15 m15 => ?_
  refine run_mov_reg "%rdx" "%rcx" ?_
  refine run_mulxMem "%r8" "%rcx" "%rsi" 24 a3 hI.ha3 fun h16 l16 m16 => ?_
  refine run_xor_self "%rdx" ?_
  refine run_adox "%rdi" "%r11" fun w68 c68 e68 => ?_
  refine run_adox "%r13" "%r14" fun w69 c69 e69 => ?_
  refine run_mov_reg "%r14" "%rcx" ?_
  refine run_adcxMem "%r14" "%rsp" (-16) l4 s15 fun w71 c71 e71 => ?_
  refine run_adcxMem "%r8" "%rsp" (-24) h4 ((f15 _ (slot_ne _ (by decide))).trans s14)
    fun w72 c72 e72 => ?_
  refine run_loadMem "%rdx" "%rsi" 0 a0 hI.ha0 ?_
  refine run_mulxMem "%rcx" "%r11" "%rax" 0 b0 hI.hb0 fun h17 l17 m17 => ?_
  refine run_loadMem "%rdx" "%rax" 0 b0 hI.hb0 ?_
  refine run_storeMem "%rsp" (-8) "%r13" fun mm16 s16 f16 => ?_
  replace hI := midIn_store hsep _ (by decide) f16 hI
  refine run_storeMem "%rsp" 0 "%rdi" fun mm17 s17 f17 => ?_
  replace hI := midIn_store hsep _ (by decide) f17 hI
  refine run_mulxMem "%rdi" "%r13" "%rsi" 8 a1 hI.ha1 fun h18 l18 m18 => ?_
  refine run_xor_self "%rdx" ?_
  refine run_adox "%rbx" "%r11" fun w80 c80 e80 => ?_
  refine run_adox "%rcx" "%r9" fun w81 c81 e81 => ?_
  refine run_adcx "%r10" "%r13" fun w82 c82 e82 => ?_
  refine run_adcx "%rdi" "%r12" fun w83 c83 e83 => ?_
  refine run_loadMem "%rdx" "%rsi" 16 a2 hI.ha2 ?_
  refine run_mulxMem "%r9" "%r12" "%rax" 16 b2 hI.hb2 fun h19 l19 m19 => ?_
  refine run_addMem "%r10" "%rsp" (-32) l3
    ((f17 _ (slot_ne _ (by decide))).trans ((f16 _ (slot_ne _ (by decide))).trans
      ((f15 _ (slot_ne _ (by decide))).trans ((f14 _ (slot_ne _ (by decide))).trans s13))))
    fun w86 c86 _ e86 => ?_
  refine run_adcxMem "%rdi" "%rsp" (-40) h3
    ((f17 _ (slot_ne _ (by decide))).trans ((f16 _ (slot_ne _ (by decide))).trans
      ((f15 _ (slot_ne _ (by decide))).trans ((f14 _ (slot_ne _ (by decide))).trans
        ((f13 _ (slot_ne _ (by decide))).trans s12)))))
    fun w87 c87 e87 => ?_
  refine run_mov_reg "%rdx" "%rbx" ?_
  refine run_shrd51 "%rdx" "%rcx" fun q89 _ _ e89 => ?_
  refine run_mov_imm "%r11" 51 ?_
  refine run_bzhi51 "%r13" "%rbx" "%r11" rfl fun c0w e91 => ?_
  refine run_mov_reg "%rbx" "%rdx" ?_
  -- instructions 93–120
  refine run_loadMem "%rdx" "%rax" 8 b1 hI.hb1 ?_
  refine run_mulxMem "%r11" "%rcx" "%rsi" 24 a3 hI.ha3 fun h20 l20 m20 => ?_
  refine run_adox "%rbp" "%rcx" fun w95 c95 e95 => ?_
  refine run_adox "%r11" "%r15" fun w96 c96 e96 => ?_
  refine run_add "%rbp" "%r12" fun w97 c97 _ e97 => ?_
  refine run_adcx "%r9" "%r11" fun w98 c98 e98 => ?_
  refine run_add "%r10" "%rbx" fun w99 c99 _ e99 => ?_
  refine run_adc_imm "%rdi" 0 fun w100 c100 _ e100 => ?_
  refine run_loadMem "%rdx" "%rsi" 8 a1 hI.ha1 ?_
  refine run_mulxMem "%r12" "%r15" "%rax" 8 b1 hI.hb1 fun h21 l21 m21 => ?_
  refine run_loadMem "%rdx" "%rax" 24 b3 hI.hb3 ?_
  refine run_mulxMem "%rcx" "%rbx" "%rsi" 8 a1 hI.ha1 fun h22 l22 m22 => ?_
  refine run_mov_imm "%rdx" 51 ?_
  refine run_bzhi51 "%r11" "%r10" "%rdx" rfl fun c1w e106 => ?_
  refine run_shrd51 "%r10" "%rdi" fun q107 _ _ e107 => ?_
  refine run_add "%rbp" "%rbx" fun w108 c108 _ e108 => ?_
  refine run_adcx "%rcx" "%r9" fun w109 c109 e109 => ?_
  refine run_loadMem "%rdx" "%rax" 0 b0 hI.hb0 ?_
  refine run_mulxMem "%rdi" "%r9" "%rsi" 16 a2 hI.ha2 fun h23 l23 m23 => ?_
  refine run_xor_self "%rdx" ?_
  refine run_adox "%r14" "%r9" fun w113 c113 e113 => ?_
  refine run_adox "%rdi" "%r8" fun w114 c114 e114 => ?_
  refine run_adcx "%r14" "%r15" fun w115 c115 e115 => ?_
  refine run_adcx "%r12" "%rdi" fun w116 c116 e116 => ?_
  refine run_loadMem "%rdx" "%rsi" 0 a0 hI.ha0 ?_
  refine run_mulxMem "%r15" "%r8" "%rax" 16 b2 hI.hb2 fun h24 l24 m24 => ?_
  refine run_add "%r14" "%r8" fun w119 c119 _ e119 => ?_
  refine run_adcx "%r15" "%r12" fun w120 c120 e120 => ?_
  -- instructions 121–146
  refine run_add "%r14" "%r10" fun w121 c121 _ e121 => ?_
  refine run_adc_imm "%r15" 0 fun w122 c122 _ e122 => ?_
  refine run_mov_reg "%rdx" "%r14" ?_
  refine run_shrd51 "%rdx" "%r15" fun q124 _ _ e124 => ?_
  refine run_mov_reg "%rbx" "%rdx" ?_
  refine run_loadMem "%rdx" "%rax" 16 b2 hI.hb2 ?_
  refine run_mulxMem "%r9" "%r10" "%rsi" 8 a1 hI.ha1 fun h25 l25 m25 => ?_
  refine run_mov_reg "%rdx" "%r10" ?_
  refine run_addMem "%rdx" "%rsp" 0 _ s17 fun w129 c129 _ e129 => ?_
  refine run_adcxMem "%r9" "%rsp" (-8) _ ((f17 _ (slot_ne _ (by decide))).trans s16)
    fun w130 c130 e130 => ?_
  refine run_mov_imm "%rdi" 51 ?_
  refine run_bzhi51 "%r12" "%r14" "%rdi" rfl fun c2w e132 => ?_
  refine run_adoxMem "%rdx" "%rsp" (-48) l5
    ((f17 _ (slot_ne _ (by decide))).trans ((f16 _ (slot_ne _ (by decide))).trans
      ((f15 _ (slot_ne _ (by decide))).trans ((f14 _ (slot_ne _ (by decide))).trans
        ((f13 _ (slot_ne _ (by decide))).trans ((f12 _ (slot_ne _ (by decide))).trans s11))))))
    fun w133 c133 e133 => ?_
  refine run_adoxMem "%r9" "%rsp" (-56) h5
    ((f17 _ (slot_ne _ (by decide))).trans ((f16 _ (slot_ne _ (by decide))).trans
      ((f15 _ (slot_ne _ (by decide))).trans ((f14 _ (slot_ne _ (by decide))).trans
        ((f13 _ (slot_ne _ (by decide))).trans ((f12 _ (slot_ne _ (by decide))).trans
          ((f11 _ (slot_ne _ (by decide))).trans s10)))))))
    fun w134 c134 e134 => ?_
  refine run_add "%rdx" "%rbx" fun w135 c135 _ e135 => ?_
  refine run_adc_imm "%r9" 0 fun w136 c136 _ e136 => ?_
  refine run_xor_self "%r8" ?_
  refine run_adoxMem "%rbp" "%rsp" (-64) l2
    ((f17 _ (slot_ne _ (by decide))).trans ((f16 _ (slot_ne _ (by decide))).trans
      ((f15 _ (slot_ne _ (by decide))).trans ((f14 _ (slot_ne _ (by decide))).trans
        ((f13 _ (slot_ne _ (by decide))).trans ((f12 _ (slot_ne _ (by decide))).trans
          ((f11 _ (slot_ne _ (by decide))).trans ((f10 _ (slot_ne _ (by decide))).trans
            s9))))))))
    fun w138 c138 e138 => ?_
  refine run_adoxMem "%rcx" "%rsp" (-72) h2
    ((f17 _ (slot_ne _ (by decide))).trans ((f16 _ (slot_ne _ (by decide))).trans
      ((f15 _ (slot_ne _ (by decide))).trans ((f14 _ (slot_ne _ (by decide))).trans
        ((f13 _ (slot_ne _ (by decide))).trans ((f12 _ (slot_ne _ (by decide))).trans
          ((f11 _ (slot_ne _ (by decide))).trans ((f10 _ (slot_ne _ (by decide))).trans
            ((f9 _ (slot_ne _ (by decide))).trans s8)))))))))
    fun w139 c139 e139 => ?_
  refine run_bzhi51 "%r14" "%rdx" "%rdi" rfl fun c3w e140 => ?_
  refine run_shrd51 "%rdx" "%r9" fun q141 _ _ e141 => ?_
  refine run_add "%rbp" "%rdx" fun w142 c142 _ e142 => ?_
  refine run_adc_imm "%rcx" 0 fun w143 c143 _ e143 => ?_
  refine run_mov_reg "%r15" "%rbp" ?_
  refine run_shrd51 "%r15" "%rcx" fun q145 _ _ e145 => ?_
  refine run_imulri19 "%rbx" "%r15" fun w146 _ _ e146 => ?_
  -- the output registers, the output-pointer slot and the limb equations
  dsimp only [RegRead.get, RegWrite.set] at *
  have hB1 : B1.toNat = b1.toNat * 19 := by rw [eB1, hm19 _ hb1]
  have hB4 : B4.toNat = b4.toNat * 19 := by rw [eB4, hm19 _ hb4]
  rw [hX] at m1 m4 m10
  rw [hY] at m7 m8
  rw [hB1] at m6
  rw [hB4] at m9 m12 m13 m16
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at e50 e52 e56 e58 e68 e71 e80 e82
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at e95 e113 e115 e133 e138
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, add_zero] at e100 e122 e136 e143
  obtain ⟨G0, Q89⟩ := col0 m6 m7 m10 m9 m17 (lt19l hb1 ha4) (lt19r hb2 ha3) (lt19r hb3 ha2)
    (lt19l hb4 ha1) (lt108 ha0 hb0) e34 e35 e52 e53 e58 e59 e80 e81 e89 e91
  obtain ⟨G1, Q107⟩ := col1 m1 m8 m13 m18 m3 (lt19l hb3 ha3) (lt19l hb2 ha4) (lt19l hb4 ha2)
    (lt108 hb0 ha1) (lt108 hb1 ha0) Q89 e36 e37 e56 e57 e82 e83 e86 e87 e99 e100 e107 e106
  obtain ⟨G2, Q124⟩ := col2 m16 m4 m23 m21 m24 (lt19l hb4 ha3) (lt19r hb3 ha4) (lt108 hb0 ha2)
    (lt108 ha1 hb1) (lt108 ha0 hb2) Q107 e71 e72 e113 e114 e115 e116 e119 e120 e121 e122 e124
    e132
  obtain ⟨G3, Q141⟩ := col3 m12 m11 m14 m25 m5 (lt19l hb4 ha4) (lt108 hb0 ha3) (lt108 hb1 ha2)
    (lt108 hb2 ha1) (lt108 hb3 ha0) Q124 e50 e51 e68 e69 e129 e130 e133 e134 e135 e136 e141
    e140
  obtain ⟨G4, B145⟩ := col4 m15 m20 m19 m22 m2 (lt108 ha4 hb0) (lt108 hb1 ha3) (lt108 ha2 hb2)
    (lt108 hb3 ha1) (lt108 ha0 hb4) Q141 e95 e96 e97 e98 e108 e109 e138 e139 e142 e143 e145
  have h146 : w146.toNat = 19 * q145.toNat := by
    rw [e146, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by norm_num)) B145)
  have key := mul_mod_p a0.toNat a1.toNat a2.toNat a3.toNat a4.toNat b0.toNat b1.toNat b2.toNat
    b3.toNat b4.toNat c0w.toNat c1w.toNat c2w.toNat c3w.toNat (w142.toNat % 2 ^ 51) q145.toNat
    (by linarith only [G0, G1, G2, G3, G4])
  simp only [MidOut, absRunMem, mkS, regsOf_rdi, regsOf_rsp, regsOf_r11, regsOf_r12, regsOf_r13,
    regsOf_r14, regsOf_rbp, regsOf_rbx]
  refine ⟨trivial, trivial, by rw [e91]; exact Nat.mod_lt _ (by norm_num),
    by rw [e106]; exact Nat.mod_lt _ (by norm_num), by rw [e132]; exact Nat.mod_lt _ (by norm_num),
    by rw [h146]; exact B145, ?_, ?_⟩
  · exact (f17 _ (slot_ne _ (by decide))).trans ((f16 _ (slot_ne _ (by decide))).trans
      ((f15 _ (slot_ne _ (by decide))).trans ((f14 _ (slot_ne _ (by decide))).trans
        ((f13 _ (slot_ne _ (by decide))).trans ((f12 _ (slot_ne _ (by decide))).trans
          ((f11 _ (slot_ne _ (by decide))).trans ((f10 _ (slot_ne _ (by decide))).trans
            ((f9 _ (slot_ne _ (by decide))).trans ((f8 _ (slot_ne _ (by decide))).trans
              s7)))))))))
  · rw [h146]
    exact key

/-- **The abstract run of instructions 148–166 meets `TailOut`.** From a state whose
    `%rdi` holds `51`, whose three low limb registers are below `2^51` and whose `%rbx`
    leaves room for a limb, the run folds `%rbx` into the lowest limb, carries twice, and
    stores five words at `[r10 + 8i]` whose value is the weighted sum of the limb
    registers with `%rbx`. -/
theorem absRunMem_carryMulTail_spec (base : String → BitVec 64) (V : RegCM) (cf of : Bool)
    (mem : BitVec 64 → BitVec 64) (h51 : V.rdi = 51#64) (h13 : V.r13.toNat < 2 ^ 51)
    (h11 : V.r11.toNat < 2 ^ 51) (h12 : V.r12.toNat < 2 ^ 51)
    (hbx : V.rbx.toNat + 2 ^ 51 ≤ 2 ^ 64) :
    TailOut V (absRunMem carryMulTail (mkS base V cf of mem)) := by
  unfold carryMulTail
  refine run_storeMem "%r10" 24 "%r14" fun m1 s1 f1 => ?_
  refine run_bzhi51 "%r9" "%rbp" "%rdi" h51 fun c4 e149 => ?_
  refine run_storeMem "%r10" 32 "%r9" fun m2 s2 f2 => ?_
  refine run_lea "%r13" "%r13" "%rbx" fun x ex => ?_
  refine run_bzhi51 "%r14" "%r13" "%rdi" h51 fun o0 eo0 => ?_
  refine run_storeMem "%r10" 0 "%r14" fun m3 s3 f3 => ?_
  refine run_shr51 "%r13" fun y1 _ _ ey1 => ?_
  refine run_lea "%r13" "%r13" "%r11" fun y2 ey2 => ?_
  refine run_bzhi51 "%r11" "%r13" "%rdi" h51 fun o1 eo1 => ?_
  refine run_shr51 "%r13" fun y3 _ _ ey3 => ?_
  refine run_lea "%r13" "%r13" "%r12" fun o2 eo2 => ?_
  refine run_storeMem "%r10" 16 "%r13" fun m4 s4 f4 => ?_
  refine run_storeMem "%r10" 8 "%r11" fun m5 s5 f5 => ?_
  refine run_loadMem "%rbx" "%rsp" (-128) _ rfl ?_
  refine run_loadMem "%rbp" "%rsp" (-120) _ rfl ?_
  refine run_loadMem "%r12" "%rsp" (-112) _ rfl ?_
  refine run_loadMem "%r13" "%rsp" (-104) _ rfl ?_
  refine run_loadMem "%r14" "%rsp" (-96) _ rfl ?_
  refine run_loadMem "%r15" "%rsp" (-88) _ rfl ?_
  dsimp only [RegRead.get, RegWrite.set] at *
  simp only [TailOut, absRunMem, mkS, regsOf_r10]
  refine ⟨trivial, ?_⟩
  have r0 : m5 (V.r10 + BitVec.ofInt 64 0) = o0 :=
    (f5 _ (slot_ne _ (by decide))).trans ((f4 _ (slot_ne _ (by decide))).trans s3)
  have r2 : m5 (V.r10 + BitVec.ofInt 64 16) = o2 := (f5 _ (slot_ne _ (by decide))).trans s4
  have r3 : m5 (V.r10 + BitVec.ofInt 64 24) = V.r14 :=
    (f5 _ (slot_ne _ (by decide))).trans ((f4 _ (slot_ne _ (by decide))).trans
      ((f3 _ (slot_ne _ (by decide))).trans ((f2 _ (slot_ne _ (by decide))).trans s1)))
  have r4 : m5 (V.r10 + BitVec.ofInt 64 32) = c4 :=
    (f5 _ (slot_ne _ (by decide))).trans ((f4 _ (slot_ne _ (by decide))).trans
      ((f3 _ (slot_ne _ (by decide))).trans s2))
  rw [r0, s5, r2, r3, r4, val5, e149]
  have := tail_nat h13 h11 h12 hbx ex eo0 ey1 ey2 eo1 ey3 eo2
  omega

/-! ## The machine statement -/

/-- The register valuation that addresses the cells of instructions 5–146 before the
    first instruction: `%rax` carries the second input pointer `%rdx`, which
    `xchg rdx, rax` moves into it, and `%rsp` is lowered by the frame of `sub rsp, 136`. -/
def carryMulMidRegs (regs : String → BitVec 64) (r : String) : BitVec 64 :=
  if r = "%rax" then regs "%rdx" else if r = "%rsp" then regs "%rsp" - 136#64 else regs r

/-- The register valuation that addresses the cells of instructions 148–166 before the
    first instruction: `%r10` carries the output pointer `%rdi`, which the kernel spills
    and reloads into it, and `%rsp` is lowered by the frame. -/
def carryMulTailRegs (regs : String → BitVec 64) (r : String) : BitVec 64 :=
  if r = "%r10" then regs "%rdi" else if r = "%rsp" then regs "%rsp" - 136#64 else regs r

/-- The record of the thirteen written registers read off a register valuation. -/
def RegCM.ofRegs (regs : String → BitVec 64) : RegCM :=
  ⟨regs "%rbx", regs "%rcx", regs "%rdx", regs "%rbp", regs "%rdi", regs "%r8", regs "%r9",
    regs "%r10", regs "%r11", regs "%r12", regs "%r13", regs "%r14", regs "%r15"⟩

/-- `regsOf` of the record read off `regs`, over `regs`, is `regs`. -/
theorem regsOf_ofRegs (regs : String → BitVec 64) : regsOf (RegCM.ofRegs regs) regs = regs := by
  have step : ∀ {r s : String} {x : BitVec 64}, x = regs r →
      (if r = s then regs s else x) = regs r := by
    intro r s x h
    by_cases e : r = s
    · subst e; exact if_pos rfl
    · rw [if_neg e, h]
  funext r
  exact step (step (step (step (step (step (step (step (step (step (step (step (step
    rfl))))))))))))

/-- The effect of instructions 1–4 on memory and on the registers the later segments
    read. -/
theorem runBlock_carryMulPre (st : JState 64) :
    (runBlock st carryMulPre).mem = st.mem ∧
    (runBlock st carryMulPre).regs "%rax" = st.regs "%rdx" ∧
    (runBlock st carryMulPre).regs "%rsp" = st.regs "%rsp" - 136#64 ∧
    ((runBlock st carryMulPre).regs "%rdx").toNat = (st.mem "%rdx" 24).toNat * 19 % 2 ^ 64 ∧
    ((runBlock st carryMulPre).regs "%r10").toNat = (st.mem "%rdx" 16).toNat * 19 % 2 ^ 64 ∧
    (runBlock st carryMulPre).regs "%rsi" = st.regs "%rsi" ∧
    (runBlock st carryMulPre).regs "%rdi" = st.regs "%rdi" := by
  have hw : ∀ (v1 v2 : BitVec 64), (x86_SUB v1 v2).word = v1 - v2 := fun _ _ => rfl
  have hi : ∀ (v1 v2 : BitVec 64), (x86_IMULt v1 v2).word = v1 * v2 := fun _ _ => rfl
  simp only [carryMulPre, runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W,
    JState.setReg, JState.get, JState.load, JOperand.eval, x86_XCHG, hw, hi]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [BitVec.toNat_mul]

/-- The effect of instruction 147 on memory and registers. -/
theorem runBlock_carryMulLoadOut (st : JState 64) :
    (runBlock st carryMulLoadOut).mem = st.mem ∧
    (runBlock st carryMulLoadOut).regs "%r10" = st.mem "%rsp" (-80) ∧
    ∀ r, r ≠ "%r10" → (runBlock st carryMulLoadOut).regs r = st.regs r := by
  refine ⟨rfl, ?_, fun r hr => ?_⟩
  · simp [carryMulLoadOut, evalInstr, JState.setReg, JState.load, x86_MOV]
  · simp [carryMulLoadOut, evalInstr, JState.setReg, x86_MOV, hr]

/-- Instruction 167 leaves memory unchanged. -/
theorem runBlock_carryMulPost_mem (st : JState 64) :
    (runBlock st carryMulPost).mem = st.mem := by
  simp [carryMulPost, evalInstr, JState.writeB5W]

/-- The base registers of a cell list whose registers all lie in `rs` agree with a
    valuation that agrees on `rs`. -/
theorem baseRegs_agree {cells : List (String × Int)} {regs regs' : String → BitVec 64}
    (h : ∀ r ∈ baseRegs cells, regs' r = regs r) :
    CellsSeparated cells regs → CellsSeparated cells regs' :=
  cellsSeparated_frame cells regs regs' h

/-- **Functional correctness of CryptOpt's `fiat_curve25519_carry_mul`.** For every
    machine state whose input limbs at `[rsi + 8i]` and `[rdx + 8i]` are below `2^54`,
    whose memory bank `%rax` agrees with `%rdx` on the second input (the kernel reads
    that input through `rax` after `xchg rdx, rax`), and whose cells are separated at the
    addresses the kernel uses (the inputs apart from the frame slots below
    `rsp - 136`, `carryMulMidRegs`; the outputs `[rdi + 8i]` apart from the saved-register
    slots, `carryMulTailRegs`), the five words `runBlock st carryMulBlock` writes through
    `%r10` meet fiat-crypto's `mul_correct` congruence against the inputs. -/
theorem carryMul_correct (st : JState 64)
    (hmid : CellsSeparated carryMulMidCells (carryMulMidRegs st.regs))
    (htail : CellsSeparated carryMulTailCells (carryMulTailRegs st.regs))
    (hbank : ∀ i : Fin 5, st.mem "%rax" (8 * (i.val : Int)) = st.mem "%rdx" (8 * (i.val : Int)))
    (ha : LimbsBelow54 (fun i => st.mem "%rsi" (8 * (i.val : Int))))
    (hb : LimbsBelow54 (fun i => st.mem "%rdx" (8 * (i.val : Int)))) :
    CarryMulSpec (fun i => st.mem "%rsi" (8 * (i.val : Int)))
      (fun i => st.mem "%rdx" (8 * (i.val : Int)))
      (fun i => (runBlock st carryMulBlock).mem "%r10" (8 * (i.val : Int))) := by
  have hblk : runBlock st carryMulBlock = runBlock (runBlock (runBlock (runBlock
      (runBlock st carryMulPre) carryMulMid) carryMulLoadOut) carryMulTail) carryMulPost := by
    rw [← carryMulBody_eq_block]
    simp only [runBlock_append]
  have ha' : ∀ i : Fin 5, (st.mem "%rsi" (8 * (i.val : Int))).toNat < 2 ^ 54 := ha
  have hb' : ∀ i : Fin 5, (st.mem "%rdx" (8 * (i.val : Int))).toNat < 2 ^ 54 := hb
  have e3 : ((3 : Fin 5) : Nat) = 3 := rfl
  have e4 : ((4 : Fin 5) : Nat) = 4 := rfl
  -- instructions 1–4
  obtain ⟨hm1, hax1, hsp1, hdx1, hr101, hsi1, hdi1⟩ := runBlock_carryMulPre st
  generalize hst1 : runBlock st carryMulPre = st1 at hm1 hax1 hsp1 hdx1 hr101 hsi1 hdi1 hblk
  have hsep1 : CellsSeparated carryMulMidCells st1.regs := by
    refine baseRegs_agree (fun r hr => ?_) hmid
    simp only [baseRegs, carryMulMidCells, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h <;> subst h <;> simp [carryMulMidRegs, hax1, hsp1, hsi1]
  -- instructions 5–146
  have hc1 : ∀ c ∈ carryMulMidCells,
      cellMem carryMulMidCells st1 (cellAddr st1.regs c) = st.mem c.1 c.2 := fun c hc =>
    (cellMem_eq _ _ hsep1 c hc).trans (by rw [hm1])
  have hSR1 := srmem_cellMem carryMulMidCells st1 hsep1
  rw [← regsOf_ofRegs st1.regs] at hSR1
  have hrun1 := carryMulMid_corres st1 _ hSR1 trivial
  have hI : MidIn (cellMem carryMulMidCells st1) st1.regs
      (st.mem "%rsi" 0) (st.mem "%rsi" 8) (st.mem "%rsi" 16) (st.mem "%rsi" 24)
      (st.mem "%rsi" 32) (st.mem "%rdx" 0) (st.mem "%rdx" 8) (st.mem "%rdx" 16)
      (st.mem "%rdx" 24) (st.mem "%rdx" 32) :=
    ⟨hc1 ("%rsi", 0) (by decide), hc1 ("%rsi", 8) (by decide), hc1 ("%rsi", 16) (by decide),
      hc1 ("%rsi", 24) (by decide), hc1 ("%rsi", 32) (by decide),
      (hc1 ("%rax", 0) (by decide)).trans (by simpa using hbank 0),
      (hc1 ("%rax", 8) (by decide)).trans (by simpa using hbank 1),
      (hc1 ("%rax", 16) (by decide)).trans (by simpa using hbank 2),
      (hc1 ("%rax", 24) (by decide)).trans (by simpa [e3] using hbank 3),
      (hc1 ("%rax", 32) (by decide)).trans (by simpa [e4] using hbank 4)⟩
  have hmo := absRunMem_carryMulMid_spec st1.regs (RegCM.ofRegs st1.regs)
    (st1.flagB (·.cf)) (st1.flagB (·.of)) (cellMem carryMulMidCells st1) hsep1 hI
    (by simpa using ha' 0) (by simpa using ha' 1) (by simpa using ha' 2)
    (by simpa [e3] using ha' 3) (by simpa [e4] using ha' 4)
    (by simpa using hb' 0) (by simpa using hb' 1) (by simpa using hb' 2)
    (by simpa [e3] using hb' 3) (by simpa [e4] using hb' 4) hdx1 hr101
  simp only [mkS] at hmo
  obtain ⟨h51, hsp2, h13, h11, h12, hbx, hout, hcong⟩ := hmo
  obtain ⟨⟨hreg2, -, -⟩, hmem2, -⟩ := hrun1
  generalize hs2 : absRunMem carryMulMid _ = s2 at h51 hsp2 h13 h11 h12 hbx hout hcong hreg2 hmem2
  generalize hst2 : runBlock st1 carryMulMid = st2 at hreg2 hmem2 hblk
  have hslot : st2.mem "%rsp" (-80) = st.regs "%rdi" := by
    rw [hmem2 ("%rsp", -80) (by decide)]
    simp only [cellAddr, hsp2]
    rw [hout]
    simp [RegCM.ofRegs, hdi1]
  -- instruction 147
  obtain ⟨hm3, hr103, hreg3⟩ := runBlock_carryMulLoadOut st2
  generalize hst3 : runBlock st2 carryMulLoadOut = st3 at hm3 hr103 hreg3 hblk
  have hsep3 : CellsSeparated carryMulTailCells st3.regs := by
    refine baseRegs_agree (fun r hr => ?_) htail
    simp only [baseRegs, carryMulTailCells, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h
    all_goals first
      | (rw [hreg3 "%rsp" (by decide), hreg2, hsp2, hsp1]; simp [carryMulTailRegs])
      | simp [carryMulTailRegs, hr103, hslot]
  -- instructions 148–166
  have hSR3 := srmem_cellMem carryMulTailCells st3 hsep3
  rw [← regsOf_ofRegs st3.regs] at hSR3
  have hrun3 := carryMulTail_corres st3 _ hSR3 trivial
  have hr3 : ∀ r, r ≠ "%r10" → st3.regs r = s2.c.regs r := fun r hr =>
    (hreg3 r hr).trans (hreg2 r)
  have htl := absRunMem_carryMulTail_spec st3.regs (RegCM.ofRegs st3.regs)
    (st3.flagB (·.cf)) (st3.flagB (·.of)) (cellMem carryMulTailCells st3)
    (by simp only [RegCM.ofRegs]; rw [hr3 _ (by decide), h51])
    (by simp only [RegCM.ofRegs]; rw [hr3 _ (by decide)]; exact h13)
    (by simp only [RegCM.ofRegs]; rw [hr3 _ (by decide)]; exact h11)
    (by simp only [RegCM.ofRegs]; rw [hr3 _ (by decide)]; exact h12)
    (by simp only [RegCM.ofRegs]; rw [hr3 _ (by decide)]; exact hbx)
  simp only [mkS] at htl
  obtain ⟨hr10s, hval⟩ := htl
  obtain ⟨⟨hreg4, -, -⟩, hmem4, -⟩ := hrun3
  -- instruction 167 and the output words
  rw [hblk, runBlock_carryMulPost_mem]
  have hout4 : ∀ o : Int, ("%r10", o) ∈ carryMulTailCells →
      (runBlock st3 carryMulTail).mem "%r10" o =
        (absRunMem carryMulTail ⟨⟨regsOf (RegCM.ofRegs st3.regs) st3.regs, st3.flagB (·.cf),
          st3.flagB (·.of)⟩, cellMem carryMulTailCells st3⟩).mem
          ((RegCM.ofRegs st3.regs).r10 + BitVec.ofInt 64 o) := by
    intro o ho
    rw [hmem4 _ ho]
    simp only [cellAddr, hr10s]
  have hv := hval
  have g13 : (RegCM.ofRegs st3.regs).r13 = s2.c.regs "%r13" := hr3 _ (by decide)
  have g11 : (RegCM.ofRegs st3.regs).r11 = s2.c.regs "%r11" := hr3 _ (by decide)
  have g12 : (RegCM.ofRegs st3.regs).r12 = s2.c.regs "%r12" := hr3 _ (by decide)
  have g14 : (RegCM.ofRegs st3.regs).r14 = s2.c.regs "%r14" := hr3 _ (by decide)
  have gbp : (RegCM.ofRegs st3.regs).rbp = s2.c.regs "%rbp" := hr3 _ (by decide)
  have gbx : (RegCM.ofRegs st3.regs).rbx = s2.c.regs "%rbx" := hr3 _ (by decide)
  rw [g13, g11, g12, g14, gbp, gbx] at hv
  rw [← hv] at hcong
  unfold CarryMulSpec eval5
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, e3, e4]
  rw [show ((8 : Int) * ((0 : Nat) : Int)) = 0 by norm_num,
    show ((8 : Int) * ((1 : Nat) : Int)) = 8 by norm_num,
    show ((8 : Int) * ((2 : Nat) : Int)) = 16 by norm_num,
    show ((8 : Int) * ((3 : Nat) : Int)) = 24 by norm_num,
    show ((8 : Int) * ((4 : Nat) : Int)) = 32 by norm_num]
  rw [hout4 0 (by decide), hout4 8 (by decide), hout4 16 (by decide), hout4 24 (by decide),
    hout4 32 (by decide)]
  simpa only [val5] using hcong

end CatCrypt.Crypto.SecureCompilation.Ascent.CarryMul
