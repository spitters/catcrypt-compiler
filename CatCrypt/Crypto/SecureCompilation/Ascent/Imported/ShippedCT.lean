/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.CallSeg
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519MulShipped
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519SqrShipped
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519AddShipped
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519SubShipped
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519CombSelectShipped
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519Join16Shipped
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PackSignShipped
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScMuladdShipped
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519MaddShipped
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519InvertShipped
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519CompressShipped
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519Pow22523Shipped

/-!
# Constant time of the shipped Ed25519 and fe25519 kernels

This module proves constant-time statements about the imported instruction lists
of the shipped kernels (`Ascent.Imported.*Shipped`), in the leakage model of
`X86Backend.MachineConstantTime`: the trace of branch decisions and memory
accesses `blockLeak`, where a memory access records the name of its base register
and its displacement, or the scaled value of its index register.

Each imported list prints back to the instruction sequence of the shipped `.s`
file (`bench/s2n_import/compare_owned.sh`), up to the normalisation and the frame
instructions documented in each imported module, so the statements are about
the shipped instructions. The omitted frame instructions (`push`, `pop`, the
stack allocation, `ret`) access memory only through `%rsp`.

## Leakage model and the base-register assumption

`instrLeak` records the base register of a memory access by name, not by value.
A statement about `blockLeak` therefore says nothing about the value of a base
register. `blockAddr` is the trace of effective addresses as processor words
(base value plus displacement, or plus scaled index value); the `_addr` theorems
state that it is determined by the SysV pointer arguments and `%rsp`. They are
the statement that every base register holds, at each access, a value computed
from public data. Both traces are about `JasminModel`, whose memory is keyed by
base-register name: a cell read back through a different register name than it
was written through is a different cell in the model.

## The analysis

`step` is a forward analysis over a public set `PubSet` of registers and memory
cells (§2). `check strict P body` requires every index register, and with
`strict = true` every base register, to be public at its access. `check_sound`
states that two states agreeing on `P` have equal `blockLeak` and, for
`strict = true`, equal `blockAddr`. `MachineConstantTime.CTAddressed` requires the
public registers to be written nowhere in the block; the index registers of the
kernels below are written in the block, so the flow-sensitive `check` is the
form that applies to them, with the same conclusion as
`MachineConstantTime.blockLeak_pub_determined`.

## Calls

A kernel with calls is a `List CallSeg`; its traces `segsLeak` and `segsAddr`
take the behaviour of the callees as a parameter `C : CallModel` (§7). The
leakage theorems assume only that each shipped callee has the leakage trace of
its imported code (`LeafModel`, `ShippedModel`) and nothing about the state a
callee returns. The address theorems also assume the SysV callee-saved registers
and the caller's argument slots are preserved across a call (`CalleeFrame`).
`shippedCalls` satisfies all of these hypotheses.

## Coverage

| Kernel | Leakage theorem | Hypotheses | Address theorem | Public set |
|---|---|---|---|---|
| `fe25519_mul` | `fe25519Mul_constant_time` | none | `fe25519Mul_addr` | `pub3` |
| `fe25519_sqr` | `fe25519Sqr_constant_time` | none | `fe25519Sqr_addr` | `pub2` |
| `fe25519_add` | `fe25519Add_constant_time` | none | `fe25519Add_addr` | `pub3` |
| `fe25519_sub` | `fe25519Sub_constant_time` | none | `fe25519Sub_addr` | `pub3` |
| `ed25519_comb_select` | `ed25519CombSelect_constant_time` | none | `ed25519CombSelect_addr` | `pubCombSelect` |
| `ed25519_join16` | `ed25519Join16_constant_time` | none | `ed25519Join16_addr` | `pub5` |
| `ed25519_pack_sign` | `ed25519PackSign_constant_time` | none | `ed25519PackSign_addr` | `pub3` |
| `ed25519_sc_reduce` | `ed25519ScReduce_constant_time` | none | `ed25519ScReduce_addr` | `pub2` |
| `ed25519_sc_muladd` | `ed25519ScMuladd_constant_time` | none | `ed25519ScMuladd_addr` | `pub4` |
| `ed25519_madd` | `ed25519Madd_constant_time` | `LeafModel C` | `ed25519Madd_addr` | `pub2`, frame |
| `ed25519_invert` | `ed25519Invert_constant_time` | `LeafModel C` | `ed25519Invert_addr` | `pub2`, frame |
| `fe25519_pow22523` | `fe25519Pow22523_constant_time` | `LeafModel C` | `fe25519Pow22523_addr` | `pub2`, frame |
| `ed25519_compress` | `ed25519Compress_constant_time` | `ShippedModel C` | `ed25519Compress_addr` | `pub4`, frame |

`shipped_kernels_constant_time` collects the leakage theorems.

The first five kernels have no indexed memory access and are covered by
`allDirect`. In the others every index register holds a value computed from
immediates, possibly stored in and reloaded from a `%rsp` cell, so their
checks pass from the empty public set. The checks of the two scalar kernels run
part by part, with the public set between parts stated explicitly.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
  (allDirect allDirect_constant_time)

/-! ## 1. Public sets and their agreement relation -/

/-- A set of public locations: registers, and memory cells `(base, off)` of the
    name-keyed memory of `JasminModel`. -/
structure PubSet where
  /-- The public registers. -/
  regs : List String
  /-- The public memory cells. -/
  cells : List (String × Int)
  deriving Repr, DecidableEq

/-- Two states agree on every location of `P`. -/
def PubSet.Agree {w : Nat} (P : PubSet) (s₁ s₂ : JState w) : Prop :=
  (∀ r ∈ P.regs, s₁.get r = s₂.get r) ∧ (∀ c ∈ P.cells, s₁.mem c.1 c.2 = s₂.mem c.1 c.2)

/-- The empty public set. -/
def PubSet.empty : PubSet := ⟨[], []⟩

/-- Any two states agree on the empty public set. -/
theorem PubSet.agree_empty {w : Nat} (s₁ s₂ : JState w) : PubSet.empty.Agree s₁ s₂ :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

/-- `A.le B`: every location of `A` is a location of `B`. -/
def PubSet.le (A B : PubSet) : Bool :=
  A.regs.all B.regs.contains && A.cells.all B.cells.contains

/-- Agreement on a larger public set implies agreement on a smaller one. -/
theorem PubSet.agree_of_le {w : Nat} {A B : PubSet} (h : A.le B = true) {s₁ s₂ : JState w}
    (hB : B.Agree s₁ s₂) : A.Agree s₁ s₂ := by
  simp only [PubSet.le, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨fun r hr => hB.1 r (h.1 r hr), fun c hc => hB.2 c (h.2 c hc)⟩

/-! ## 2. The forward public-data analysis

`step P i` is the public set after `i`, given that `P` is public before it. A
register written by `i` is public afterwards only when `i` is a `mov` of a public
operand, a `loadMem` of a public cell, or a `lea` of two public registers; every
other write makes it non-public. A cell is public afterwards when it is untouched
by `i` and public before, or when `i` is a `storeMem` of a public operand into it.
Flags are not tracked, so an instruction that reads a flag produces a non-public
value. -/

/-- The memory cells an instruction may write: `(b, o)` is written by `i` only if
    `touches i b o = true`. -/
def touches {w : Nat} : JInstr w → String → Int → Bool
  | .storeMem b o _, b', o' => b' == b && o' == o
  | .addToMem b o _, b', o' => b' == b && o' == o
  | .storeMemIdx b _ _ _, b', _ => b' == b
  | .loadSym d _, b', _ => b' == d
  | _, _, _ => false

/-- An instruction leaves every memory cell it does not touch unchanged. -/
theorem evalInstr_mem_of_not_touches {w : Nat} (s : JState w) (i : JInstr w) (b : String)
    (o : Int) (h : touches i b o = false) : (evalInstr s i).mem b o = s.mem b o := by
  cases i <;>
    simp_all [touches, evalInstr, JState.setReg, JState.writeB5W, JState.writeB5,
      JState.writeB2W, JState.store, JState.storeIdx, JState.writeB4W, JState.writeB5W2,
      JState.writeB5N, JState.writeCFW, JState.setRegMerge, JState.writeB5Mem]

/-- An operand whose value is determined by `P`: an immediate, or a register of `P`. -/
def opPub (P : PubSet) : JOperand → Bool
  | .reg r => P.regs.contains r
  | .imm _ => true

/-- A `P`-determined operand evaluates equally in two states agreeing on `P`. -/
theorem opPub_eval{w : Nat} {P : PubSet} {o : JOperand} (h : opPub P o = true)
    {s₁ s₂ : JState w} (hag : P.Agree s₁ s₂) : o.eval s₁ = o.eval s₂ := by
  cases o with
  | reg r =>
    simp only [opPub, List.contains_iff_mem] at h
    exact hag.1 r h
  | imm v => rfl

/-- The registers `i` writes with a value determined by `P`. -/
def newRegs {w : Nat} (P : PubSet) : JInstr w → List String
  | .mov d src => if opPub P src then [d] else []
  | .loadMem d b o => if P.cells.contains (b, o) then [d] else []
  | .lea d b x _ _ => if P.regs.contains b && P.regs.contains x then [d] else []
  | _ => []

/-- The memory cells `i` writes with a value determined by `P`. -/
def newCells {w : Nat} (P : PubSet) : JInstr w → List (String × Int)
  | .storeMem b o src => if opPub P src then [(b, o)] else []
  | _ => []

/-- The public set after `i`. -/
def step {w : Nat} (P : PubSet) (i : JInstr w) : PubSet where
  regs := newRegs P i ++ P.regs.filter (fun r => !(dstRegs i).contains r)
  cells := newCells P i ++ P.cells.filter (fun c => !touches i c.1 c.2)

/-- The registers of `newRegs P i` agree after `i` in two states agreeing on `P`. -/
theorem newRegs_sound{w : Nat} (P : PubSet) (i : JInstr w) {s₁ s₂ : JState w}
    (hag : P.Agree s₁ s₂) : ∀ r ∈ newRegs P i, (evalInstr s₁ i).get r = (evalInstr s₂ i).get r := by
  intro r hr
  cases i with
  | mov d src =>
    simp only [newRegs] at hr
    split at hr
    · rename_i h
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [evalInstr, JState.get_setReg_same, opPub_eval h hag]
    · simp at hr
  | loadMem d b o =>
    simp only [newRegs] at hr
    split at hr
    · rename_i h
      simp only [List.mem_singleton] at hr
      subst hr
      rw [List.contains_iff_mem] at h
      simp only [evalInstr, JState.get_setReg_same, JState.load, hag.2 _ h]
    · simp at hr
  | lea d b x sc off =>
    simp only [newRegs] at hr
    split at hr
    · rename_i h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [evalInstr, JState.get_setReg_same, hag.1 _ h.1, hag.1 _ h.2]
    · simp at hr
  | _ => simp [newRegs] at hr

/-- The cells of `newCells P i` agree after `i` in two states agreeing on `P`. -/
theorem newCells_sound{w : Nat} (P : PubSet) (i : JInstr w) {s₁ s₂ : JState w}
    (hag : P.Agree s₁ s₂) :
    ∀ c ∈ newCells P i, (evalInstr s₁ i).mem c.1 c.2 = (evalInstr s₂ i).mem c.1 c.2 := by
  intro c hc
  cases i with
  | storeMem b o src =>
    simp only [newCells] at hc
    split at hc
    · rename_i h
      simp only [List.mem_singleton] at hc
      subst hc
      simp only [evalInstr, JState.store, and_self, ite_true, opPub_eval h hag]
    · simp at hc
  | _ => simp [newCells] at hc

/-- **Soundness of one analysis step.** If two states agree on `P`, the states
    after `i` agree on `step P i`. -/
theorem step_sound {w : Nat} (P : PubSet) (i : JInstr w) {s₁ s₂ : JState w}
    (hag : P.Agree s₁ s₂) : (step P i).Agree (evalInstr s₁ i) (evalInstr s₂ i) := by
  refine ⟨fun r hr => ?_, fun c hc => ?_⟩
  · simp only [step, List.mem_append, List.mem_filter, Bool.not_eq_true'] at hr
    rcases hr with hr | ⟨hr, hnd⟩
    · exact newRegs_sound P i hag r hr
    · have hnd' : r ∉ dstRegs i := by simpa using hnd
      rw [evalInstr_get_of_not_dst s₁ i r hnd', evalInstr_get_of_not_dst s₂ i r hnd']
      exact hag.1 r hr
  · simp only [step, List.mem_append, List.mem_filter, Bool.not_eq_true'] at hc
    rcases hc with hc | ⟨hc, hnt⟩
    · exact newCells_sound P i hag c hc
    · rw [evalInstr_mem_of_not_touches s₁ i _ _ hnt, evalInstr_mem_of_not_touches s₂ i _ _ hnt]
      exact hag.2 c hc

/-- The public set after a block. -/
def run {w : Nat} (P : PubSet) : List (JInstr w) → PubSet
  | [] => P
  | i :: is => run (step P i) is

/-- **Soundness of the analysis over a block.** -/
theorem run_sound {w : Nat} (body : List (JInstr w)) :
    ∀ (P : PubSet) {s₁ s₂ : JState w}, P.Agree s₁ s₂ →
      (run P body).Agree (runBlock s₁ body) (runBlock s₂ body) := by
  induction body with
  | nil => intro P _ _ h; exact h
  | cons i is ih => intro P _ _ h; exact ih (step P i) (step_sound P i h)

/-! ## 3. The address trace and the checker -/

/-- The base register of a memory access of `i`, for each instruction that
    `instrLeak` records as a memory access. -/
def memBase {w : Nat} : JInstr w → Option String
  | .loadMem _ b _ | .storeMem b _ _ | .mulxMem _ _ _ b _ | .addMem _ b _
  | .adcxMem _ b _ | .adoxMem _ b _ | .imulMem _ b _ | .imulriMem _ b _ _
  | .addToMem b _ _ | .cmpMem _ b _ | .cmovccMem _ _ b _ | .loadMemIdx _ b _ _
  | .storeMemIdx b _ _ _ | .aluMem _ _ b _ | .andnMem _ _ b _ => some b
  | _ => none

/-- The effective addresses `i` accesses from state `s`, as processor words: the
    value of the base register plus the displacement, or plus `scale` times the
    value of the index register. One entry per event of `instrLeak s i`. -/
def instrAddr {w : Nat} (s : JState w) : JInstr w → List (BitVec w)
  | .loadMem _ b o | .storeMem b o _ | .mulxMem _ _ _ b o | .addMem _ b o
  | .adcxMem _ b o | .adoxMem _ b o | .imulMem _ b o | .imulriMem _ b o _ | .cmpMem _ b o
  | .cmovccMem _ _ b o | .aluMem _ _ b o | .andnMem _ _ b o =>
      [s.get b + BitVec.ofInt w o]
  | .addToMem b o _ => [s.get b + BitVec.ofInt w o, s.get b + BitVec.ofInt w o]
  | .loadMemIdx _ b x sc | .storeMemIdx b x sc _ =>
      [s.get b + BitVec.ofNat w (sc * (s.get x).toNat)]
  | _ => []

/-- The address trace of a block, threaded through `evalInstr` as `blockLeak`. -/
def blockAddr {w : Nat} (s : JState w) : List (JInstr w) → List (BitVec w)
  | [] => []
  | i :: is => instrAddr s i ++ blockAddr (evalInstr s i) is

/-- The index register of `i`, if any, is in `P`. -/
def idxOk {w : Nat} (P : PubSet) (i : JInstr w) : Bool :=
  match idxReg i with
  | some x => P.regs.contains x
  | none => true

/-- The base register of the memory access of `i`, if any, is in `P`. -/
def baseOk {w : Nat} (P : PubSet) (i : JInstr w) : Bool :=
  match memBase i with
  | some b => P.regs.contains b
  | none => true

/-- The checker: along the block, every index register is public; with
    `strict = true`, every base register is public as well. -/
def check {w : Nat} (strict : Bool) : PubSet → List (JInstr w) → Bool
  | _, [] => true
  | P, i :: is => idxOk P i && (!strict || baseOk P i) && check strict (step P i) is

/-- An instruction whose index register is in `P` leaks equally from two states
    agreeing on `P`. -/
theorem instrLeak_eq_of_idxOk{w : Nat} {P : PubSet} {i : JInstr w} (h : idxOk P i = true)
    {s₁ s₂ : JState w} (hag : P.Agree s₁ s₂) : instrLeak s₁ i = instrLeak s₂ i := by
  cases i with
  | loadMemIdx d b x sc =>
    simp only [idxOk, idxReg, List.contains_iff_mem] at h
    simp only [instrLeak, hag.1 x h]
  | storeMemIdx b x sc src =>
    simp only [idxOk, idxReg, List.contains_iff_mem] at h
    simp only [instrLeak, hag.1 x h]
  | _ => rfl

/-- An instruction whose index and base registers are in `P` accesses the same
    addresses from two states agreeing on `P`. -/
theorem instrAddr_eq_of_ok{w : Nat} {P : PubSet} {i : JInstr w} (hi : idxOk P i = true)
    (hb : baseOk P i = true) {s₁ s₂ : JState w} (hag : P.Agree s₁ s₂) :
    instrAddr s₁ i = instrAddr s₂ i := by
  cases i <;>
    simp only [idxOk, baseOk, idxReg, memBase, List.contains_iff_mem] at hi hb <;>
    simp only [instrAddr] <;>
    first | rfl | simp only [hag.1 _ hb, hag.1 _ hi] | simp only [hag.1 _ hb]

/-- **Soundness of the checker.** If `check strict P body` holds, any two states
    agreeing on `P` have the same leakage trace, and with `strict = true` the same
    address trace. -/
theorem check_sound {w : Nat} (strict : Bool) (body : List (JInstr w)) :
    ∀ (P : PubSet), check strict P body = true → ∀ {s₁ s₂ : JState w}, P.Agree s₁ s₂ →
      blockLeak s₁ body = blockLeak s₂ body ∧
        (strict = true → blockAddr s₁ body = blockAddr s₂ body) := by
  induction body with
  | nil => intro _ _ _ _ _; exact ⟨rfl, fun _ => rfl⟩
  | cons i is ih =>
    intro P hc s₁ s₂ hag
    simp only [check, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨hi, hb⟩, hrest⟩ := hc
    obtain ⟨hl, ha⟩ := ih (step P i) hrest (step_sound P i hag)
    refine ⟨?_, fun hs => ?_⟩
    · simp only [blockLeak_cons, instrLeak_eq_of_idxOk hi hag, hl]
    · have hb' : baseOk P i = true := by
        rcases hb with h | h
        · simp [hs] at h
        · exact h
      simp only [blockAddr, instrAddr_eq_of_ok hi hb' hag, ha hs]

/-- Leakage form of `check_sound`. -/
theorem check_leak {w : Nat} {strict : Bool} {body : List (JInstr w)} {P : PubSet}
    (hc : check strict P body = true) {s₁ s₂ : JState w} (hag : P.Agree s₁ s₂) :
    blockLeak s₁ body = blockLeak s₂ body :=
  (check_sound strict body P hc hag).1

/-- Address form of `check_sound`. -/
theorem check_addr {w : Nat} {body : List (JInstr w)} {P : PubSet}
    (hc : check true P body = true) {s₁ s₂ : JState w} (hag : P.Agree s₁ s₂) :
    blockAddr s₁ body = blockAddr s₂ body :=
  (check_sound true body P hc hag).2 rfl

/-- A block passing the checker from the empty public set has a leakage trace
    independent of the initial state. -/
theorem check_empty_leak {w : Nat} {strict : Bool} {body : List (JInstr w)}
    (hc : check strict PubSet.empty body = true) (s₁ s₂ : JState w) :
    blockLeak s₁ body = blockLeak s₂ body :=
  check_leak hc (PubSet.agree_empty s₁ s₂)

/-- A check of a concatenation, from a check of each side and the public set
    between them. -/
theorem check_append_of {w : Nat} {strict : Bool} {P Q : PubSet} {a b : List (JInstr w)}
    (ha : check strict P a = true ∧ run P a = Q) (hb : check strict Q b = true) :
    check strict P (a ++ b) = true := by
  induction a generalizing P with
  | nil => obtain ⟨-, rfl⟩ := ha; exact hb
  | cons i is ih =>
    obtain ⟨h1, h2⟩ := ha
    simp only [check, Bool.and_eq_true] at h1
    simp only [List.cons_append, check, Bool.and_eq_true]
    exact ⟨h1.1, ih ⟨h1.2, h2⟩⟩

/-! ## 4. Public sets of the SysV entry state

The pointer arguments of each kernel and `%rsp` are public. The second argument
of `ed25519_comb_select` is the secret digit, so it is not in its set. -/

/-- The public set naming the registers `rs` and no memory cell. -/
def regsPub (rs : List String) : PubSet := ⟨rs, []⟩

/-- The public set naming the registers `rs` and the `%rsp` cells at offsets `os`. -/
def rspPub (rs : List String) (os : List Int) : PubSet := ⟨rs, os.map (("%rsp", ·))⟩

/-- `f(out, x)`: `%rdi`, `%rsi`, `%rsp`. -/
def pub2 : PubSet := regsPub ["%rdi", "%rsi", "%rsp"]

/-- `f(out, x, y)`: `%rdi`, `%rsi`, `%rdx`, `%rsp`. -/
def pub3 : PubSet := regsPub ["%rdi", "%rsi", "%rdx", "%rsp"]

/-- `f(out, a, b, c)`: `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%rsp`. -/
def pub4 : PubSet := regsPub ["%rdi", "%rsi", "%rdx", "%rcx", "%rsp"]

/-- `f(out, a, b, c, d)`: `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8`, `%rsp`. -/
def pub5 : PubSet := regsPub ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%rsp"]

/-- `ed25519_comb_select(tbl, d, out)`: `%rdi`, `%rdx`, `%rsp`; the digit `%rsi` is
    not public. -/
def pubCombSelect : PubSet := regsPub ["%rdi", "%rdx", "%rsp"]

/-! ## 5. Call-free kernels without indexed memory

Every instruction of these blocks is direct (`allDirect`), so the leakage trace
is the same from any two states (`allDirect_constant_time`). -/

open Fe25519MulShipped in
/-- `fe25519_mul`: the leakage trace is the same from any two states. -/
theorem fe25519Mul_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ fe25519MulShippedBlock = blockLeak s₂ fe25519MulShippedBlock :=
  allDirect_constant_time _ (by decide +kernel) s₁ s₂

open Fe25519SqrShipped in
/-- `fe25519_sqr`: the leakage trace is the same from any two states. -/
theorem fe25519Sqr_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ fe25519SqrShippedBlock = blockLeak s₂ fe25519SqrShippedBlock :=
  allDirect_constant_time _ (by decide +kernel) s₁ s₂

open Fe25519AddShipped in
/-- `fe25519_add`: the leakage trace is the same from any two states. -/
theorem fe25519Add_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ fe25519AddShippedBlock = blockLeak s₂ fe25519AddShippedBlock :=
  allDirect_constant_time _ (by decide +kernel) s₁ s₂

open Fe25519SubShipped in
/-- `fe25519_sub`: the leakage trace is the same from any two states. -/
theorem fe25519Sub_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ fe25519SubShippedBlock = blockLeak s₂ fe25519SubShippedBlock :=
  allDirect_constant_time _ (by decide +kernel) s₁ s₂

open Ed25519CombSelectShipped in
/-- `ed25519_comb_select`: the leakage trace is the same from any two states. -/
theorem ed25519CombSelect_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ ed25519CombSelectShippedBlock = blockLeak s₂ ed25519CombSelectShippedBlock :=
  allDirect_constant_time _ (by decide +kernel) s₁ s₂

/-! ### Address traces of the direct kernels -/

open Fe25519MulShipped in
/-- `fe25519_mul`: the address trace is determined by `%rdi`, `%rsi`, `%rdx`, `%rsp`. -/
theorem fe25519Mul_addr (s₁ s₂ : JState 64) (hag : pub3.Agree s₁ s₂) :
    blockAddr s₁ fe25519MulShippedBlock = blockAddr s₂ fe25519MulShippedBlock :=
  check_addr (by decide +kernel) hag

open Fe25519SqrShipped in
/-- `fe25519_sqr`: the address trace is determined by `%rdi`, `%rsi`, `%rsp`. -/
theorem fe25519Sqr_addr (s₁ s₂ : JState 64) (hag : pub2.Agree s₁ s₂) :
    blockAddr s₁ fe25519SqrShippedBlock = blockAddr s₂ fe25519SqrShippedBlock :=
  check_addr (by decide +kernel) hag

open Fe25519AddShipped in
/-- `fe25519_add`: the address trace is determined by `%rdi`, `%rsi`, `%rdx`, `%rsp`. -/
theorem fe25519Add_addr (s₁ s₂ : JState 64) (hag : pub3.Agree s₁ s₂) :
    blockAddr s₁ fe25519AddShippedBlock = blockAddr s₂ fe25519AddShippedBlock :=
  check_addr (by decide +kernel) hag

open Fe25519SubShipped in
/-- `fe25519_sub`: the address trace is determined by `%rdi`, `%rsi`, `%rdx`, `%rsp`. -/
theorem fe25519Sub_addr (s₁ s₂ : JState 64) (hag : pub3.Agree s₁ s₂) :
    blockAddr s₁ fe25519SubShippedBlock = blockAddr s₂ fe25519SubShippedBlock :=
  check_addr (by decide +kernel) hag

open Ed25519CombSelectShipped in
/-- `ed25519_comb_select`: the address trace is determined by `%rdi`, `%rdx`, `%rsp`,
    whatever the digit in `%rsi`. -/
theorem ed25519CombSelect_addr (s₁ s₂ : JState 64) (hag : pubCombSelect.Agree s₁ s₂) :
    blockAddr s₁ ed25519CombSelectShippedBlock = blockAddr s₂ ed25519CombSelectShippedBlock :=
  check_addr (by decide +kernel) hag

/-! ## 6. Call-free kernels with indexed memory

Every index register of these blocks holds, at its access, a value computed from
immediates only, possibly through `%rsp` cells, so the checker passes from the
empty public set: the leakage trace is the same from any two states. From the
entry public set the checker also passes with base registers required public. -/

open Ed25519Join16Shipped in
/-- `ed25519_join16`: the leakage trace is the same from any two states. -/
theorem ed25519Join16_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ ed25519Join16ShippedBlock = blockLeak s₂ ed25519Join16ShippedBlock :=
  check_empty_leak (strict := false) (by decide +kernel) s₁ s₂

open Ed25519Join16Shipped in
/-- `ed25519_join16`: the address trace is determined by its five pointer arguments
    and `%rsp`. -/
theorem ed25519Join16_addr (s₁ s₂ : JState 64) (hag : pub5.Agree s₁ s₂) :
    blockAddr s₁ ed25519Join16ShippedBlock = blockAddr s₂ ed25519Join16ShippedBlock :=
  check_addr (by decide +kernel) hag

open Ed25519PackSignShipped in
/-- `ed25519_pack_sign`: the leakage trace is the same from any two states. -/
theorem ed25519PackSign_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ ed25519PackSignShippedBlock = blockLeak s₂ ed25519PackSignShippedBlock :=
  check_empty_leak (strict := false) (by decide +kernel) s₁ s₂

open Ed25519PackSignShipped in
/-- `ed25519_pack_sign`: the address trace is determined by `%rdi`, `%rsi`, `%rdx`,
    `%rsp`. -/
theorem ed25519PackSign_addr (s₁ s₂ : JState 64) (hag : pub3.Agree s₁ s₂) :
    blockAddr s₁ ed25519PackSignShippedBlock = blockAddr s₂ ed25519PackSignShippedBlock :=
  check_addr (by decide +kernel) hag

/-! ### `ed25519_sc_reduce`, part by part

Each `*_partNN` theorem checks one part of the imported block from the public set
after the previous part and states the public set after it; the `strict` family
starts from the entry set `pub2`, the `empty` family from the empty set. -/

/-- The `%rsp` offsets public after parts 1 to 4 from the entry set. -/
def scrCellsA : List Int := [88, 96, 104, 112, 40, 32, 24, 16, 8, 168, 160, 152, 144, 136, 224, 232]

/-- The `%rsp` offsets public after parts 1 to 4 from the empty set. -/
def scrCellsB : List Int := [88, 96, 104, 112, 40, 32, 24, 16, 8, 168, 160, 152, 144]

/-- The `%rsp` offsets public after part 6 from the entry set. -/
def scrCellsC : List Int := [88, 96, 104, 112, 24, 16, 8, 168, 160, 152, 144, 136, 224, 232]

/-- The `%rsp` offsets public after part 6 from the empty set. -/
def scrCellsD : List Int := [88, 96, 104, 112, 24, 16, 8, 168, 160, 152, 144]

/-- The `%rsp` offsets public after part 7, from either entry set: part 7 ends in
    the stack-clearing pass's thirty zero stores, and a cell holding the public
    constant zero is public. -/
def scrCellsE : List Int :=
  [56, 48, 0, 128, 120, 80, 72, 168, 160, 152, 144, 136, 176, 184, 192, 200, 208, 216, 224, 232,
    88, 96, 104, 112, 24, 16, 8]

section ScReduce
open Ed25519ScReduceShipped

theorem scReduce_strict_part01 :
    check true pub2 ed25519ScReduceShippedPart01 = true ∧
      run pub2 ed25519ScReduceShippedPart01 =
        rspPub ["%rbp", "%r14", "%r15", "%rsp"] scrCellsA := by decide +kernel
theorem scReduce_strict_part02 :
    check true (rspPub ["%rbp", "%r14", "%r15", "%rsp"] scrCellsA)
        ed25519ScReduceShippedPart02 = true ∧
      run (rspPub ["%rbp", "%r14", "%r15", "%rsp"] scrCellsA) ed25519ScReduceShippedPart02 =
        rspPub ["%r15", "%r14", "%rsp"] scrCellsA := by decide +kernel
theorem scReduce_strict_part03 :
    check true (rspPub ["%r15", "%r14", "%rsp"] scrCellsA) ed25519ScReduceShippedPart03 = true ∧
      run (rspPub ["%r15", "%r14", "%rsp"] scrCellsA) ed25519ScReduceShippedPart03 =
        rspPub ["%r14", "%r15", "%rsp"] scrCellsA := by decide +kernel
theorem scReduce_strict_part04 :
    check true (rspPub ["%r14", "%r15", "%rsp"] scrCellsA) ed25519ScReduceShippedPart04 = true ∧
      run (rspPub ["%r14", "%r15", "%rsp"] scrCellsA) ed25519ScReduceShippedPart04 =
        rspPub ["%r14", "%r15", "%rsp"] scrCellsA := by decide +kernel
theorem scReduce_strict_part05 :
    check true (rspPub ["%r14", "%r15", "%rsp"] scrCellsA) ed25519ScReduceShippedPart05 = true ∧
      run (rspPub ["%r14", "%r15", "%rsp"] scrCellsA) ed25519ScReduceShippedPart05 =
        rspPub ["%r14", "%r15", "%rsp"] (scrCellsA.erase 40) := by decide +kernel
theorem scReduce_strict_part06 :
    check true (rspPub ["%r14", "%r15", "%rsp"] (scrCellsA.erase 40))
        ed25519ScReduceShippedPart06 = true ∧
      run (rspPub ["%r14", "%r15", "%rsp"] (scrCellsA.erase 40)) ed25519ScReduceShippedPart06 =
        rspPub ["%r14", "%r15", "%rsp"] scrCellsC := by decide +kernel
theorem scReduce_strict_part07 :
    check true (rspPub ["%r14", "%r15", "%rsp"] scrCellsC) ed25519ScReduceShippedPart07 = true ∧
      run (rspPub ["%r14", "%r15", "%rsp"] scrCellsC) ed25519ScReduceShippedPart07 =
        rspPub ["%r8", "%rsp"] scrCellsE := by decide +kernel
theorem scReduce_strict_part08 :
    check true (rspPub ["%r8", "%rsp"] scrCellsE)
      ed25519ScReduceShippedPart08 = true := by decide +kernel

theorem scReduce_empty_part01 :
    check false PubSet.empty ed25519ScReduceShippedPart01 = true ∧
      run PubSet.empty ed25519ScReduceShippedPart01 =
        rspPub ["%rbp", "%r14", "%r15"] scrCellsB := by decide +kernel
theorem scReduce_empty_part02 :
    check false (rspPub ["%rbp", "%r14", "%r15"] scrCellsB) ed25519ScReduceShippedPart02 = true ∧
      run (rspPub ["%rbp", "%r14", "%r15"] scrCellsB) ed25519ScReduceShippedPart02 =
        rspPub ["%r15", "%r14"] scrCellsB := by decide +kernel
theorem scReduce_empty_part03 :
    check false (rspPub ["%r15", "%r14"] scrCellsB) ed25519ScReduceShippedPart03 = true ∧
      run (rspPub ["%r15", "%r14"] scrCellsB) ed25519ScReduceShippedPart03 =
        rspPub ["%r14", "%r15"] scrCellsB := by decide +kernel
theorem scReduce_empty_part04 :
    check false (rspPub ["%r14", "%r15"] scrCellsB) ed25519ScReduceShippedPart04 = true ∧
      run (rspPub ["%r14", "%r15"] scrCellsB) ed25519ScReduceShippedPart04 =
        rspPub ["%r14", "%r15"] scrCellsB := by decide +kernel
theorem scReduce_empty_part05 :
    check false (rspPub ["%r14", "%r15"] scrCellsB) ed25519ScReduceShippedPart05 = true ∧
      run (rspPub ["%r14", "%r15"] scrCellsB) ed25519ScReduceShippedPart05 =
        rspPub ["%r14", "%r15"] (scrCellsB.erase 40) := by decide +kernel
theorem scReduce_empty_part06 :
    check false (rspPub ["%r14", "%r15"] (scrCellsB.erase 40))
        ed25519ScReduceShippedPart06 = true ∧
      run (rspPub ["%r14", "%r15"] (scrCellsB.erase 40)) ed25519ScReduceShippedPart06 =
        rspPub ["%r14", "%r15"] scrCellsD := by decide +kernel
theorem scReduce_empty_part07 :
    check false (rspPub ["%r14", "%r15"] scrCellsD) ed25519ScReduceShippedPart07 = true ∧
      run (rspPub ["%r14", "%r15"] scrCellsD) ed25519ScReduceShippedPart07 =
        rspPub ["%r8"] scrCellsE := by decide +kernel
theorem scReduce_empty_part08 :
    check false (rspPub ["%r8"] scrCellsE) ed25519ScReduceShippedPart08 = true := by
  decide +kernel

theorem scReduce_check_strict : check true pub2 ed25519ScReduceShippedBlock = true := by
  unfold ed25519ScReduceShippedBlock
  simp only [List.append_assoc]
  exact check_append_of scReduce_strict_part01 <| check_append_of scReduce_strict_part02 <|
    check_append_of scReduce_strict_part03 <| check_append_of scReduce_strict_part04 <|
    check_append_of scReduce_strict_part05 <| check_append_of scReduce_strict_part06 <|
    check_append_of scReduce_strict_part07 scReduce_strict_part08

theorem scReduce_check_empty : check false PubSet.empty ed25519ScReduceShippedBlock = true := by
  unfold ed25519ScReduceShippedBlock
  simp only [List.append_assoc]
  exact check_append_of scReduce_empty_part01 <| check_append_of scReduce_empty_part02 <|
    check_append_of scReduce_empty_part03 <| check_append_of scReduce_empty_part04 <|
    check_append_of scReduce_empty_part05 <| check_append_of scReduce_empty_part06 <|
    check_append_of scReduce_empty_part07 scReduce_empty_part08

/-- `ed25519_sc_reduce`: the leakage trace is the same from any two states. -/
theorem ed25519ScReduce_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ ed25519ScReduceShippedBlock = blockLeak s₂ ed25519ScReduceShippedBlock :=
  check_empty_leak scReduce_check_empty s₁ s₂

/-- `ed25519_sc_reduce`: the address trace is determined by `%rdi`, `%rsi`, `%rsp`. -/
theorem ed25519ScReduce_addr (s₁ s₂ : JState 64) (hag : pub2.Agree s₁ s₂) :
    blockAddr s₁ ed25519ScReduceShippedBlock = blockAddr s₂ ed25519ScReduceShippedBlock :=
  check_addr scReduce_check_strict hag

end ScReduce

/-! ### `ed25519_sc_muladd`, part by part

As for `ed25519_sc_reduce`, with the entry set `pub4`. -/

/-- The `%rsp` offsets public after part 1 from the entry set. -/
def scmCellsA : List Int := [168, 160, 152, 144, 136, -16, -8, 224, 232]

/-- The `%rsp` offsets public after part 1 from the empty set. -/
def scmCellsB : List Int := [168, 160, 152, 144]

/-- The `%rsp` offsets public after parts 2 to 4 from the entry set. -/
def scmCellsC : List Int :=
  [104, 112, 120, 128, 40, 32, 24, 16, 8, 168, 160, 152, 144, 136, -16, -8, 224, 232]

/-- The `%rsp` offsets public after parts 2 to 4 from the empty set. -/
def scmCellsD : List Int := [104, 112, 120, 128, 40, 32, 24, 16, 8, 168, 160, 152, 144]

section ScMuladd
open Ed25519ScMuladdShipped

theorem scMuladd_strict_part01 :
    check true pub4 ed25519ScMuladdShippedPart01 = true ∧
      run pub4 ed25519ScMuladdShippedPart01 = rspPub ["%rsp"] scmCellsA := by decide +kernel
theorem scMuladd_strict_part02 :
    check true (rspPub ["%rsp"] scmCellsA) ed25519ScMuladdShippedPart02 = true ∧
      run (rspPub ["%rsp"] scmCellsA) ed25519ScMuladdShippedPart02 =
        rspPub ["%r14", "%r15", "%rsp"] scmCellsC := by decide +kernel
theorem scMuladd_strict_part03 :
    check true (rspPub ["%r14", "%r15", "%rsp"] scmCellsC) ed25519ScMuladdShippedPart03 = true ∧
      run (rspPub ["%r14", "%r15", "%rsp"] scmCellsC) ed25519ScMuladdShippedPart03 =
        rspPub ["%r14", "%r15", "%rsp"] scmCellsC := by decide +kernel
theorem scMuladd_strict_part04 :
    check true (rspPub ["%r14", "%r15", "%rsp"] scmCellsC) ed25519ScMuladdShippedPart04 = true ∧
      run (rspPub ["%r14", "%r15", "%rsp"] scmCellsC) ed25519ScMuladdShippedPart04 =
        rspPub ["%r14", "%r15", "%rsp"] scmCellsC := by decide +kernel
theorem scMuladd_strict_part05 :
    check true (rspPub ["%r14", "%r15", "%rsp"] scmCellsC) ed25519ScMuladdShippedPart05 = true ∧
      run (rspPub ["%r14", "%r15", "%rsp"] scmCellsC) ed25519ScMuladdShippedPart05 =
        rspPub ["%r14", "%r15", "%rsp"] scmCellsC := by decide +kernel
theorem scMuladd_strict_part06 :
    check true (rspPub ["%r14", "%r15", "%rsp"] scmCellsC) ed25519ScMuladdShippedPart06 = true ∧
      run (rspPub ["%r14", "%r15", "%rsp"] scmCellsC) ed25519ScMuladdShippedPart06 =
        rspPub ["%rbx", "%r14", "%r15", "%rsp"] (scmCellsC.erase 40) := by decide +kernel
theorem scMuladd_strict_part07 :
    check true (rspPub ["%rbx", "%r14", "%r15", "%rsp"] (scmCellsC.erase 40))
        ed25519ScMuladdShippedPart07 = true ∧
      run (rspPub ["%rbx", "%r14", "%r15", "%rsp"] (scmCellsC.erase 40))
          ed25519ScMuladdShippedPart07 =
        rspPub ["%r14", "%rsp"] ((scmCellsC.erase 40).erase 32) := by decide +kernel
theorem scMuladd_strict_part08 :
    check true (rspPub ["%r14", "%rsp"] ((scmCellsC.erase 40).erase 32))
        ed25519ScMuladdShippedPart08 = true ∧
      run (rspPub ["%r14", "%rsp"] ((scmCellsC.erase 40).erase 32))
          ed25519ScMuladdShippedPart08 =
        rspPub ["%r14", "%r15", "%rsp"] ((scmCellsC.erase 40).erase 32) := by decide +kernel
theorem scMuladd_strict_part09 :
    check true (rspPub ["%r14", "%r15", "%rsp"] ((scmCellsC.erase 40).erase 32))
      ed25519ScMuladdShippedPart09 = true := by decide +kernel

theorem scMuladd_empty_part01 :
    check false PubSet.empty ed25519ScMuladdShippedPart01 = true ∧
      run PubSet.empty ed25519ScMuladdShippedPart01 = rspPub [] scmCellsB := by decide +kernel
theorem scMuladd_empty_part02 :
    check false (rspPub [] scmCellsB) ed25519ScMuladdShippedPart02 = true ∧
      run (rspPub [] scmCellsB) ed25519ScMuladdShippedPart02 =
        rspPub ["%r14", "%r15"] scmCellsD := by decide +kernel
theorem scMuladd_empty_part03 :
    check false (rspPub ["%r14", "%r15"] scmCellsD) ed25519ScMuladdShippedPart03 = true ∧
      run (rspPub ["%r14", "%r15"] scmCellsD) ed25519ScMuladdShippedPart03 =
        rspPub ["%r14", "%r15"] scmCellsD := by decide +kernel
theorem scMuladd_empty_part04 :
    check false (rspPub ["%r14", "%r15"] scmCellsD) ed25519ScMuladdShippedPart04 = true ∧
      run (rspPub ["%r14", "%r15"] scmCellsD) ed25519ScMuladdShippedPart04 =
        rspPub ["%r14", "%r15"] scmCellsD := by decide +kernel
theorem scMuladd_empty_part05 :
    check false (rspPub ["%r14", "%r15"] scmCellsD) ed25519ScMuladdShippedPart05 = true ∧
      run (rspPub ["%r14", "%r15"] scmCellsD) ed25519ScMuladdShippedPart05 =
        rspPub ["%r14", "%r15"] scmCellsD := by decide +kernel
theorem scMuladd_empty_part06 :
    check false (rspPub ["%r14", "%r15"] scmCellsD) ed25519ScMuladdShippedPart06 = true ∧
      run (rspPub ["%r14", "%r15"] scmCellsD) ed25519ScMuladdShippedPart06 =
        rspPub ["%rbx", "%r14", "%r15"] (scmCellsD.erase 40) := by decide +kernel
theorem scMuladd_empty_part07 :
    check false (rspPub ["%rbx", "%r14", "%r15"] (scmCellsD.erase 40))
        ed25519ScMuladdShippedPart07 = true ∧
      run (rspPub ["%rbx", "%r14", "%r15"] (scmCellsD.erase 40)) ed25519ScMuladdShippedPart07 =
        rspPub ["%r14"] ((scmCellsD.erase 40).erase 32) := by decide +kernel
theorem scMuladd_empty_part08 :
    check false (rspPub ["%r14"] ((scmCellsD.erase 40).erase 32))
        ed25519ScMuladdShippedPart08 = true ∧
      run (rspPub ["%r14"] ((scmCellsD.erase 40).erase 32)) ed25519ScMuladdShippedPart08 =
        rspPub ["%r14", "%r15"] ((scmCellsD.erase 40).erase 32) := by decide +kernel
theorem scMuladd_empty_part09 :
    check false (rspPub ["%r14", "%r15"] ((scmCellsD.erase 40).erase 32))
      ed25519ScMuladdShippedPart09 = true := by decide +kernel

theorem scMuladd_check_strict : check true pub4 ed25519ScMuladdShippedBlock = true := by
  unfold ed25519ScMuladdShippedBlock
  simp only [List.append_assoc]
  exact check_append_of scMuladd_strict_part01 <| check_append_of scMuladd_strict_part02 <|
    check_append_of scMuladd_strict_part03 <| check_append_of scMuladd_strict_part04 <|
    check_append_of scMuladd_strict_part05 <| check_append_of scMuladd_strict_part06 <|
    check_append_of scMuladd_strict_part07 <| check_append_of scMuladd_strict_part08
    scMuladd_strict_part09

theorem scMuladd_check_empty : check false PubSet.empty ed25519ScMuladdShippedBlock = true := by
  unfold ed25519ScMuladdShippedBlock
  simp only [List.append_assoc]
  exact check_append_of scMuladd_empty_part01 <| check_append_of scMuladd_empty_part02 <|
    check_append_of scMuladd_empty_part03 <| check_append_of scMuladd_empty_part04 <|
    check_append_of scMuladd_empty_part05 <| check_append_of scMuladd_empty_part06 <|
    check_append_of scMuladd_empty_part07 <| check_append_of scMuladd_empty_part08
    scMuladd_empty_part09

/-- `ed25519_sc_muladd`: the leakage trace is the same from any two states. -/
theorem ed25519ScMuladd_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ ed25519ScMuladdShippedBlock = blockLeak s₂ ed25519ScMuladdShippedBlock :=
  check_empty_leak scMuladd_check_empty s₁ s₂

/-- `ed25519_sc_muladd`: the address trace is determined by its four pointer
    arguments and `%rsp`. -/
theorem ed25519ScMuladd_addr (s₁ s₂ : JState 64) (hag : pub4.Agree s₁ s₂) :
    blockAddr s₁ ed25519ScMuladdShippedBlock = blockAddr s₂ ed25519ScMuladdShippedBlock :=
  check_addr scMuladd_check_strict hag

end ScMuladd

/-! ## 7. Kernels with calls

A `List CallSeg` runs each segment body and then its call. The effect of a call
is a parameter `C : CallModel`: for a callee symbol and the state at the call, the
callee's leakage trace, its address trace, and the state after it returns. The
trace of the caller interleaves the leakage of each body with a `call f` event and
the callee's trace.

The analysis crosses a call as follows. At the call, the callee's public set
`pre f` must be contained in the caller's current public set. After the call only
two kinds of location stay public: registers in `saved` (the SysV callee-saved
registers), and cells in `keep` (the caller's own stack slots that the callee does
not write). Every other register and cell is treated as arbitrary: the callee may
change it, and nothing is assumed about the value it leaves. The hypotheses on `C`
are exactly these: `CalleeCT` (the callee's traces are determined by `pre f`) and
`CalleeFrame` (the callee preserves `saved` and `keep`). The leakage theorems use
`saved = keep = []`, so their only hypothesis on a callee is that its leakage
trace is a function of nothing. -/

/-- An event of the leakage trace of a function with calls: a machine event, or a
    call of a named symbol. -/
inductive CallEvent where
  /-- A leakage event of an instruction of the function. -/
  | ev (e : MLeak)
  /-- The `call` of `callee`. -/
  | call (callee : String)
  deriving DecidableEq, Repr

/-- The observable result of a call: the callee's leakage and address traces and
    the state it returns. -/
structure CallOut where
  /-- The leakage trace of the callee. -/
  leak : List CallEvent
  /-- The address trace of the callee. -/
  addr : List (BitVec 64)
  /-- The state after the callee returns. -/
  post : JState 64

/-- A model of the called functions, by symbol and state at the call. -/
abbrev CallModel := String → JState 64 → CallOut

/-- The leakage trace of a list of segments under the call model `C`. -/
def segsLeak (C : CallModel) : JState 64 → List CallSeg → List CallEvent
  | _, [] => []
  | s, g :: gs =>
    match g.callee with
    | none => (blockLeak s g.body).map .ev ++ segsLeak C (runBlock s g.body) gs
    | some f => (blockLeak s g.body).map .ev ++ (.call f :: ((C f (runBlock s g.body)).leak ++
        segsLeak C (C f (runBlock s g.body)).post gs))

/-- The address trace of a list of segments under the call model `C`. -/
def segsAddr (C : CallModel) : JState 64 → List CallSeg → List (BitVec 64)
  | _, [] => []
  | s, g :: gs =>
    match g.callee with
    | none => blockAddr s g.body ++ segsAddr C (runBlock s g.body) gs
    | some f => blockAddr s g.body ++ ((C f (runBlock s g.body)).addr ++
        segsAddr C (C f (runBlock s g.body)).post gs)

/-- The leakage trace of callee `f` is determined by the locations of `pre`. -/
def CalleeCT (C : CallModel) (f : String) (pre : PubSet) : Prop :=
  ∀ s₁ s₂ : JState 64, pre.Agree s₁ s₂ → (C f s₁).leak = (C f s₂).leak

/-- The address trace of callee `f` is determined by the locations of `pre`. -/
def CalleeAddrCT (C : CallModel) (f : String) (pre : PubSet) : Prop :=
  ∀ s₁ s₂ : JState 64, pre.Agree s₁ s₂ → (C f s₁).addr = (C f s₂).addr

/-- Every callee preserves the registers `saved` and the cells `keep`. -/
def CalleeFrame (C : CallModel) (saved : List String) (keep : List (String × Int)) : Prop :=
  ∀ f s, (∀ r ∈ saved, (C f s).post.get r = s.get r) ∧
    (∀ c ∈ keep, (C f s).post.mem c.1 c.2 = s.mem c.1 c.2)

/-- The frame condition with nothing preserved holds of every model. -/
theorem calleeFrame_nil (C : CallModel) : CalleeFrame C [] [] :=
  fun _ _ => ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

/-- The public set after a call: the public registers in `saved` and the public
    cells in `keep`. -/
def afterCall (saved : List String) (keep : List (String × Int)) (Q : PubSet) : PubSet :=
  ⟨Q.regs.filter saved.contains, Q.cells.filter keep.contains⟩

/-- Under `CalleeFrame`, the states returned by a callee from two states agreeing
    on `Q` agree on `afterCall saved keep Q`. -/
theorem afterCall_sound{C : CallModel} {saved : List String} {keep : List (String × Int)}
    (hF : CalleeFrame C saved keep) (f : String) {Q : PubSet} {s₁ s₂ : JState 64}
    (hag : Q.Agree s₁ s₂) : (afterCall saved keep Q).Agree (C f s₁).post (C f s₂).post := by
  refine ⟨fun r hr => ?_, fun c hc => ?_⟩
  · simp only [afterCall, List.mem_filter, List.contains_iff_mem] at hr
    rw [(hF f s₁).1 r hr.2, (hF f s₂).1 r hr.2]
    exact hag.1 r hr.1
  · simp only [afterCall, List.mem_filter, List.contains_iff_mem] at hc
    rw [(hF f s₁).2 c hc.2, (hF f s₂).2 c hc.2]
    exact hag.2 c hc.1

/-- The call of `f` is allowed with public set `Q`: `f` has a public set, and it is
    contained in `Q`. -/
def preOk (pre : String → Option PubSet) (f : String) (Q : PubSet) : Bool :=
  match pre f with
  | some A => A.le Q
  | none => false

/-- The checker for a list of segments. -/
def checkSegs (strict : Bool) (pre : String → Option PubSet) (saved : List String)
    (keep : List (String × Int)) : PubSet → List CallSeg → Bool
  | _, [] => true
  | P, g :: gs => check strict P g.body &&
      match g.callee with
      | none => checkSegs strict pre saved keep (run P g.body) gs
      | some f => preOk pre f (run P g.body) &&
          checkSegs strict pre saved keep (afterCall saved keep (run P g.body)) gs

/-- **Soundness of the segment checker.** Under the callee hypotheses, two states
    agreeing on `P` have the same leakage trace, and with `strict = true` the same
    address trace. -/
theorem checkSegs_sound (strict : Bool) (pre : String → Option PubSet) (saved : List String)
    (keep : List (String × Int)) (C : CallModel) (hF : CalleeFrame C saved keep)
    (hL : ∀ f A, pre f = some A → CalleeCT C f A)
    (hA : strict = true → ∀ f A, pre f = some A → CalleeAddrCT C f A) (segs : List CallSeg) :
    ∀ P, checkSegs strict pre saved keep P segs = true → ∀ {s₁ s₂ : JState 64},
      P.Agree s₁ s₂ → segsLeak C s₁ segs = segsLeak C s₂ segs ∧
        (strict = true → segsAddr C s₁ segs = segsAddr C s₂ segs) := by
  induction segs with
  | nil => intro _ _ _ _ _; exact ⟨rfl, fun _ => rfl⟩
  | cons g gs ih =>
    intro P hc s₁ s₂ hag
    rcases g with ⟨body, callee⟩
    simp only [checkSegs, Bool.and_eq_true] at hc
    obtain ⟨hb, hrest⟩ := hc
    obtain ⟨hbl, hba⟩ := check_sound strict body P hb hag
    have hrun := run_sound body P hag
    cases callee with
    | none =>
      obtain ⟨hl, ha⟩ := ih _ hrest hrun
      exact ⟨by simp only [segsLeak, hbl, hl], fun hs => by simp only [segsAddr, hba hs, ha hs]⟩
    | some f =>
      simp only [Bool.and_eq_true] at hrest
      obtain ⟨hpre, hrest⟩ := hrest
      unfold preOk at hpre
      split at hpre
      · rename_i A hA'
        have hagA := PubSet.agree_of_le hpre hrun
        obtain ⟨hl, ha⟩ := ih _ hrest (afterCall_sound hF f hrun)
        refine ⟨?_, fun hs => ?_⟩
        · simp only [segsLeak, hbl, hL f A hA' _ _ hagA, hl]
        · simp only [segsAddr, hba hs, hA hs f A hA' _ _ hagA, ha hs]
      · simp at hpre

/-- A callee whose leakage trace is that of a block with a state-independent
    leakage trace satisfies `CalleeCT` for every public set. -/
theorem calleeCT_of_block {C : CallModel} {f : String} {b : List (JInstr 64)}
    (hC : ∀ s, (C f s).leak = (blockLeak s b).map .ev)
    (hb : ∀ s₁ s₂ : JState 64, blockLeak s₁ b = blockLeak s₂ b) (pre : PubSet) :
    CalleeCT C f pre :=
  fun s₁ s₂ _ => by rw [hC, hC, hb s₁ s₂]

/-- A callee whose address trace is that of a block with a `pre`-determined
    address trace satisfies `CalleeAddrCT` for `pre`. -/
theorem calleeAddrCT_of_block {C : CallModel} {f : String} {b : List (JInstr 64)}
    {pre : PubSet} (hC : ∀ s, (C f s).addr = blockAddr s b)
    (hb : ∀ s₁ s₂ : JState 64, pre.Agree s₁ s₂ → blockAddr s₁ b = blockAddr s₂ b) :
    CalleeAddrCT C f pre :=
  fun s₁ s₂ h => by rw [hC, hC, hb s₁ s₂ h]

/-! ### The shipped callees -/

/-- The symbol of `fe25519_mul`. -/
def mulSym : String := "fe25519_mul_x86_from_lean"
/-- The symbol of `fe25519_sqr`. -/
def sqrSym : String := "fe25519_sqr_x86_from_lean"
/-- The symbol of `fe25519_add`. -/
def addSym : String := "fe25519_add_x86_from_lean"
/-- The symbol of `fe25519_sub`. -/
def subSym : String := "fe25519_sub_x86_from_lean"
/-- The symbol of `ed25519_join16`. -/
def join16Sym : String := "ed25519_join16_x86_from_lean"
/-- The symbol of `ed25519_pack_sign`. -/
def packSignSym : String := "ed25519_pack_sign_x86_from_lean"
/-- The symbol of `ed25519_invert`. -/
def invertSym : String := "ed25519_invert_x86_from_lean"

/-- A call model whose call-free shipped callees have the traces of their imported
    blocks. The post-state is unconstrained. -/
structure LeafModel (C : CallModel) : Prop where
  mul : ∀ s, (C mulSym s).leak = (blockLeak s Fe25519MulShipped.fe25519MulShippedBlock).map .ev ∧
    (C mulSym s).addr = blockAddr s Fe25519MulShipped.fe25519MulShippedBlock
  sqr : ∀ s, (C sqrSym s).leak = (blockLeak s Fe25519SqrShipped.fe25519SqrShippedBlock).map .ev ∧
    (C sqrSym s).addr = blockAddr s Fe25519SqrShipped.fe25519SqrShippedBlock
  add : ∀ s, (C addSym s).leak = (blockLeak s Fe25519AddShipped.fe25519AddShippedBlock).map .ev ∧
    (C addSym s).addr = blockAddr s Fe25519AddShipped.fe25519AddShippedBlock
  sub : ∀ s, (C subSym s).leak = (blockLeak s Fe25519SubShipped.fe25519SubShippedBlock).map .ev ∧
    (C subSym s).addr = blockAddr s Fe25519SubShipped.fe25519SubShippedBlock
  join16 : ∀ s, (C join16Sym s).leak =
      (blockLeak s Ed25519Join16Shipped.ed25519Join16ShippedBlock).map .ev ∧
    (C join16Sym s).addr = blockAddr s Ed25519Join16Shipped.ed25519Join16ShippedBlock
  packSign : ∀ s, (C packSignSym s).leak =
      (blockLeak s Ed25519PackSignShipped.ed25519PackSignShippedBlock).map .ev ∧
    (C packSignSym s).addr = blockAddr s Ed25519PackSignShipped.ed25519PackSignShippedBlock

/-- A call model that is a `LeafModel` and whose `ed25519_invert` has the traces of
    its imported segments under the same model. -/
structure ShippedModel (C : CallModel) : Prop extends LeafModel C where
  invert : ∀ s, (C invertSym s).leak =
      segsLeak C s Ed25519InvertShipped.ed25519InvertShippedBlock ∧
    (C invertSym s).addr = segsAddr C s Ed25519InvertShipped.ed25519InvertShippedBlock

/-- The call-free shipped callees, each with the empty public set. -/
def leafLeakPre (f : String) : Option PubSet :=
  if f = mulSym ∨ f = sqrSym ∨ f = addSym ∨ f = subSym ∨ f = join16Sym ∨ f = packSignSym then
    some PubSet.empty else none

/-- The call-free shipped callees, each with the public set of its arguments. -/
def leafAddrPre (f : String) : Option PubSet :=
  if f = mulSym ∨ f = addSym ∨ f = subSym ∨ f = packSignSym then some pub3
  else if f = sqrSym then some pub2
  else if f = join16Sym then some pub5
  else none

/-- In a `LeafModel`, each call-free shipped callee satisfies `CalleeCT` for every
    public set. -/
theorem leafModel_calleeCT{C : CallModel} (hC : LeafModel C) (f : String) (A : PubSet)
    (hf : f = mulSym ∨ f = sqrSym ∨ f = addSym ∨ f = subSym ∨ f = join16Sym ∨
      f = packSignSym) : CalleeCT C f A := by
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact calleeCT_of_block (fun s => (hC.mul s).1) fe25519Mul_constant_time A
  · exact calleeCT_of_block (fun s => (hC.sqr s).1) fe25519Sqr_constant_time A
  · exact calleeCT_of_block (fun s => (hC.add s).1) fe25519Add_constant_time A
  · exact calleeCT_of_block (fun s => (hC.sub s).1) fe25519Sub_constant_time A
  · exact calleeCT_of_block (fun s => (hC.join16 s).1) ed25519Join16_constant_time A
  · exact calleeCT_of_block (fun s => (hC.packSign s).1) ed25519PackSign_constant_time A

/-- The callee hypothesis of `checkSegs_sound` for `leafLeakPre`. -/
theorem leafLeakPre_sound{C : CallModel} (hC : LeafModel C) :
    ∀ f A, leafLeakPre f = some A → CalleeCT C f A := by
  intro f A h
  unfold leafLeakPre at h
  split at h
  · exact leafModel_calleeCT hC f A (by assumption)
  · exact absurd h (by simp)

/-- The callee hypotheses of `checkSegs_sound` for `leafAddrPre`. -/
theorem leafAddrPre_sound{C : CallModel} (hC : LeafModel C) :
    ∀ f A, leafAddrPre f = some A → CalleeCT C f A ∧ CalleeAddrCT C f A := by
  intro f A h
  unfold leafAddrPre at h
  split at h
  · rename_i hf
    cases h
    refine ⟨leafModel_calleeCT hC f _ (by rcases hf with h | h | h | h <;> simp [h]), ?_⟩
    rcases hf with rfl | rfl | rfl | rfl
    · exact calleeAddrCT_of_block (fun s => (hC.mul s).2) fe25519Mul_addr
    · exact calleeAddrCT_of_block (fun s => (hC.add s).2) fe25519Add_addr
    · exact calleeAddrCT_of_block (fun s => (hC.sub s).2) fe25519Sub_addr
    · exact calleeAddrCT_of_block (fun s => (hC.packSign s).2) ed25519PackSign_addr
  split at h
  · rename_i hf
    cases h
    subst hf
    exact ⟨leafModel_calleeCT hC _ _ (by simp),
      calleeAddrCT_of_block (fun s => (hC.sqr s).2) fe25519Sqr_addr⟩
  split at h
  · rename_i hf
    cases h
    subst hf
    exact ⟨leafModel_calleeCT hC _ _ (by simp),
      calleeAddrCT_of_block (fun s => (hC.join16 s).2) ed25519Join16_addr⟩
  · exact absurd h (by simp)

/-- The SysV callee-saved registers. -/
def sysvSaved : List String := ["%rbx", "%rbp", "%r12", "%r13", "%r14", "%r15", "%rsp"]

/-- The `%rsp` cells at the offsets `os`. -/
def rspCells (os : List Int) : List (String × Int) := os.map (("%rsp", ·))

/-! ### `ed25519_madd` -/

section Madd
open Ed25519MaddShipped

/-- `ed25519_madd`: for any model of its callees in which each call-free shipped
    callee has the leakage trace of its imported block, the leakage trace is the
    same from any two states. -/
theorem ed25519Madd_constant_time (C : CallModel) (hC : LeafModel C) (s₁ s₂ : JState 64) :
    segsLeak C s₁ ed25519MaddShippedBlock = segsLeak C s₂ ed25519MaddShippedBlock :=
  (checkSegs_sound false leafLeakPre [] [] C (calleeFrame_nil C) (leafLeakPre_sound hC)
    (fun h => absurd h Bool.false_ne_true) _ PubSet.empty (by decide +kernel)
    (PubSet.agree_empty s₁ s₂)).1

/-- `ed25519_madd`: if each call-free shipped callee has the traces of its imported
    block, and every callee preserves the SysV callee-saved registers and the two
    argument slots at `576(%rsp)` and `584(%rsp)`, the address trace is determined by
    `%rdi`, `%rsi`, `%rsp`. -/
theorem ed25519Madd_addr (C : CallModel) (hC : LeafModel C)
    (hF : CalleeFrame C sysvSaved (rspCells [576, 584])) (s₁ s₂ : JState 64)
    (hag : pub2.Agree s₁ s₂) :
    segsAddr C s₁ ed25519MaddShippedBlock = segsAddr C s₂ ed25519MaddShippedBlock :=
  (checkSegs_sound true leafAddrPre sysvSaved (rspCells [576, 584]) C hF
    (fun f A h => (leafAddrPre_sound hC f A h).1)
    (fun _ f A h => (leafAddrPre_sound hC f A h).2) _ pub2 (by decide +kernel) hag).2 rfl

end Madd

/-! ### `ed25519_invert` -/

section Invert
open Ed25519InvertShipped

/-- `ed25519_invert`: for any model of its callees in which `fe25519_mul` and
    `fe25519_sqr` have the leakage traces of their imported blocks, the leakage
    trace is the same from any two states. -/
theorem ed25519Invert_constant_time (C : CallModel) (hC : LeafModel C) (s₁ s₂ : JState 64) :
    segsLeak C s₁ ed25519InvertShippedBlock = segsLeak C s₂ ed25519InvertShippedBlock :=
  (checkSegs_sound false leafLeakPre [] [] C (calleeFrame_nil C) (leafLeakPre_sound hC)
    (fun h => absurd h Bool.false_ne_true) _ PubSet.empty (by decide +kernel)
    (PubSet.agree_empty s₁ s₂)).1

/-- `ed25519_invert`: if its callees have the traces of their imported blocks and
    every callee preserves the SysV callee-saved registers and the argument slot at
    `128(%rsp)`, the address trace is determined by `%rdi`, `%rsi`, `%rsp`. -/
theorem ed25519Invert_addr (C : CallModel) (hC : LeafModel C)
    (hF : CalleeFrame C sysvSaved (rspCells [128])) (s₁ s₂ : JState 64)
    (hag : pub2.Agree s₁ s₂) :
    segsAddr C s₁ ed25519InvertShippedBlock = segsAddr C s₂ ed25519InvertShippedBlock :=
  (checkSegs_sound true leafAddrPre sysvSaved (rspCells [128]) C hF
    (fun f A h => (leafAddrPre_sound hC f A h).1)
    (fun _ f A h => (leafAddrPre_sound hC f A h).2) _ pub2 (by decide +kernel) hag).2 rfl

end Invert

/-! ### `fe25519_pow22523` -/

section Pow22523
open Fe25519Pow22523Shipped

/-- `fe25519_pow22523`: for any model of its callees in which `fe25519_mul` and
    `fe25519_sqr` have the leakage traces of their imported blocks, the leakage
    trace is the same from any two states. -/
theorem fe25519Pow22523_constant_time (C : CallModel) (hC : LeafModel C) (s₁ s₂ : JState 64) :
    segsLeak C s₁ fe25519Pow22523ShippedBlock = segsLeak C s₂ fe25519Pow22523ShippedBlock :=
  (checkSegs_sound false leafLeakPre [] [] C (calleeFrame_nil C) (leafLeakPre_sound hC)
    (fun h => absurd h Bool.false_ne_true) _ PubSet.empty (by decide +kernel)
    (PubSet.agree_empty s₁ s₂)).1

/-- `fe25519_pow22523`: if its callees have the traces of their imported blocks and
    every callee preserves the SysV callee-saved registers and the argument slot at
    `128(%rsp)`, the address trace is determined by `%rdi`, `%rsi`, `%rsp`. -/
theorem fe25519Pow22523_addr (C : CallModel) (hC : LeafModel C)
    (hF : CalleeFrame C sysvSaved (rspCells [128])) (s₁ s₂ : JState 64)
    (hag : pub2.Agree s₁ s₂) :
    segsAddr C s₁ fe25519Pow22523ShippedBlock = segsAddr C s₂ fe25519Pow22523ShippedBlock :=
  (checkSegs_sound true leafAddrPre sysvSaved (rspCells [128]) C hF
    (fun f A h => (leafAddrPre_sound hC f A h).1)
    (fun _ f A h => (leafAddrPre_sound hC f A h).2) _ pub2 (by decide +kernel) hag).2 rfl

end Pow22523

/-! ### `ed25519_compress` -/

/-- The callees of `ed25519_compress`, each with the empty public set. -/
def compressLeakPre (f : String) : Option PubSet :=
  if f = invertSym then some PubSet.empty else leafLeakPre f

/-- The callees of `ed25519_compress`, each with the public set of its arguments. -/
def compressAddrPre (f : String) : Option PubSet :=
  if f = invertSym then some pub2 else leafAddrPre f

/-- In a `ShippedModel`, `ed25519_invert` satisfies `CalleeCT` for every public set. -/
theorem invert_calleeCT{C : CallModel} (hC : ShippedModel C) (A : PubSet) :
    CalleeCT C invertSym A := fun s₁ s₂ _ => by
  rw [(hC.invert s₁).1, (hC.invert s₂).1]
  exact ed25519Invert_constant_time C hC.toLeafModel s₁ s₂

section Compress
open Ed25519CompressShipped

/-- `ed25519_compress`: for any model of its callees in which the call-free shipped
    callees have the leakage traces of their imported blocks and `ed25519_invert`
    that of its imported segments, the leakage trace is the same from any two
    states. -/
theorem ed25519Compress_constant_time (C : CallModel) (hC : ShippedModel C)
    (s₁ s₂ : JState 64) :
    segsLeak C s₁ ed25519CompressShippedBlock = segsLeak C s₂ ed25519CompressShippedBlock := by
  refine (checkSegs_sound false compressLeakPre [] [] C (calleeFrame_nil C) ?_
    (fun h => absurd h Bool.false_ne_true) _ PubSet.empty (by decide +kernel)
    (PubSet.agree_empty s₁ s₂)).1
  intro f A h
  unfold compressLeakPre at h
  split at h
  · rename_i hf
    subst hf
    exact invert_calleeCT hC A
  · exact leafLeakPre_sound hC.toLeafModel f A h

/-- `ed25519_compress`: if its callees have the traces of their imported blocks and
    segments, every callee preserves the SysV callee-saved registers, and the
    callees preserve the argument slot at `96(%rsp)` (for the calls of
    `ed25519_compress`) and at `128(%rsp)` (for the calls of `ed25519_invert`), the
    address trace is determined by `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%rsp`. -/
theorem ed25519Compress_addr (C : CallModel) (hC : ShippedModel C)
    (hF : CalleeFrame C sysvSaved (rspCells [96]))
    (hFi : CalleeFrame C sysvSaved (rspCells [128])) (s₁ s₂ : JState 64)
    (hag : pub4.Agree s₁ s₂) :
    segsAddr C s₁ ed25519CompressShippedBlock = segsAddr C s₂ ed25519CompressShippedBlock := by
  have hsound : ∀ f A, compressAddrPre f = some A → CalleeCT C f A ∧ CalleeAddrCT C f A := by
    intro f A h
    unfold compressAddrPre at h
    split at h
    · rename_i hf
      subst hf
      cases h
      refine ⟨invert_calleeCT hC _, fun t₁ t₂ ht => ?_⟩
      rw [(hC.invert t₁).2, (hC.invert t₂).2]
      exact ed25519Invert_addr C hC.toLeafModel hFi t₁ t₂ ht
    · exact leafAddrPre_sound hC.toLeafModel f A h
  exact (checkSegs_sound true compressAddrPre sysvSaved (rspCells [96]) C hF
    (fun f A h => (hsound f A h).1) (fun _ f A h => (hsound f A h).2) _ pub4
    (by decide +kernel) hag).2 rfl

end Compress

/-! ### A model satisfying the hypotheses

`shippedCalls` runs no callee: each call-free shipped callee returns the traces of
its imported block, `ed25519_invert` those of its imported segments, and every
callee returns the state it was called in. It is a `ShippedModel` and satisfies
every `CalleeFrame`, so the hypotheses of §7 are jointly satisfiable. -/

/-- Two call models that agree on the callees of `segs` give `segs` the same
    traces. -/
theorem segs_congr {C C' : CallModel} (segs : List CallSeg) :
    (∀ f ∈ CallSeg.callees segs, C f = C' f) → ∀ s,
      segsLeak C s segs = segsLeak C' s segs ∧ segsAddr C s segs = segsAddr C' s segs := by
  induction segs with
  | nil => intro _ _; exact ⟨rfl, rfl⟩
  | cons g gs ih =>
    intro h s
    rcases g with ⟨body, callee⟩
    cases callee with
    | none =>
      have h' : ∀ f ∈ CallSeg.callees gs, C f = C' f := fun f hf =>
        h f (by simpa [CallSeg.callees] using hf)
      obtain ⟨hl, ha⟩ := ih h' (runBlock s body)
      exact ⟨by simp only [segsLeak, hl], by simp only [segsAddr, ha]⟩
    | some f =>
      have hf : C f = C' f := h f (by simp [CallSeg.callees])
      have h' : ∀ f ∈ CallSeg.callees gs, C f = C' f := fun f' hf' =>
        h f' (by simp [CallSeg.callees] at hf' ⊢; exact Or.inr hf')
      simp only [segsLeak, segsAddr, hf]
      obtain ⟨hl, ha⟩ := ih h' (C' f (runBlock s body)).post
      exact ⟨by rw [hl], by rw [ha]⟩

/-- The outcome of a call-free callee with block `b` that returns its entry state. -/
def leafOut (b : List (JInstr 64)) (s : JState 64) : CallOut :=
  ⟨(blockLeak s b).map .ev, blockAddr s b, s⟩

/-- The call-free shipped callees, each returning its entry state. -/
def leafCalls : CallModel := fun f s =>
  if f = mulSym then leafOut Fe25519MulShipped.fe25519MulShippedBlock s
  else if f = sqrSym then leafOut Fe25519SqrShipped.fe25519SqrShippedBlock s
  else if f = addSym then leafOut Fe25519AddShipped.fe25519AddShippedBlock s
  else if f = subSym then leafOut Fe25519SubShipped.fe25519SubShippedBlock s
  else if f = join16Sym then leafOut Ed25519Join16Shipped.ed25519Join16ShippedBlock s
  else if f = packSignSym then leafOut Ed25519PackSignShipped.ed25519PackSignShippedBlock s
  else ⟨[], [], s⟩

/-- `leafCalls` with `ed25519_invert` added. -/
def shippedCalls : CallModel := fun f s =>
  if f = invertSym then
    ⟨segsLeak leafCalls s Ed25519InvertShipped.ed25519InvertShippedBlock,
      segsAddr leafCalls s Ed25519InvertShipped.ed25519InvertShippedBlock, s⟩
  else leafCalls f s

/-- `ed25519_invert` does not call itself. -/
theorem invertSym_not_mem_callees :
    invertSym ∉ CallSeg.callees Ed25519InvertShipped.ed25519InvertShippedBlock := by
  decide +kernel

/-- `shippedCalls` is a `ShippedModel`. -/
theorem shippedCalls_model : ShippedModel shippedCalls where
  mul s := by
    simp only [shippedCalls, leafCalls, leafOut, ite_eq_right (show mulSym ≠ invertSym by decide)]
    exact ⟨rfl, rfl⟩
  sqr s := by
    simp only [shippedCalls, leafCalls, leafOut, ite_eq_right (show sqrSym ≠ invertSym by decide),
      ite_eq_right (show sqrSym ≠ mulSym by decide)]
    exact ⟨rfl, rfl⟩
  add s := by
    simp only [shippedCalls, leafCalls, leafOut, ite_eq_right (show addSym ≠ invertSym by decide),
      ite_eq_right (show addSym ≠ mulSym by decide), ite_eq_right (show addSym ≠ sqrSym by decide)]
    exact ⟨rfl, rfl⟩
  sub s := by
    simp only [shippedCalls, leafCalls, leafOut, ite_eq_right (show subSym ≠ invertSym by decide),
      ite_eq_right (show subSym ≠ mulSym by decide), ite_eq_right (show subSym ≠ sqrSym by decide),
      ite_eq_right (show subSym ≠ addSym by decide)]
    exact ⟨rfl, rfl⟩
  join16 s := by
    simp only [shippedCalls, leafCalls, leafOut, ite_eq_right (show join16Sym ≠ invertSym by decide),
      ite_eq_right (show join16Sym ≠ mulSym by decide), ite_eq_right (show join16Sym ≠ sqrSym by decide),
      ite_eq_right (show join16Sym ≠ addSym by decide), ite_eq_right (show join16Sym ≠ subSym by decide)]
    exact ⟨rfl, rfl⟩
  packSign s := by
    simp only [shippedCalls, leafCalls, leafOut,
      ite_eq_right (show packSignSym ≠ invertSym by decide),
      ite_eq_right (show packSignSym ≠ mulSym by decide), ite_eq_right (show packSignSym ≠ sqrSym by decide),
      ite_eq_right (show packSignSym ≠ addSym by decide), ite_eq_right (show packSignSym ≠ subSym by decide),
      ite_eq_right (show packSignSym ≠ join16Sym by decide)]
    exact ⟨rfl, rfl⟩
  invert s := by
    have h := segs_congr (C := shippedCalls) (C' := leafCalls)
      Ed25519InvertShipped.ed25519InvertShippedBlock (fun f hf => by
        funext t
        have : f ≠ invertSym := fun e => invertSym_not_mem_callees (e ▸ hf)
        simp [shippedCalls, this]) s
    simp only [shippedCalls]
    exact ⟨h.1.symm, h.2.symm⟩

/-- `shippedCalls` satisfies every frame condition. -/
theorem shippedCalls_frame (saved : List String) (keep : List (String × Int)) :
    CalleeFrame shippedCalls saved keep := by
  intro f s
  have hpost : (shippedCalls f s).post = s := by
    unfold shippedCalls leafCalls leafOut
    repeat' split
    all_goals rfl
  rw [hpost]
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## 8. Summary -/

/-- **The shipped kernels are constant time.** The leakage trace of each call-free
    kernel is the same from any two states; the leakage trace of each kernel with
    calls is the same from any two states for every call model in which the
    shipped callees have the traces of their imported code. -/
theorem shipped_kernels_constant_time :
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Fe25519MulShipped.fe25519MulShippedBlock =
      blockLeak s₂ Fe25519MulShipped.fe25519MulShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Fe25519SqrShipped.fe25519SqrShippedBlock =
      blockLeak s₂ Fe25519SqrShipped.fe25519SqrShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Fe25519AddShipped.fe25519AddShippedBlock =
      blockLeak s₂ Fe25519AddShipped.fe25519AddShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Fe25519SubShipped.fe25519SubShippedBlock =
      blockLeak s₂ Fe25519SubShipped.fe25519SubShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Ed25519CombSelectShipped.ed25519CombSelectShippedBlock =
      blockLeak s₂ Ed25519CombSelectShipped.ed25519CombSelectShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Ed25519Join16Shipped.ed25519Join16ShippedBlock =
      blockLeak s₂ Ed25519Join16Shipped.ed25519Join16ShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Ed25519PackSignShipped.ed25519PackSignShippedBlock =
      blockLeak s₂ Ed25519PackSignShipped.ed25519PackSignShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Ed25519ScReduceShipped.ed25519ScReduceShippedBlock =
      blockLeak s₂ Ed25519ScReduceShipped.ed25519ScReduceShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Ed25519ScMuladdShipped.ed25519ScMuladdShippedBlock =
      blockLeak s₂ Ed25519ScMuladdShipped.ed25519ScMuladdShippedBlock) ∧
    (∀ C, LeafModel C → ∀ s₁ s₂, segsLeak C s₁ Ed25519MaddShipped.ed25519MaddShippedBlock =
      segsLeak C s₂ Ed25519MaddShipped.ed25519MaddShippedBlock) ∧
    (∀ C, LeafModel C → ∀ s₁ s₂, segsLeak C s₁ Ed25519InvertShipped.ed25519InvertShippedBlock =
      segsLeak C s₂ Ed25519InvertShipped.ed25519InvertShippedBlock) ∧
    (∀ C, LeafModel C → ∀ s₁ s₂,
      segsLeak C s₁ Fe25519Pow22523Shipped.fe25519Pow22523ShippedBlock =
        segsLeak C s₂ Fe25519Pow22523Shipped.fe25519Pow22523ShippedBlock) ∧
    (∀ C, ShippedModel C → ∀ s₁ s₂,
      segsLeak C s₁ Ed25519CompressShipped.ed25519CompressShippedBlock =
        segsLeak C s₂ Ed25519CompressShipped.ed25519CompressShippedBlock) :=
  ⟨fe25519Mul_constant_time, fe25519Sqr_constant_time, fe25519Add_constant_time,
    fe25519Sub_constant_time, ed25519CombSelect_constant_time, ed25519Join16_constant_time,
    ed25519PackSign_constant_time, ed25519ScReduce_constant_time,
    ed25519ScMuladd_constant_time, ed25519Madd_constant_time, ed25519Invert_constant_time,
    fe25519Pow22523_constant_time, ed25519Compress_constant_time⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT

