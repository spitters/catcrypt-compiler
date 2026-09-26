/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.RangeDomain
public import Batteries.Data.BitVec
public import Std.Data.HashMap

/-!
# A machine model of the owned `%zmm` / `%ymm` text and its symbolic execution

The instruction forms `VpackZmmLinearRender.renderZmmLinearBinds` prints, as a machine
over 32 vector registers of 512 bits, `%eax`, the mask registers `%k0..7`, an input
region read at `%rsi`, a data table read at `%rip`, an output region written at
`%rdi` and a stack frame below `%rsp`, allocated by `subq $n, %rsp` and released by
`addq $n, %rsp`, holding spilled registers. A `%ymm` form (`Mode.ymm`) reads the low 256
bits of each register and each
write keeps the low 256 bits and zeroes the upper 256 bits (`wr`). Every lane-wise
instruction is defined through the lane read `lane` and the lane assembly `ofLanes`.

The memory model: the input region is a function from byte offsets to the 64 bytes
there, a store appends its offset and value to a log, and the output region at an
offset is the newest store there; this agrees with a byte memory when the store offsets
are multiples of the store width (checked by the validator) and the regions do not
overlap. The stack holds, at each byte offset from the current `%rsp`, the register value
last stored there, and a load of mode `m` reads its active bits (`wr`); moving `%rsp`
by `n` shifts these offsets by `n`. This agrees with a byte memory when the stack offsets
are multiples of the store width and lie inside the allocated frame (checked by the
validator, `ZmmTextValidate.frameOK`). The epilogue `vzeroupper; ret` touches no memory
and is not modelled.

A symbolic state holds a `Term` per register and per stack slot, the slots keyed by their
offset from `%rsp` at entry; `srun` runs a program on terms, and a
normaliser `norm` may replace a term by one of equal value. `srun_sound`: when the
normaliser preserves values and every input offset holds the value its name denotes,
a symbolic run describes the machine run.

## Main definitions

* `Mode`, `lane`, `ofLanes`, `wr`: the register forms and lanes.
* `LOp`, `semLW`, `semShImm`, `semDup`, `semMerge`: the lane-wise instruction semantics.
* `Instr`, `MState`, `step`, `run`, `MState.outAt`: the machine.
* `Term`, `Term.eval`, `SState`, `sstep`, `srun`, `Rel`: the symbolic execution.

## Main results

* `wr_eq_of_lanes`: two writes are equal when their active lanes are.
* `lane32_even`, `lane32_odd`, `hi_mul_setWidth`, `lo_mul_setWidth`: the dword halves
  of a `vpmuludq` product.
* `sstep_sound`, `srun_sound`: a symbolic run describes the machine run.
* `outAt_rel`: the stored values of the two runs agree.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp mulHiW)
open CatCrypt.Crypto.SecureCompilation.RangeDomain (umin)

/-! ## 1. Lanes -/

/-- The register form of a program: 512-bit `%zmm` or 256-bit `%ymm` registers. -/
inductive Mode where
  | zmm
  | ymm
  deriving DecidableEq

/-- The number of bits an instruction of mode `m` reads and writes. -/
def Mode.act : Mode → Nat
  | .zmm => 512
  | .ymm => 256

/-- The bytes a vector store of mode `m` writes. -/
def Mode.stride (m : Mode) : Nat := m.act / 8

/-- An instruction reads and writes 256 or 512 bits. -/
theorem Mode.act_cases (m : Mode) : m.act = 256 ∨ m.act = 512 := by
  cases m <;> simp [Mode.act]

/-- Lane `k` of width `L` of a 512-bit value, little-endian. -/
def lane (L : Nat) (v : BitVec 512) (k : Nat) : BitVec L :=
  v.extractLsb' (L * k) L

/-- The 512-bit value whose lane `k` of width `L` is `f k`. -/
def ofLanes (L : Nat) (f : Nat → BitVec L) : BitVec 512 :=
  BitVec.ofFnLE (fun i : Fin 512 => (f (i.val / L)).getLsbD (i.val % L))

/-- The value an instruction of mode `m` writes: a `%ymm` write keeps the low 256 bits
    and zeroes the upper 256 bits of the `%zmm` register. -/
def wr : Mode → BitVec 512 → BitVec 512
  | .zmm, x => x
  | .ymm, x => (x.setWidth 256).setWidth 512

/-- Bit `i` of lane `k`. -/
theorem getLsbD_lane (L : Nat) (v : BitVec 512) (k i : Nat) :
    (lane L v k).getLsbD i = (decide (i < L) && v.getLsbD (L * k + i)) := by
  simp [lane, BitVec.getLsbD_extractLsb']

/-- Bit `i` of a lane assembly. -/
theorem getLsbD_ofLanes (L : Nat) (f : Nat → BitVec L) (i : Nat) :
    (ofLanes L f).getLsbD i = (decide (i < 512) && (f (i / L)).getLsbD (i % L)) := by
  unfold ofLanes
  rw [BitVec.getLsbD_ofFnLE]
  by_cases h : i < 512 <;> simp [h]

/-- Bit `i` of a write: the active bits of the value. -/
theorem getLsbD_wr (m : Mode) (x : BitVec 512) (i : Nat) :
    (wr m x).getLsbD i = (decide (i < m.act) && x.getLsbD i) := by
  cases m
  · by_cases h : i < 512
    · simp [wr, Mode.act, h]
    · simp [wr, Mode.act, h, BitVec.getLsbD_of_ge x i (by omega)]
  · simp only [wr, Mode.act, BitVec.getLsbD_setWidth]
    by_cases h : i < 256 <;> simp [h]; omega

/-- Lane `k` of a lane assembly is `f k`. -/
theorem lane_ofLanes {L k : Nat} (f : Nat → BitVec L) (hL : 0 < L) (hk : L * k + L ≤ 512) :
    lane L (ofLanes L f) k = f k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : (L * k + i) / L = k := by
    rw [Nat.mul_add_div hL, Nat.div_eq_of_lt hi, Nat.add_zero]
  have h2 : (L * k + i) % L = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  rw [getLsbD_lane, getLsbD_ofLanes, h1, h2]
  simp [hi]
  omega

/-- An active lane of a write is the lane of the value. -/
theorem lane_wr {m : Mode} {L k : Nat} (x : BitVec 512) (hk : L * k + L ≤ m.act) :
    lane L (wr m x) k = lane L x k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_lane, getLsbD_lane, getLsbD_wr]
  have : L * k + i < m.act := by omega
  simp [this]

/-- A write is idempotent. -/
theorem wr_wr (m : Mode) (x : BitVec 512) : wr m (wr m x) = wr m x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_wr, getLsbD_wr]
  by_cases h : i < m.act <;> simp [h]

/-- Two values agree after a write of mode `m` when their active lanes of width `L`
    agree, for `L` either lane width. -/
theorem wr_eq_of_lanes {m : Mode} {L : Nat} (hL : L = 32 ∨ L = 64) {x y : BitVec 512}
    (h : ∀ k, L * k + L ≤ m.act → lane L x k = lane L y k) : wr m x = wr m y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_wr, getLsbD_wr]
  by_cases ha : i < m.act
  · have hb : L * (i / L) + L ≤ m.act := by
      rcases hL with rfl | rfl <;> rcases m.act_cases with h' | h' <;> rw [h'] at ha ⊢ <;> omega
    have hc := congrArg (fun v => v.getLsbD (i % L)) (h (i / L) hb)
    have hL0 : 0 < L := by omega
    have hmod : i % L < L := Nat.mod_lt _ hL0
    have hdm : L * (i / L) + i % L = i := Nat.div_add_mod i L
    simp only [getLsbD_lane, hmod, decide_true, Bool.true_and, hdm] at hc
    simp [ha, hc]
  · simp [ha]

/-- Dword `2i` of a value is the low half of its qword `i`. -/
theorem lane32_even (x : BitVec 512) (i : Nat) :
    lane 32 x (2 * i) = (lane 64 x i).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_lane, BitVec.getLsbD_setWidth, getLsbD_lane]
  have : 32 * (2 * i) + j = 64 * i + j := by omega
  simp [hj, this]
  omega

/-- Dword `2i+1` of a value is the high half of its qword `i`. -/
theorem lane32_odd (x : BitVec 512) (i : Nat) :
    lane 32 x (2 * i + 1) = (lane 64 x i).extractLsb' 32 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_lane, BitVec.getLsbD_extractLsb', getLsbD_lane]
  have : 32 * (2 * i + 1) + j = 64 * i + (32 + j) := by omega
  simp [hj, this]
  omega

/-- The high half of the 64-bit product of two zero-extended dwords is their high
    multiply. -/
theorem hi_mul_setWidth (a b : BitVec 32) :
    (a.setWidth 64 * b.setWidth 64).extractLsb' 32 32 = mulHiW a b := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 64 := by
    calc a.toNat * b.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 64 := by norm_num
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth, mulHiW,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega),
    Nat.mod_eq_of_lt hab, Nat.shiftRight_eq_div_pow]

/-- The low half of the 64-bit product of two zero-extended dwords is their product. -/
theorem lo_mul_setWidth (a b : BitVec 32) :
    (a.setWidth 64 * b.setWidth 64).setWidth 32 = a * b := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega),
    Nat.mod_mod_of_dvd _ (by norm_num)]

/-! ## 2. Lane-wise operations -/

/-- A lane-wise binary operation: a `JasminBinOp`, the unsigned minimum, or the product
    of the low 32 bits of each lane (`vpmuludq`). -/
inductive LOp where
  | bin (b : JasminBinOp)
  | minu
  | muludq
  deriving DecidableEq

/-- The operation on one lane of width `L`. -/
def LOp.apply {L : Nat} : LOp → BitVec L → BitVec L → BitVec L
  | .bin b, x, y => b.apply x y
  | .minu, x, y => umin x y
  | .muludq, x, y => (x.setWidth 32).setWidth L * (y.setWidth 32).setWidth L

/-- The lane-wise operation `o` on lanes of width `L`. -/
def semLW (L : Nat) (o : LOp) (x y : BitVec 512) : BitVec 512 :=
  ofLanes L (fun k => o.apply (lane L x k) (lane L y k))

/-- The shift of every lane of width `L` by the immediate `imm`, left or right. -/
def semShImm (L : Nat) (left : Bool) (imm : Nat) (x : BitVec 512) : BitVec 512 :=
  ofLanes L (fun k => if left then lane L x k <<< imm else lane L x k >>> imm)

/-- `vmovshdup` (`odd`): each dword pair takes its odd dword; `vmovsldup`: its even
    dword. -/
def semDup (odd : Bool) (x : BitVec 512) : BitVec 512 :=
  ofLanes 32 (fun j => lane 32 x (2 * (j / 2) + if odd then 1 else 0))

/-- The merge under the mask `k`: dword `j` of `new` where bit `j` of `k` is set, else
    dword `j` of `old`. -/
def semMerge (k : BitVec 16) (new old : BitVec 512) : BitVec 512 :=
  ofLanes 32 (fun j => if k.getLsbD j then lane 32 new j else lane 32 old j)

/-- Every lane of width `L` holding `x`. -/
def bcast (L : Nat) (x : BitVec L) : BitVec 512 := ofLanes L (fun _ => x)

/-- The eight quadwords `q[0..7]` read from memory, missing ones zero. -/
def quadsVec (q : Array (BitVec 64)) : BitVec 512 := ofLanes 64 (fun i => q.getD i 0)

/-- Lane `k` of a lane-wise operation. -/
theorem lane_semLW {L k : Nat} (o : LOp) (x y : BitVec 512) (hL : 0 < L)
    (hk : L * k + L ≤ 512) :
    lane L (semLW L o x y) k = o.apply (lane L x k) (lane L y k) :=
  lane_ofLanes _ hL hk

/-- Lane `k` of an immediate shift. -/
theorem lane_semShImm {L k : Nat} (left : Bool) (imm : Nat) (x : BitVec 512) (hL : 0 < L)
    (hk : L * k + L ≤ 512) :
    lane L (semShImm L left imm x) k =
      if left then lane L x k <<< imm else lane L x k >>> imm :=
  lane_ofLanes _ hL hk

/-- Dword `j` of a dword duplication. -/
theorem lane_semDup {j : Nat} (odd : Bool) (x : BitVec 512) (hj : j < 16) :
    lane 32 (semDup odd x) j = lane 32 x (2 * (j / 2) + if odd then 1 else 0) :=
  lane_ofLanes _ (by omega) (by omega)

/-- Dword `j` of a masked merge. -/
theorem lane_semMerge {j : Nat} (k : BitVec 16) (new old : BitVec 512) (hj : j < 16) :
    lane 32 (semMerge k new old) j = if k.getLsbD j then lane 32 new j else lane 32 old j :=
  lane_ofLanes _ (by omega) (by omega)

/-! ## 3. The machine -/

/-- A read-only memory operand: a label's 64 bytes, or its first quadword or dword
    broadcast to every lane. -/
inductive CSrc where
  | full (lbl : String)
  | bq (lbl : String)
  | bd (lbl : String)
  deriving DecidableEq

/-- The second source of a lane-wise instruction: a register or a read-only operand. -/
inductive Opnd where
  | reg (r : Fin 32)
  | mem (c : CSrc)
  deriving DecidableEq

/-- The instruction forms of the renderer's text. -/
inductive Instr where
  /-- `vmovdqu64 off(%rsi), dst`. -/
  | ldIn (off : Nat) (dst : Fin 32)
  /-- `vmovdqu64 lbl(%rip), dst`, `vpbroadcastq lbl(%rip), dst`, `vpbroadcastd …`. -/
  | ldC (c : CSrc) (dst : Fin 32)
  /-- `vmovdqu64 src, off(%rdi)`. -/
  | st (src : Fin 32) (off : Nat)
  /-- `mnem src2, src1, dst`: `dst := src1 ∘ src2` lane-wise at width `L`. -/
  | op (L : Nat) (o : LOp) (src2 : Opnd) (src1 dst : Fin 32)
  /-- `vpsllq/vpsrlq/vpslld/vpsrld $imm, src, dst`. -/
  | shi (L : Nat) (left : Bool) (imm : Nat) (src dst : Fin 32)
  /-- `vmovshdup` (`odd`) or `vmovsldup` `src, dst`, with an optional merge mask. -/
  | dup (odd : Bool) (src dst : Fin 32) (mask : Option (Fin 8))
  /-- `vmovdqa64 src, dst`. -/
  | mova (src dst : Fin 32)
  /-- `movl $imm, %eax`. -/
  | movEax (imm : BitVec 32)
  /-- `kmovw %eax, %kN`. -/
  | kmov (k : Fin 8)
  /-- `vmovdqu64 off(%rsp), dst`: a load from the stack frame. -/
  | ldS (off : Nat) (dst : Fin 32)
  /-- `vmovdqu64 src, off(%rsp)`: a store to the stack frame. -/
  | stS (src : Fin 32) (off : Nat)
  /-- `subq $n, %rsp`: allocate `n` bytes of stack frame. -/
  | spSub (n : Nat)
  /-- `addq $n, %rsp`: release `n` bytes of stack frame. -/
  | spAdd (n : Nat)
  deriving DecidableEq

/-- The machine state: 32 vector registers, `%eax`, the mask registers, the stores
    to the output region, newest first, and the stack. -/
structure MState where
  /-- The vector registers. -/
  zmm : Fin 32 → BitVec 512
  /-- `%eax`. -/
  eax : BitVec 32
  /-- The mask registers. -/
  kr : Fin 8 → BitVec 16
  /-- The stores: offset and value, newest first. -/
  log : List (Nat × BitVec 512)
  /-- The stack: the register value last stored at each byte offset from `%rsp`. -/
  stk : Int → BitVec 512

/-- The state with register `d` set to `v`. -/
def MState.setZ (σ : MState) (d : Fin 32) (v : BitVec 512) : MState :=
  { σ with zmm := fun r => if r = d then v else σ.zmm r }

/-- The value of a read-only operand, from the data table `ro` (label to quadwords):
    a full read needs the quadwords the mode reads. -/
def csrcVal (m : Mode) (ro : Std.HashMap String (Array (BitVec 64))) :
    CSrc → Option (BitVec 512)
  | .full l => (ro.get? l).bind fun q =>
      if m.act / 64 ≤ q.size then some (quadsVec q) else none
  | .bq l => (ro.get? l).bind fun q => q[0]?.map (bcast 64)
  | .bd l => (ro.get? l).bind fun q => q[0]?.map (fun x => bcast 32 (x.setWidth 32))

/-- The value of the second source of a lane-wise instruction. -/
def opVal (m : Mode) (ro : Std.HashMap String (Array (BitVec 64))) (σ : MState) :
    Opnd → Option (BitVec 512)
  | .reg r => some (σ.zmm r)
  | .mem c => (csrcVal m ro c).map (wr m)

/-- One instruction on input region `inp` (the 64 bytes at each offset) and data
    table `ro`; `none` on a missing data label. -/
def step (m : Mode) (inp : Nat → BitVec 512) (ro : Std.HashMap String (Array (BitVec 64)))
    (σ : MState) : Instr → Option MState
  | .ldIn off d => some (σ.setZ d (wr m (inp off)))
  | .ldC c d => (csrcVal m ro c).map fun v => σ.setZ d (wr m v)
  | .st r off => some { σ with log := (off, wr m (σ.zmm r)) :: σ.log }
  | .op L o s2 s1 d => (opVal m ro σ s2).map fun b => σ.setZ d (wr m (semLW L o (σ.zmm s1) b))
  | .shi L l i r d => some (σ.setZ d (wr m (semShImm L l i (σ.zmm r))))
  | .dup odd r d none => some (σ.setZ d (wr m (semDup odd (σ.zmm r))))
  | .dup odd r d (some k) =>
      some (σ.setZ d (wr m (semMerge (σ.kr k) (semDup odd (σ.zmm r)) (σ.zmm d))))
  | .mova r d => some (σ.setZ d (wr m (σ.zmm r)))
  | .movEax imm => some { σ with eax := imm }
  | .kmov k => some { σ with kr := fun k' => if k' = k then σ.eax.setWidth 16 else σ.kr k' }
  | .ldS off d => some (σ.setZ d (wr m (σ.stk off)))
  | .stS r off => some { σ with stk := fun a => if a = (off : Int) then σ.zmm r else σ.stk a }
  | .spSub n => some { σ with stk := fun a => σ.stk (a - n) }
  | .spAdd n => some { σ with stk := fun a => σ.stk (a + n) }

/-- A straight-line run; `none` when an instruction fails. -/
def run (m : Mode) (inp : Nat → BitVec 512) (ro : Std.HashMap String (Array (BitVec 64))) :
    MState → List Instr → Option MState
  | σ, [] => some σ
  | σ, i :: is => (step m inp ro σ i).bind fun σ' => run m inp ro σ' is

/-- The last value stored at offset `off` of the output region. -/
def MState.outAt (σ : MState) (off : Nat) : Option (BitVec 512) :=
  (σ.log.find? (fun e => e.1 == off)).map (·.2)

/-! ## 4. Symbolic values -/

/-- A symbolic register value: an initial register, a named value of the reference
    program, a constant, or an instruction applied to symbolic values. -/
inductive Term where
  | init (r : Nat)
  | var (n : String)
  | cst (c : BitVec 512)
  | lw (L : Nat) (o : LOp) (a b : Term)
  | shi (L : Nat) (left : Bool) (imm : Nat) (a : Term)
  | dup (odd : Bool) (a : Term)
  | mdup (odd : Bool) (k : BitVec 16) (src old : Term)
  deriving DecidableEq

/-- The value of a term, with initial registers `σ0` and named values `P`. -/
def Term.eval (m : Mode) (σ0 : Fin 32 → BitVec 512) (P : String → BitVec 512) :
    Term → BitVec 512
  | .init r => if h : r < 32 then σ0 ⟨r, h⟩ else 0
  | .var n => wr m (P n)
  | .cst c => wr m c
  | .lw L o a b => wr m (semLW L o (a.eval m σ0 P) (b.eval m σ0 P))
  | .shi L l i a => wr m (semShImm L l i (a.eval m σ0 P))
  | .dup odd a => wr m (semDup odd (a.eval m σ0 P))
  | .mdup odd k a b => wr m (semMerge k (semDup odd (a.eval m σ0 P)) (b.eval m σ0 P))

/-- Whether a term is an initial register. -/
def Term.isInit : Term → Bool
  | .init _ => true
  | _ => false

/-- The value of a term other than an initial register is a write. -/
theorem Term.wr_eval {m : Mode} {σ0 : Fin 32 → BitVec 512} {P : String → BitVec 512}
    (t : Term) (h : t.isInit = false) : wr m (t.eval m σ0 P) = t.eval m σ0 P := by
  cases t <;> simp_all [Term.isInit, Term.eval, wr_wr]

/-- The symbolic state: a term per register, the known values of `%eax` and the mask
    registers, the stores, newest first, the bytes of stack frame allocated since entry,
    and a term per stack slot keyed by its offset from `%rsp` at entry. -/
structure SState where
  /-- The term of each vector register. -/
  regs : Vector Term 32
  /-- The value of `%eax`, when known. -/
  eax : Option (BitVec 32)
  /-- The value of each mask register, when known. -/
  kr : Fin 8 → Option (BitVec 16)
  /-- The stores: offset and term, newest first. -/
  log : List (Nat × Term)
  /-- The bytes of stack frame allocated since entry: `%rsp` is `sp` bytes below its
      value at entry. -/
  sp : Int
  /-- The term last stored to each stack slot, keyed by its offset from `%rsp` at entry. -/
  stk : Std.HashMap Int Term

/-- The symbolic state at entry. -/
def SState.init : SState :=
  { regs := Vector.ofFn (fun r => .init r.val), eax := none, kr := fun _ => none, log := [],
    sp := 0, stk := {} }

/-- The symbolic state with register `d` set to `t`. -/
def SState.setR (s : SState) (d : Fin 32) (t : Term) : SState :=
  { s with regs := s.regs.set d t }

/-- The symbolic second source. -/
def symOpnd (m : Mode) (ro : Std.HashMap String (Array (BitVec 64))) (s : SState) :
    Opnd → Option Term
  | .reg r => some s.regs[(r : Nat)]
  | .mem c => (csrcVal m ro c).map .cst

/-- One symbolic step: `paramAt off` names the input at offset `off`, and `norm`
    replaces a term by an equal one. -/
def sstep (m : Mode) (ro : Std.HashMap String (Array (BitVec 64)))
    (paramAt : Nat → Option String) (norm : Term → Term) (s : SState) :
    Instr → Option SState
  | .ldIn off d => (paramAt off).map fun p => s.setR d (.var p)
  | .ldC c d => (csrcVal m ro c).map fun v => s.setR d (norm (.cst v))
  | .st r off => some { s with log := (off, s.regs[(r : Nat)]) :: s.log }
  | .op L o s2 s1 d =>
      (symOpnd m ro s s2).map fun t => s.setR d (norm (.lw L o s.regs[(s1 : Nat)] t))
  | .shi L l i r d => some (s.setR d (norm (.shi L l i s.regs[(r : Nat)])))
  | .dup odd r d none => some (s.setR d (norm (.dup odd s.regs[(r : Nat)])))
  | .dup odd r d (some k) =>
      (s.kr k).map fun kv =>
        s.setR d (norm (.mdup odd kv s.regs[(r : Nat)] s.regs[(d : Nat)]))
  | .mova r d =>
      if s.regs[(r : Nat)].isInit then none else some (s.setR d s.regs[(r : Nat)])
  | .movEax imm => some { s with eax := some imm }
  | .kmov k => s.eax.map fun v =>
      { s with kr := fun k' => if k' = k then some (v.setWidth 16) else s.kr k' }
  | .ldS off d =>
      match s.stk[(off : Int) - s.sp]? with
      | some t => if t.isInit then none else some (s.setR d t)
      | none => none
  | .stS r off => some { s with stk := s.stk.insert ((off : Int) - s.sp) s.regs[(r : Nat)] }
  | .spSub n => some { s with sp := s.sp + n }
  | .spAdd n => some { s with sp := s.sp - n }

/-- The symbolic run. -/
def srun (m : Mode) (ro : Std.HashMap String (Array (BitVec 64)))
    (paramAt : Nat → Option String) (norm : Term → Term) :
    SState → List Instr → Option SState
  | s, [] => some s
  | s, i :: is => (sstep m ro paramAt norm s i).bind fun s' => srun m ro paramAt norm s' is

/-- The symbolic state `s` describes the machine state `σ`. -/
def Rel (m : Mode) (σ0 : Fin 32 → BitVec 512) (P : String → BitVec 512) (s : SState)
    (σ : MState) : Prop :=
  (∀ r : Fin 32, s.regs[(r : Nat)].eval m σ0 P = σ.zmm r) ∧
  (∀ v, s.eax = some v → σ.eax = v) ∧
  (∀ k v, s.kr k = some v → σ.kr k = v) ∧
  List.Forall₂ (fun a b => a.1 = b.1 ∧ wr m (a.2.eval m σ0 P) = b.2) s.log σ.log ∧
  (∀ a t, s.stk[a]? = some t → σ.stk (a + s.sp) = t.eval m σ0 P)

/-- The symbolic entry state describes every machine state with no stores. -/
theorem rel_init (m : Mode) (σ : MState) (P : String → BitVec 512) (h : σ.log = []) :
    Rel m σ.zmm P SState.init σ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    simp [SState.init, Term.eval]
  · simp [SState.init]
  · simp [SState.init]
  · simp [SState.init, h]
  · simp [SState.init]

/-- Setting a register to a term and to its value preserves `Rel`. -/
theorem rel_setR {m : Mode} {σ0 : Fin 32 → BitVec 512} {P : String → BitVec 512}
    {s : SState} {σ : MState} (h : Rel m σ0 P s σ) (d : Fin 32) (t : Term)
    (v : BitVec 512) (ht : t.eval m σ0 P = v) : Rel m σ0 P (s.setR d t) (σ.setZ d v) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, h2, h3, h4, h5⟩
  intro r
  simp only [SState.setR, MState.setZ, Vector.getElem_set]
  by_cases hr : r = d
  · subst hr; simp [ht]
  · have hr' : ¬ (d : Nat) = r := fun e => hr (Fin.ext e.symm)
    simp [hr, hr', h1 r]

/-- One symbolic step describes one machine step, when `norm` preserves values and
    each input offset holds the value its name denotes. -/
theorem sstep_sound {m : Mode} {ro : Std.HashMap String (Array (BitVec 64))}
    {paramAt : Nat → Option String} {norm : Term → Term} {σ0 : Fin 32 → BitVec 512}
    {P : String → BitVec 512} {inp : Nat → BitVec 512}
    (hnorm : ∀ t, (norm t).eval m σ0 P = t.eval m σ0 P)
    (hin : ∀ off p, paramAt off = some p → wr m (inp off) = wr m (P p))
    {s s' : SState} {σ : MState} (h : Rel m σ0 P s σ) (i : Instr)
    (hs : sstep m ro paramAt norm s i = some s') :
    ∃ σ', step m inp ro σ i = some σ' ∧ Rel m σ0 P s' σ' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have h : Rel m σ0 P s σ := ⟨h1, h2, h3, h4, h5⟩
  cases i with
  | ldIn off d =>
    simp only [sstep, Option.map_eq_some_iff] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact ⟨_, rfl, rel_setR h d _ _ (by simp [Term.eval, hin off p hp])⟩
  | ldC c d =>
    simp only [sstep, Option.map_eq_some_iff] at hs
    obtain ⟨v, hv, rfl⟩ := hs
    exact ⟨σ.setZ d (wr m v), by simp [step, hv], rel_setR h d _ _ (by rw [hnorm]; rfl)⟩
  | st r off =>
    simp only [sstep, Option.some.injEq] at hs
    subst hs
    refine ⟨_, rfl, h1, h2, h3, ?_, h5⟩
    exact List.Forall₂.cons ⟨rfl, by rw [h1 r]⟩ h4
  | op L o s2 s1 d =>
    simp only [sstep, Option.map_eq_some_iff] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    cases s2 with
    | reg r =>
      simp only [symOpnd, Option.some.injEq] at ht
      subst ht
      exact ⟨_, rfl, rel_setR h d _ _ (by rw [hnorm]; simp [Term.eval, h1])⟩
    | mem c =>
      simp only [symOpnd, Option.map_eq_some_iff] at ht
      obtain ⟨v, hv, rfl⟩ := ht
      exact ⟨σ.setZ d (wr m (semLW L o (σ.zmm s1) (wr m v))), by simp [step, opVal, hv],
        rel_setR h d _ _ (by rw [hnorm]; simp [Term.eval, ← h1 s1])⟩
  | shi L l imm r d =>
    simp only [sstep, Option.some.injEq] at hs
    subst hs
    exact ⟨_, rfl, rel_setR h d _ _ (by rw [hnorm]; simp [Term.eval, h1])⟩
  | dup odd r d mask =>
    cases mask with
    | none =>
      simp only [sstep, Option.some.injEq] at hs
      subst hs
      exact ⟨_, rfl, rel_setR h d _ _ (by rw [hnorm]; simp [Term.eval, h1])⟩
    | some k =>
      simp only [sstep, Option.map_eq_some_iff] at hs
      obtain ⟨kv, hk, rfl⟩ := hs
      exact ⟨_, rfl, rel_setR h d _ _ (by rw [hnorm]; simp [Term.eval, h1, h3 k kv hk])⟩
  | mova r d =>
    simp only [sstep] at hs
    split at hs
    · cases hs
    · rename_i hni
      simp only [Option.some.injEq] at hs
      subst hs
      refine ⟨_, rfl, rel_setR h d _ _ ?_⟩
      rw [← h1 r, Term.wr_eval _ (by simpa using hni)]
  | movEax imm =>
    simp only [sstep, Option.some.injEq] at hs
    subst hs
    exact ⟨_, rfl, h1, by simp, h3, h4, h5⟩
  | kmov k =>
    simp only [sstep, Option.map_eq_some_iff] at hs
    obtain ⟨v, hv, rfl⟩ := hs
    refine ⟨_, rfl, h1, h2, ?_, h4, h5⟩
    intro k' v' hk'
    by_cases e : k' = k
    · subst e; simp at hk' ⊢; rw [← hk', h2 v hv]
    · simp [e] at hk' ⊢; exact h3 k' v' hk'
  | ldS off d =>
    simp only [sstep] at hs
    split at hs
    · rename_i t ht
      split at hs
      · cases hs
      · rename_i hni
        simp only [Option.some.injEq] at hs
        subst hs
        refine ⟨_, rfl, rel_setR h d _ _ ?_⟩
        have e := h5 _ t ht
        rw [Int.sub_add_cancel] at e
        rw [e, Term.wr_eval _ (by simpa using hni)]
    · cases hs
  | stS r off =>
    simp only [sstep, Option.some.injEq] at hs
    subst hs
    refine ⟨_, rfl, h1, h2, h3, h4, ?_⟩
    intro a t ht
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at ht
    by_cases e : (off : Int) - s.sp = a
    · subst e
      simp only [if_true, Option.some.injEq] at ht
      subst ht
      simp [h1 r]
    · rw [if_neg e] at ht
      have e' : ¬ a + s.sp = (off : Int) := fun e'' => e (by omega)
      simp only [if_neg e']
      exact h5 a t ht
  | spSub n =>
    simp only [sstep, Option.some.injEq] at hs
    subst hs
    refine ⟨_, rfl, h1, h2, h3, h4, ?_⟩
    intro a t ht
    have e := h5 a t ht
    simp only
    rw [show a + (s.sp + (n : Int)) - (n : Int) = a + s.sp by omega, e]
  | spAdd n =>
    simp only [sstep, Option.some.injEq] at hs
    subst hs
    refine ⟨_, rfl, h1, h2, h3, h4, ?_⟩
    intro a t ht
    have e := h5 a t ht
    simp only
    rw [show a + (s.sp - (n : Int)) + (n : Int) = a + s.sp by omega, e]

/-- A symbolic run describes the machine run of the same program: the machine run
    succeeds and ends in a state the final symbolic state describes. -/
theorem srun_sound {m : Mode} {ro : Std.HashMap String (Array (BitVec 64))}
    {paramAt : Nat → Option String} {norm : Term → Term} {σ0 : Fin 32 → BitVec 512}
    {P : String → BitVec 512} {inp : Nat → BitVec 512}
    (hnorm : ∀ t, (norm t).eval m σ0 P = t.eval m σ0 P)
    (hin : ∀ off p, paramAt off = some p → wr m (inp off) = wr m (P p)) :
    ∀ (prog : List Instr) {s s' : SState} {σ : MState}, Rel m σ0 P s σ →
      srun m ro paramAt norm s prog = some s' →
      ∃ σ', run m inp ro σ prog = some σ' ∧ Rel m σ0 P s' σ'
  | [], _, _, _, h, hs => by
    simp only [srun, Option.some.injEq] at hs
    subst hs
    exact ⟨_, rfl, h⟩
  | i :: is, _, _, _, h, hs => by
    simp only [srun, Option.bind_eq_some_iff] at hs
    obtain ⟨s1, hs1, hs2⟩ := hs
    obtain ⟨σ1, hσ1, h1⟩ := sstep_sound hnorm hin h i hs1
    obtain ⟨σ2, hσ2, h2⟩ := srun_sound hnorm hin is h1 hs2
    exact ⟨σ2, by simp [run, hσ1, hσ2], h2⟩

/-- The last symbolic store at offset `off`. -/
def SState.outAt (s : SState) (off : Nat) : Option Term :=
  (s.log.find? (fun e => e.1 == off)).map (·.2)

/-- The machine's last store at an offset is the value of the symbolic one. -/
theorem outAt_rel {m : Mode} {σ0 : Fin 32 → BitVec 512} {P : String → BitVec 512}
    {s : SState} {σ : MState} (h : Rel m σ0 P s σ) (off : Nat) (t : Term)
    (ht : s.outAt off = some t) : σ.outAt off = some (wr m (t.eval m σ0 P)) := by
  obtain ⟨-, -, -, h4, -⟩ := h
  unfold SState.outAt at ht
  unfold MState.outAt
  generalize s.log = ls at ht h4
  generalize σ.log = ls' at h4
  induction h4 with
  | nil => simp at ht
  | @cons a b l l' hab _ ih =>
    obtain ⟨e1, e2⟩ := hab
    by_cases hc : a.1 = off
    · have hc' : b.1 = off := e1 ▸ hc
      rw [List.find?_cons_of_pos (by simpa using hc)] at ht
      rw [List.find?_cons_of_pos (by simpa using hc')]
      simp only [Option.map_some, Option.some.injEq] at ht ⊢
      rw [← e2, ht]
    · have hc' : ¬ b.1 = off := e1 ▸ hc
      rw [List.find?_cons_of_neg (by simpa using hc)] at ht
      rw [List.find?_cons_of_neg (by simpa using hc')]
      exact ih ht

end CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel
