/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFGMemF
public import CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86IsaDef
public import Std.Data.HashMap.Basic
public import Std.Data.TreeMap.Lemmas

/-!
# Value translation validation of a body rewrite under `lsemFuelMemF`

A checker `ownedCheckM outs B B'` for a typed body `B` and a rewritten body `B'`, with
the theorem that every halting `lsemFuelMemF` run of `B` from pc `0` is matched by a
halting run of `B'` from the same state, the end states agreeing on the registers
`outs`, on the arrays and on the word memory.

## Symbolic execution

A symbolic word (`STerm`) is a term over the registers, arrays, carry flag and overflow
flag at the start of a block; it denotes a width-tagged word `Σ w, BitVec w`, as the
register file of `LstateN` stores it, and a flag is a word of width `1`. A symbolic array
(`SArr`) denotes an `ArrCell`, a symbolic flag (`SFlag`) the zero flag. A guard (`SG`)
states a width or a shape of a symbolic value. Terms name the values at the block start,
never registers, so a renaming of registers inside a block leaves them unchanged.

`symStep i ss` describes one instruction `i` exactly: `ok ss' gs` when the step of
`evalInstrPMemF` succeeds from a state `ss` describes if and only if the guards `gs`
hold, and then ends in a state `ss'` describes; `fail` when the step fails from every such
state; `unk` when the instruction is outside the described fragment. The fragment is the
flag `CMP`, the register copies (`MOV` and the array-ABI moves `MOVQ`, `LOAD:64`,
`STORE:64`), labels, `Lalign`, the array load and store of
`lsemStepMem`, the arms of `lsemStepN` (two-source arithmetic, immediate `MOV`, `NEG`,
immediate shifts, the register select `CMOV` as `STerm.sel`) with the carry and overflow flags `withALUFlags` writes, the carry
family `ADC`, `SBB`, `ADCX`, `ADOX` of `carryStep`, and the two-source `MOV` and the
widening multiplies `MULX`, `MULXMEM` of `wideStep` (`symWide`: the low word the masked
low `MUL` term `mulLoT`, the term of the front's masked low product, and the high word
`STerm.mulx`), the high word `MULXHI` of `lsemStepMC` (the term `bin "MULXHI"`, `binW`), and
the register-carry arms `ADCX`, `SBB` (nested `bin "ADD"`, `bin "SUB"`) and `ADCXHI`, `SBBHI`
(`STerm.cout`) of `lsemStepMC`; `SAR`, a `CMOV` whose condition or first value is no register or whose second value is
neither a register nor an immediate, the
casts and the compile-time-offset memory moves are `unk`. `symRun` composes the steps of a
list.

## The check

The two control-flow graphs (`AllocCheck.LcmdCFG.cfgOf`) must have the same number of
blocks and the same terminators. Each block pair is run symbolically from one symbolic
start state; the pair is accepted when the source block always fails or ends in `Lret`
(no halting run passes through it), or when every guard of the normal form (`normG`) of the
rewritten block's guards is one of the source block or holds wherever the source block's
guards hold, two jumps name the same function, two
branch conditions have the same symbolic value, and at each exit the final symbolic states
agree on the registers live at the successor (on `outs` at an exit that leaves the body), on
the zero, carry and overflow flags when the flags are live, and on every array written,
with every start register these values read live at the block, and the flags live at the
block when a value reads a start flag. A register agrees when its two words are one word or
evaluate alike wherever the source block's guards hold (`regAgree`). The live sets are
computed by a fixpoint iteration (`liveIter`) and checked, not trusted.

## Carries in flags

The check over the term table decides the two semantic agreements by canonical keys (section
14b): a normal form `STerm.normC` of each node over the keys of its children, computed once for
the table (`CanonT.build`) with the widths that the source block's guards state of start
registers (`guardFacts`). The value form of a carry step (the three-source `ADCX`, its
carry-out `ADCXHI`) and its flag form (`ADD`, `ADC`, `ADCX`, `ADOX` and the carry and overflow
flags they write) have one key, and so have the sources of an addition in either order. Two exit
words with one key evaluate alike (`canonEqT_ev`), and a guard decided by the widths of the keys
holds (`SG.impT_holds`), so a body whose carries are held in the flags is checked against the
same computation with materialised carries.

## Shared terms

The two bodies of a block pair run over one hash-consed term table (`Tbl`, `tRun`), so the
symbolic words of a block take space linear in its length and equal words are compared by
index. A word over the table stands for its instance under a substitution of its entries
(`STerm.subst`); the symbolic step commutes with substitution (`symStep_subst`), so the run
over the table is the symbolic run up to that substitution (`tRun_subst`), and the check
over the table (`blockOkR`) implies `blockOk` (`blockOkR_spec`).

## Instruction sets

The checker (`symRun`, `blockOk`, `ownedCheckWith`, `tRun`, `blockOkR`, `ownedCheckM`) takes
the symbolic step and the symbolic branch condition as trailing arguments that default to
the x86 ones, `symStep` and `symDec`. Its soundness is proved for every instruction set
`I : LprogIsa.Isa` whose step the two describe (`SymLaws I sym dec`) and that commute with
substitution (`SymSubst sym dec`), in the theorems with the suffix `_at`. The x86 instruction
set `X86Isa.x86Isa` (the flag machine `evalInstrPMemF` with the branch condition `decC`) is
defined in this module, and the theorems about `evalInstrPMemF` and `lsemFuelMemF` are the
instances at it (`symLaws_x86`, `symSubst_x86`).

## Main definitions

* `X86Isa.x86Isa`, `StepPlain`, `SymLaws`, `SymSubst`: the x86 instruction set and the laws
  of a symbolic step against an instruction set.
* `STerm`, `SArr`, `SFlag`, `SG`, `SSt`, `Holds`: symbolic values, states and the states
  they describe.
* `symN`, `symSh`, `symMC`, `symCast`, `symMem`, `aluFl`, `symCarry`, `symWide`, `symStep`,
  `symRun`:
  the symbolic step layer by layer, and runs.
* `SDec`, `symDec`: the symbolic value of a branch condition.
* `blockOk`, `ownedCheckWith`, `ownedCheckM`: the checker.
* `STerm.semEqG`, `SG.impG`, `regAgree`: agreement of two words and a guard implied by the
  source guards, at every evaluation where those guards hold.
* `STerm.normC`, `CanonT`, `CanonT.build`, `canonEqT`, `guardFacts`, `SG.impT`, `regAgreeT`:
  the canonical keys of a term table and the checks over them.
* `STerm.subst`, `TEnt`, `Tbl`, `Tbl.intern`, `tRun`: substitution, the term table and the
  run over it.
* `blockRuns`, `blockOkR`, `runsOf`, `ownedCheckWithR`: the checker over the table.
* `typeBody`, `dropRet`, `memOuts`, `resOuts`, `ownedCheckTy`, `ownedCheck`: the checker on
  the first functions of two programs, observing the result registers and the memory cells
  written at the argument pointers, with the two-address gate
  `TwoAddrLegalize.bodyTiedOk`.
* `Rel`, `Obs`: the agreement of two states at a block entry and at the end.

## Main results

* `symN_sound`, `symSh_sound`, `symMC_sound`, `symCast_sound`, `symMem_sound`,
  `aluFlT_sound`, `symCarry_sound`, `symWide_sound`, `symStep_sound`: each layer of the
  step is described
  exactly.
* `symStep_comm`: a commutative operation `opn d, [x, d]` and `opn d, [d, x]` have one
  description (`commSwap`).
* `mulLoT_ev`: the masked low `MUL` term is the low word of `x86_MULX_lo_hi`.
* `symRun_sound`: the symbolic run describes the run of a list exactly.
* `fuel_runL`, `runL_fuel`: a run through straight-line instructions of a body.
* `decC_eq`: the symbolic branch condition describes the branch taken.
* `symStep_subst`, `symRun_subst`, `tRun_subst`, `blockOkR_spec`: the run and the check
  over the table.
* `ownedCheckWith_sound_at`, `ownedCheckM_sound_at`: soundness of the checker over an
  instruction set.
* `carryWord_adc`, `carryBit_adc`, `carryOutBit_eq`, `borrowOutBit_eq`, `aluBit_add`,
  `aluBit_sub`, `binW_add_carry`, `binW_sub_borrow`: the words and carries of one carry step in
  its two forms agree.
* `STerm.normC_ev`, `CanonT.ok_build`, `canonEqT_ev`, `SG.impT_holds`, `guardFacts_sound`,
  `regAgreeT_spec`: the normal form evaluates as the node, the canonical keys describe the
  table, and words with one key evaluate alike.
* `ownedCheckWith_sound`, `ownedCheckM_sound`, `ownedCheckTy_sound`,
  `ownedCheckTy_sound_mem`: soundness of the checker.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (stackGet stackSet mulHiW)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (lsemStepSh sarStruct? lsemStepSh_of_not_sar)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
  (lsemStepMC mulhiStruct? adcxStruct? adcxhiStruct? sbbStruct? sbbhiStruct?
   lsemStepMC_of_delegate)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
  (LinstrRT lsemStepCast castStruct? movImmStruct? lsemStepCast_of_delegate)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminImmShiftMnem (immShiftMnem?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (x86_ADC x86_SBB x86_ADCX x86_MULX_lo_hi)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
  (lsemStepMem_of_carryArgs lsemStepMem_of_wideArgs lsemStepMem_flags)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa isCtl ctlStep)

/-! ## 1. Width casts -/

/-- The word of a width-tagged value at width `w`, `0` on a width mismatch. -/
def castW (x : Σ w, BitVec w) (w : Nat) : BitVec w :=
  if h : x.1 = w then h ▸ x.2 else 0

/-- The array of a cell at shape `(w, n)`, the zero array on a shape mismatch. -/
def castA (c : ArrCell) (w n : Nat) : Fin n → BitVec w :=
  if hw : c.1 = w then
    if hn : c.2.1 = n then hn ▸ hw ▸ c.2.2 else fun _ => 0
  else fun _ => 0

@[simp] theorem castW_self (x : Σ w, BitVec w) : castW x x.1 = x.2 := by
  simp [castW]

/-- The word of a width-tagged value at width `w`, zero-extended or truncated. -/
def extW (x : Σ w, BitVec w) (w : Nat) : BitVec w := x.2.setWidth w

theorem extW_of_eq {x : Σ w, BitVec w} {w : Nat} (h : x.1 = w) : extW x w = castW x w := by
  obtain ⟨w', v⟩ := x
  simp only at h
  subst h
  simp [extW, castW]

theorem extW_ofNat {w v n : Nat} (h : n < 2 ^ w) :
    extW ⟨w, BitVec.ofNat w n⟩ v = BitVec.ofNat v n := by
  apply BitVec.eq_of_toNat_eq
  simp [extW, BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

theorem sigma_of_castW {x : Σ w, BitVec w} {w : Nat} (h : x.1 = w) :
    (⟨w, castW x w⟩ : Σ w, BitVec w) = x := by
  obtain ⟨w', v⟩ := x
  simp only at h
  subst h
  simp [castW]

theorem getW_eq (s : LstateN) (r : String) (w : Nat) :
    s.getW r w = if (s.lvm r).1 = w then some (castW (s.lvm r) w) else none := by
  unfold LstateN.getW castW
  by_cases h : (s.lvm r).1 = w <;> simp [h]

theorem getArr_eq (s : LstateM) (r : String) (w n : Nat) :
    s.getArr r w n =
      if (s.larr r).1 = w ∧ (s.larr r).2.1 = n then some (castA (s.larr r) w n) else none := by
  unfold LstateM.getArr castA
  by_cases hw : (s.larr r).1 = w
  · by_cases hn : (s.larr r).2.1 = n <;> simp [hw, hn]
  · simp [hw]

theorem cell_of_castA {c : ArrCell} {w n : Nat} (hw : c.1 = w) (hn : c.2.1 = n) :
    (⟨w, n, castA c w n⟩ : ArrCell) = c := by
  obtain ⟨w', n', a⟩ := c
  simp only at hw hn
  subst hw hn
  simp [castA]

/-! ## 2. Symbolic words, arrays, flags and guards -/

/-- The bit of a width-tagged word: its least significant bit. -/
def bitOf (x : Σ w, BitVec w) : Bool := x.2.getLsbD 0

@[simp] theorem bitOf_ofBool (b : Bool) : bitOf ⟨1, BitVec.ofBool b⟩ = b := by
  cases b <;> rfl

/-- The carry flag (`ofl = false`) or the overflow flag (`ofl = true`) that the
    arithmetic or logical operation `op` writes on `a` and `b`. -/
def aluBit (op : AluOp) (ofl : Bool) (a b : BitVec 64) : Bool :=
  if ofl then (aluB5 op a b).of.getD false else (aluB5 op a b).cf.getD false

/-- The word a carry-family operation writes, with carry-in `c`. -/
def carryWord : CarryOp → BitVec 64 → BitVec 64 → Bool → BitVec 64
  | .adc, a, b, c => (x86_ADC a b c).word
  | .sbb, a, b, c => (x86_SBB a b c).word
  | .adcx, a, b, c => (x86_ADCX a b c).2
  | .adox, a, b, c => (x86_ADCX a b c).2

/-- The carry flag (`ofl = false`) or the overflow flag (`ofl = true`) a carry-family
    operation writes, with carry-in `c`. `ADCX` writes only the carry flag and `ADOX` only
    the overflow flag, each the carry out of the addition. -/
def carryBit (op : CarryOp) (ofl : Bool) (a b : BitVec 64) (c : Bool) : Bool :=
  match op with
  | .adc => if ofl then (x86_ADC a b c).of.getD false else (x86_ADC a b c).cf.getD false
  | .sbb => if ofl then (x86_SBB a b c).of.getD false else (x86_SBB a b c).cf.getD false
  | .adcx => (x86_ADCX a b c).1.getD false
  | .adox => (x86_ADCX a b c).1.getD false

deriving instance Hashable for AluOp, CarryOp, JasminDialect.JasminCmp

/-- The two-source operation `m` at width `w`: the high word of the product (`mulHiW`) for
    `MULXHI`, the operation of `applyOpnN` otherwise, and `a` when `applyOpnN` has no
    operation `m`. -/
def binW (w : Nat) (m : String) (a b : BitVec w) : BitVec w :=
  if m = "MULXHI" then mulHiW a b else (applyOpnN w m [a, b]).getD a

/-- The carry-out (`sub = false`, `carryOutBit`) or borrow-out (`sub = true`, `borrowOutBit`)
    bit of the register-carry step on `x` and `y` at the width of `x`, with `y` extended or
    truncated to that width and the carry-in `c` to width `1` (`extW`). -/
def coutBit (sub : Bool) (x y c : Σ w, BitVec w) : BitVec 1 :=
  if sub then JasminDialect.borrowOutBit x.2 (extW y x.1) (extW c 1)
  else JasminDialect.carryOutBit x.2 (extW y x.1) (extW c 1)

mutual
/-- A symbolic width-tagged word over the registers and arrays at the start of a
    block. -/
inductive STerm where
  /-- The value of a register at the start. -/
  | reg (r : String)
  /-- The immediate `n` at width `w`. -/
  | immW (w n : Nat)
  /-- The immediate `n` at the width of `x`. -/
  | immAt (n : Nat) (x : STerm)
  /-- The two-source operation `m` (`binW`) at the width of `x`, with `y` zero-extended or
      truncated to that width (`extW`). -/
  | bin (m : String) (x y : STerm)
  /-- The one-source operation `m` of `applyOpnN` at the width of `x`. -/
  | un (m : String) (x : STerm)
  /-- The immediate shift `m` by `k` of `applyImmShiftN` at the width of `x`. -/
  | shImm (m : String) (k : Nat) (x : STerm)
  /-- Element `i` of the array `a` read at shape `(w, n)`. -/
  | aget (a : SArr) (w n : Nat) (i : STerm)
  /-- The carry flag (`ofl = false`) or the overflow flag (`ofl = true`) at the start, as a
      word of width `1`. -/
  | cin (ofl : Bool)
  /-- The flag `aluBit op ofl` on `x` and `y` read at width `64`, as a word of width `1`;
      `old` when `x` or `y` is not of width `64`. -/
  | aluF (op : AluOp) (ofl : Bool) (x y old : STerm)
  /-- The word of the carry-family operation `op` on `x` and `y` read at width `64`, with
      the carry-in the bit of `c`. -/
  | carryW (op : CarryOp) (x y c : STerm)
  /-- The flag `carryBit op ofl` on `x` and `y` read at width `64`, with the carry-in the bit
      of `c`, as a word of width `1`. -/
  | carryF (op : CarryOp) (ofl : Bool) (x y c : STerm)
  /-- The low (`hi = false`) or high (`hi = true`) word of the widening product
      `x86_MULX_lo_hi` of `x` and `y` read at width `64`. -/
  | mulx (hi : Bool) (x y : STerm)
  /-- The carry-out (`sub = false`) or borrow-out (`sub = true`) bit `coutBit` of the
      register-carry step on `x`, `y` and the carry-in `c`, as a word of width `1`. -/
  | cout (sub : Bool) (x y c : STerm)
  /-- The select `selectW` of `x` (when the bit of `c` read at width `1` is set) or `y`, at
      the width of `x`, with `y` extended or truncated to that width (`extW`). -/
  | sel (x y c : STerm)
  /-- The comparison bit `cmpBit c` of `x` and `y` at the width of `x`, with `y` extended or
      truncated to that width (`extW`), as a word of width `1`. -/
  | setcc (c : JasminDialect.JasminCmp) (x y : STerm)
  /-- Entry `k` of a term table (`TEnt`); a substitution (`STerm.subst`) gives it its term,
      and `STerm.ev` gives it the word of width `0`. -/
  | ref (k : Nat)

/-- A symbolic array cell over the registers and arrays at the start of a block. -/
inductive SArr where
  /-- The cell of a name at the start. -/
  | cell (r : String)
  /-- The array `a` read at shape `(w, n)` with element `i` set to `v`. -/
  | aset (a : SArr) (w n : Nat) (i v : STerm)
  /-- The array of shape `(w, n)` whose elements are all zero. -/
  | zero (w n : Nat)
end

deriving instance DecidableEq, Hashable for STerm, SArr

/-- A symbolic zero flag. -/
inductive SFlag where
  /-- The flag at the start. -/
  | init
  /-- The flag a `CMP` of `x` and `y` at width `64` sets. -/
  | cmp (x y : STerm)
  deriving DecidableEq

/-- A guard: a condition on symbolic values under which a step succeeds. -/
inductive SG where
  /-- `t` has width `w`. -/
  | wid (t : STerm) (w : Nat)
  /-- `x` and `y` have one width. -/
  | eqW (x y : STerm)
  /-- `a` has shape `(w, n)`. -/
  | shp (a : SArr) (w n : Nat)
  deriving DecidableEq

section Eval

variable (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)

mutual
/-- The value of a symbolic word, for the start registers `V`, arrays `A`, carry flag `C`
    and overflow flag `O`. -/
def STerm.ev : STerm → Σ w, BitVec w
  | .reg r => V r
  | .immW w n => ⟨w, BitVec.ofNat w n⟩
  | .immAt n x => ⟨(x.ev).1, BitVec.ofNat _ n⟩
  | .bin m x y => ⟨(x.ev).1, binW (x.ev).1 m (x.ev).2 (extW y.ev (x.ev).1)⟩
  | .un m x => ⟨(x.ev).1, (applyOpnN (x.ev).1 m [(x.ev).2]).getD (x.ev).2⟩
  | .shImm m k x => ⟨(x.ev).1, (applyImmShiftN (x.ev).1 m k (x.ev).2).getD (x.ev).2⟩
  | .aget a w n i => ⟨w, stackGet (castA a.ev w n) (castW i.ev 64).toNat⟩
  | .cin ofl => ⟨1, BitVec.ofBool (if ofl then O else C)⟩
  | .aluF op ofl x y old =>
      if (x.ev).1 = 64 ∧ (y.ev).1 = 64 then
        ⟨1, BitVec.ofBool (aluBit op ofl (castW x.ev 64) (castW y.ev 64))⟩
      else old.ev
  | .carryW op x y c => ⟨64, carryWord op (castW x.ev 64) (castW y.ev 64) (bitOf c.ev)⟩
  | .carryF op ofl x y c =>
      ⟨1, BitVec.ofBool (carryBit op ofl (castW x.ev 64) (castW y.ev 64) (bitOf c.ev))⟩
  | .mulx hi x y =>
      ⟨64, if hi then (x86_MULX_lo_hi (castW x.ev 64) (castW y.ev 64)).2
        else (x86_MULX_lo_hi (castW x.ev 64) (castW y.ev 64)).1⟩
  | .cout sub x y c => ⟨1, coutBit sub x.ev y.ev c.ev⟩
  | .sel x y c =>
      ⟨(x.ev).1, JasminDialect.selectW (extW c.ev 1) (x.ev).2 (extW y.ev (x.ev).1)⟩
  | .setcc c x y => ⟨1, JasminDialect.cmpBit c (x.ev).2 (extW y.ev (x.ev).1)⟩
  | .ref _ => ⟨0, 0#0⟩

/-- The value of a symbolic array, for the start registers `V`, arrays `A` and flags `C`,
    `O`. -/
def SArr.ev : SArr → ArrCell
  | .cell r => A r
  | .aset a w n i v => ⟨w, n, stackSet (castA a.ev w n) (castW i.ev 64).toNat (castW v.ev w)⟩
  | .zero w n => ⟨w, n, fun _ => 0⟩
end

/-- The value of a symbolic flag, for the start registers `V`, arrays `A` and flag `Z`. -/
def SFlag.ev (Z : Bool) : SFlag → Bool
  | .init => Z
  | .cmp x y => castW (x.ev V A C O) 64 == castW (y.ev V A C O) 64

/-- A guard holds, for the start registers `V` and arrays `A`. -/
def SG.holds : SG → Prop
  | .wid t w => (t.ev V A C O).1 = w
  | .eqW x y => (x.ev V A C O).1 = (y.ev V A C O).1
  | .shp a w n => (a.ev V A C O).1 = w ∧ (a.ev V A C O).2.1 = n

/-- Every guard of a list holds. -/
def AllG (gs : List SG) : Prop := ∀ g ∈ gs, g.holds V A C O

end Eval

theorem allG_nil (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) :
    AllG V A C O [] := by
  simp [AllG]

theorem allG_append {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {gs hs : List SG} :
    AllG V A C O (gs ++ hs) ↔ AllG V A C O gs ∧ AllG V A C O hs := by
  simp only [AllG, List.mem_append]
  constructor
  · intro h; exact ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩
  · rintro ⟨h1, h2⟩ g (hg | hg)
    · exact h1 g hg
    · exact h2 g hg

/-! ### The normal form of a guard

A symbolic word shares its subterms, and the words of a long block are deep. A guard keeps
only the word that fixes the width it states (`STerm.wbase`), and a guard whose widths the
outermost constructors fix is decided (`SG.norm`), so the guards of a run stay small. -/

/-- The symbolic word whose width is the width of `t`: through the operations that keep the
    width of their first source. -/
def STerm.wbase : STerm → STerm
  | .immAt _ x => x.wbase
  | .bin _ x _ => x.wbase
  | .un _ x => x.wbase
  | .shImm _ _ x => x.wbase
  | .sel x _ _ => x.wbase
  | t => t

/-- The width of a symbolic word that its outermost constructor fixes. -/
def STerm.wknown : STerm → Option Nat
  | .immW w _ => some w
  | .aget _ w _ _ => some w
  | .cin _ => some 1
  | .carryW .. => some 64
  | .carryF .. => some 1
  | .mulx .. => some 64
  | .cout .. => some 1
  | .setcc .. => some 1
  | _ => none

theorem STerm.wbase_ev (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) :
    ∀ t : STerm, (t.wbase.ev V A C O).1 = (t.ev V A C O).1
  | .immAt _ x => by rw [STerm.wbase, STerm.wbase_ev V A C O x, STerm.ev]
  | .bin _ x _ => by rw [STerm.wbase, STerm.wbase_ev V A C O x, STerm.ev]
  | .un _ x => by rw [STerm.wbase, STerm.wbase_ev V A C O x, STerm.ev]
  | .shImm _ _ x => by rw [STerm.wbase, STerm.wbase_ev V A C O x, STerm.ev]
  | .sel x _ _ => by rw [STerm.wbase, STerm.wbase_ev V A C O x, STerm.ev]
  | .reg _ => rfl
  | .immW _ _ => rfl
  | .aget _ _ _ _ => rfl
  | .cin _ => rfl
  | .aluF _ _ _ _ _ => rfl
  | .carryW _ _ _ _ => rfl
  | .carryF _ _ _ _ _ => rfl
  | .mulx _ _ _ => rfl
  | .cout _ _ _ _ => rfl
  | .setcc _ _ _ => rfl
  | .ref _ => rfl

theorem STerm.wknown_ev (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    {t : STerm} {w : Nat} (h : t.wknown = some w) : (t.ev V A C O).1 = w := by
  cases t <;> simp only [STerm.wknown, Option.some.injEq, reduceCtorEq] at h <;>
    simp [STerm.ev, h]

/-- A guard that holds at no evaluation. -/
def SG.falseG : SG := .wid (.immW 0 0) 1

/-- The normal form of a guard: guards that hold exactly when it holds, over the width bases
    `STerm.wbase`, and none when the outermost constructors fix agreeing widths. -/
def SG.norm : SG → List SG
  | .wid t w =>
      match t.wbase.wknown with
      | some v => if v = w then [] else [SG.falseG]
      | none => [.wid t.wbase w]
  | .eqW x y =>
      match x.wbase.wknown, y.wbase.wknown with
      | some a, some b => if a = b then [] else [SG.falseG]
      | _, _ => [.eqW x.wbase y.wbase]
  | .shp a w n => [.shp a w n]

theorem SG.norm_iff (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (g : SG) : AllG V A C O g.norm ↔ g.holds V A C O := by
  cases g with
  | wid t w =>
      have hb := STerm.wbase_ev V A C O t
      simp only [SG.norm]
      cases hk : t.wbase.wknown with
      | some v =>
          have hv := STerm.wknown_ev V A C O hk
          by_cases e : v = w
          · simp [e, AllG, SG.holds, ← hb, hv]
          · simp [e, AllG, SG.holds, SG.falseG, STerm.ev, ← hb, hv]
      | none => simp [AllG, SG.holds, hb]
  | eqW x y =>
      have hx := STerm.wbase_ev V A C O x
      have hy := STerm.wbase_ev V A C O y
      simp only [SG.norm]
      cases kx : x.wbase.wknown with
      | some a =>
          cases ky : y.wbase.wknown with
          | some b =>
              have ha := STerm.wknown_ev V A C O kx
              have hb := STerm.wknown_ev V A C O ky
              by_cases e : a = b
              · simp [e, AllG, SG.holds, ← hx, ← hy, ha, hb]
              · simp [e, AllG, SG.holds, SG.falseG, STerm.ev, ← hx, ← hy, ha, hb]
          | none => simp [AllG, SG.holds, hx, hy]
      | none => simp [AllG, SG.holds, hx, hy]
  | shp a w n => simp [SG.norm, AllG]

/-- The normal form of a list of guards. -/
def normG (gs : List SG) : List SG := gs.flatMap SG.norm

@[simp] theorem normG_nil : normG [] = [] := rfl

theorem allG_normG {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {gs : List SG} : AllG V A C O (normG gs) ↔ AllG V A C O gs := by
  induction gs with
  | nil => simp [normG, AllG]
  | cons g gs ih =>
      rw [show normG (g :: gs) = g.norm ++ normG gs from rfl, allG_append, ih,
        SG.norm_iff]
      simp [AllG]

/-! ## 3. Symbolic states -/

/-- A finite map from register names to symbolic words. -/
abbrev RegMap := Std.TreeMap String STerm compare

/-- The symbolic word of register `r` in `m`: its entry, or `reg r` when it has none. -/
def RegMap.rd (m : RegMap) (r : String) : STerm := m.getD r (.reg r)

theorem RegMap.rd_insert (m : RegMap) (d r : String) (t : STerm) :
    RegMap.rd (m.insert d t) r = if r = d then t else RegMap.rd m r := by
  simp only [RegMap.rd, Std.TreeMap.getD_insert, Std.compare_eq_iff_eq]
  by_cases h : r = d
  · subst h; simp
  · simp [h, Ne.symm h]

/-- Two register maps are equivalent when they read the same word at every register. -/
instance RegMap.setoid : Setoid RegMap where
  r m₁ m₂ := ∀ r, RegMap.rd m₁ r = RegMap.rd m₂ r
  iseqv := ⟨fun _ _ => rfl, fun h r => (h r).symm, fun h₁ h₂ r => (h₁ r).trans (h₂ r)⟩

/-- A symbolic register file: a register map up to equality of reads. Equality of register
    files is equality of their reads (`RegFile.ext`). -/
def RegFile := Quotient RegMap.setoid

/-- The register file reading `reg r` at every register `r`. -/
def RegFile.empty : RegFile := Quotient.mk _ ∅

/-- The symbolic word of register `r` in `f`. -/
def RegFile.get (f : RegFile) (r : String) : STerm :=
  Quotient.liftOn f (RegMap.rd · r) (fun _ _ h => h r)

/-- `f` with register `d` set to `t`. -/
def RegFile.set (f : RegFile) (d : String) (t : STerm) : RegFile :=
  Quotient.liftOn f (fun m => Quotient.mk _ (m.insert d t)) (fun _ _ h =>
    Quotient.sound fun r => by simp only [RegMap.rd_insert, h r])

@[simp] theorem RegFile.get_empty (r : String) : RegFile.empty.get r = .reg r := rfl

theorem RegFile.get_set (f : RegFile) (d r : String) (t : STerm) :
    (f.set d t).get r = if r = d then t else f.get r :=
  Quotient.inductionOn f fun m => RegMap.rd_insert m d r t

theorem RegFile.ext {f g : RegFile} (h : ∀ r, f.get r = g.get r) : f = g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  exact Quotient.sound h

/-- A symbolic state: a symbolic register file, a symbolic array per name, the symbolic
    zero flag, the registers and names written with the number of registers written, and
    the symbolic carry and overflow flags as words of width `1`. -/
structure SSt where
  /-- The symbolic register file. -/
  rf : RegFile
  /-- The symbolic array of each name. -/
  arrs : String → SArr
  /-- The symbolic zero flag. -/
  zf : SFlag
  /-- The registers written. -/
  wr : List String
  /-- The array names written. -/
  awr : List String
  /-- The symbolic carry flag. -/
  cf : STerm
  /-- The symbolic overflow flag. -/
  of : STerm
  /-- The number of registers written. -/
  nwr : Nat := wr.length
  /-- `nwr` is the length of `wr`. -/
  nwr_eq : nwr = wr.length := by rfl

/-- The symbolic word of each register. -/
def SSt.regs (ss : SSt) (r : String) : STerm := ss.rf.get r

/-- The symbolic state at the start of a block. -/
def SSt.start : SSt :=
  { rf := .empty, arrs := SArr.cell, zf := .init, wr := [], awr := [], cf := .cin false,
    of := .cin true }

/-- `ss` with register `d` set to `t`. -/
def SSt.setR (ss : SSt) (d : String) (t : STerm) : SSt :=
  { ss with rf := ss.rf.set d t, wr := d :: ss.wr, nwr := ss.nwr + 1,
            nwr_eq := by simp [ss.nwr_eq] }

theorem SSt.setR_regs (ss : SSt) (d : String) (t : STerm) (r : String) :
    (ss.setR d t).regs r = if r = d then t else ss.regs r :=
  RegFile.get_set _ _ _ _

/-- The registers `ss1` records as written beyond those `ss` records. -/
def SSt.newWr (ss1 ss : SSt) : List String := ss1.wr.take (ss1.nwr - ss.nwr)

theorem SSt.newWr_eq (ss1 ss : SSt) :
    ss1.newWr ss = ss1.wr.take (ss1.wr.length - ss.wr.length) := by
  rw [SSt.newWr, ss1.nwr_eq, ss.nwr_eq]

/-- `ss` with register `d` set to `t`, the written registers unchanged. -/
def SSt.putR (ss : SSt) (d : String) (t : STerm) : SSt := { ss with rf := ss.rf.set d t }

theorem SSt.putR_regs (ss : SSt) (d : String) (t : STerm) (r : String) :
    (ss.putR d t).regs r = if r = d then t else ss.regs r :=
  RegFile.get_set _ _ _ _

@[simp] theorem SSt.start_regs (r : String) : SSt.start.regs r = .reg r := rfl

@[simp] theorem SSt.rf_get (ss : SSt) (r : String) : ss.rf.get r = ss.regs r := rfl

@[simp] theorem SSt.regs_mk (f : RegFile) (a : String → SArr) (z : SFlag) (w aw : List String)
    (c o : STerm) (n : Nat) (h : n = w.length) (r : String) :
    (SSt.mk f a z w aw c o n h).regs r = f.get r := rfl

attribute [simp] RegFile.get_set

theorem SSt.ext {s t : SSt} (hr : ∀ r, s.regs r = t.regs r) (ha : s.arrs = t.arrs)
    (hz : s.zf = t.zf) (hw : s.wr = t.wr) (haw : s.awr = t.awr) (hc : s.cf = t.cf)
    (ho : s.of = t.of) : s = t := by
  obtain ⟨rf, arrs, zf, wr, awr, cf, of, n, hn⟩ := s
  obtain ⟨rf', arrs', zf', wr', awr', cf', of', n', hn'⟩ := t
  have hrf : rf = rf' := RegFile.ext hr
  simp only at ha hz hw haw hc ho
  subst hrf ha hz hw haw hc ho
  have : n = n' := hn.trans hn'.symm
  subst this
  rfl

/-- `ss` with array name `d` set to `a`. -/
def SSt.setA (ss : SSt) (d : String) (a : SArr) : SSt :=
  { ss with arrs := fun r => if r = d then a else ss.arrs r, awr := d :: ss.awr }

/-- Every register and array name not written holds its start value. -/
def SSt.Good (ss : SSt) : Prop :=
  (∀ r, r ∉ ss.wr → ss.regs r = .reg r) ∧ (∀ r, r ∉ ss.awr → ss.arrs r = .cell r)

theorem SSt.good_start : SSt.start.Good := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem SSt.Good.setR {ss : SSt} (h : ss.Good) (d : String) (t : STerm) :
    (ss.setR d t).Good := by
  refine ⟨fun r hr => ?_, h.2⟩
  simp only [SSt.setR, List.mem_cons, not_or] at hr
  rw [SSt.setR_regs, ite_eq_right hr.1]
  exact h.1 r hr.2

theorem SSt.Good.setA {ss : SSt} (h : ss.Good) (d : String) (a : SArr) :
    (ss.setA d a).Good := by
  refine ⟨h.1, fun r hr => ?_⟩
  simp only [SSt.setA, List.mem_cons, not_or] at hr ⊢
  rw [ite_eq_right hr.1]
  exact h.2 r hr.2

/-- A flag-machine state is described by a symbolic state, for the start registers `V`,
    arrays `A` and flags `C`, `O`, `Z`. -/
def Holds (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) (Z : Bool)
    (ss : SSt) (s : LstateMF) : Prop :=
  (∀ q, s.prog.base.reg.lvm q = (ss.regs q).ev V A C O) ∧
    (∀ q, s.prog.base.larr q = (ss.arrs q).ev V A C O) ∧ s.zf = ss.zf.ev V A C O Z ∧
    s.prog.base.cf = bitOf (ss.cf.ev V A C O) ∧ s.prog.base.of = bitOf (ss.of.ev V A C O)

theorem holds_start (s : LstateMF) :
    Holds s.prog.base.reg.lvm s.prog.base.larr s.prog.base.cf s.prog.base.of s.zf SSt.start s :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, by simp [SSt.start, STerm.ev],
    by simp [SSt.start, STerm.ev]⟩

/-! ## 4. The register-file layers -/

/-- The symbolic description of a register-file step: a write of `t` to `d` under the
    guards `gs`, a step that only advances the pc, a step that always fails, or an
    instruction outside the fragment. -/
inductive ROut where
  | set (d : String) (t : STerm) (gs : List SG)
  | nop
  | fail
  | unk

/-- `o` describes the register-file step `f` from the register file `r`, for the start
    registers `V` and arrays `A`. -/
def ROut.Desc (f : LstateN → Option LstateN) (V : String → Σ w, BitVec w)
    (A : String → ArrCell) (C O : Bool) (r : LstateN) : ROut → Prop
  | .set d t gs =>
      (∀ r', f r = some r' → AllG V A C O gs ∧ r' = (r.setReg d (t.ev V A C O).2).nextPc) ∧
        (AllG V A C O gs → (f r).isSome)
  | .nop => f r = some r.nextPc
  | .fail => f r = none
  | .unk => True

/-- `o` describes the register-file step `f` exactly from every register file the
    symbolic registers `R` describe. -/
def RSound (f : LstateN → Option LstateN) (R : String → STerm) (o : ROut) : Prop :=
  ∀ (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) (r : LstateN),
    (∀ q, r.lvm q = (R q).ev V A C O) →
    o.Desc f V A C O r

/-- The two-source mnemonics of `applyOpnN`. -/
def binOk (m : String) : Bool :=
  m == "ADD" || m == "SUB" || m == "MUL" || m == "AND" || m == "OR" || m == "XOR" ||
    m == "SHL" || m == "SHR" || m == "ANDN"

/-- The mnemonics of `applyImmShiftN`. -/
def shOk (m : String) : Bool := m == "SAR" || m == "SHL" || m == "SHR" || m == "ROR"

theorem applyOpnN_bin_some {w : Nat} {m : String} (h : binOk m = true) (a b : BitVec w) :
    (applyOpnN w m [a, b]).isSome := by
  simp only [binOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) <;> subst h <;> rfl

theorem applyOpnN_bin_none {w : Nat} {m : String} (h : binOk m = false) (a b : BitVec w) :
    applyOpnN w m [a, b] = none := by
  simp only [binOk, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  unfold applyOpnN
  split <;> simp_all

theorem binW_of_binOk {w : Nat} {m : String} (h : binOk m = true) (a b : BitVec w) :
    binW w m a b = (applyOpnN w m [a, b]).getD a := by
  have hm : m ≠ "MULXHI" := by
    rintro rfl
    exact absurd h (by decide)
  simp [binW, hm]

theorem applyImmShiftN_zero {w : Nat} {m : String} (h : shOk m = true) (a : BitVec w) :
    applyImmShiftN w m 0 a = some a := by
  simp only [shOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h <;> subst h <;>
    simp [applyImmShiftN, applyOpnN, BitVec.rotateRight, BitVec.rotateRightAux]

theorem applyImmShiftN_some {w : Nat} {m : String} (h : shOk m = true) (k : Nat) (a : BitVec w) :
    (applyImmShiftN w m k a).isSome := by
  simp only [shOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h <;> subst h <;> simp [applyImmShiftN, applyOpnN]

theorem applyImmShiftN_none {w : Nat} {m : String} (h : shOk m = false) (k : Nat)
    (a : BitVec w) : applyImmShiftN w m k a = none := by
  simp only [shOk, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  simp [applyImmShiftN, h.1.1.1, h.1.1.2, h.1.2, h.2]

/-- The sources of the register operation `opn d, [a, b]` are described in exchanged order:
    the base of `opn` is commutative (`TwoAddrLegalize.commBases`), `b` is the destination and
    `a` is not. The order is decided on the names alone. -/
def commSwap (opn d a b : String) : Bool :=
  TwoAddrLegalize.commBases.contains (stripWidthTag opn) && b == d && a != d

/-- The two-source operation `m` of `binW` applies to exchanged sources with the same
    result, for `m` a commutative base. -/
theorem binW_comm {w : Nat} {m : String} (hm : TwoAddrLegalize.commBases.contains m = true)
    (a b : BitVec w) : binW w m a b = binW w m b a := by
  simp only [TwoAddrLegalize.commBases, List.contains_iff_mem, List.mem_cons,
    List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    simp [binW, applyOpnN, BitVec.add_comm, BitVec.mul_comm, BitVec.and_comm, BitVec.or_comm,
      BitVec.xor_comm]

/-- The register description of a two-source operation on terms of one width does not
    depend on the order of the sources, for a commutative base `m`. -/
theorem desc_bin_swap {f : LstateN → Option LstateN} {V : String → Σ w, BitVec w}
    {A : String → ArrCell} {C O : Bool} {r : LstateN} {m d : String} {x y : STerm}
    (hm : TwoAddrLegalize.commBases.contains m = true)
    (h : ROut.Desc f V A C O r (.set d (.bin m x y) [.eqW x y])) :
    ROut.Desc f V A C O r (.set d (.bin m y x) [.eqW y x]) := by
  have hg : AllG V A C O [.eqW x y] ↔ AllG V A C O [.eqW y x] := by
    simp only [AllG, List.mem_singleton, forall_eq, SG.holds]
    exact ⟨Eq.symm, Eq.symm⟩
  have he : AllG V A C O [.eqW x y] →
      (STerm.bin m x y).ev V A C O = (STerm.bin m y x).ev V A C O := by
    simp only [AllG, List.mem_singleton, forall_eq, SG.holds, STerm.ev]
    generalize x.ev V A C O = p
    generalize y.ev V A C O = q
    obtain ⟨w, a⟩ := p
    obtain ⟨w', b⟩ := q
    rintro (rfl : w = w')
    simp [extW, binW_comm hm]
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun r' hr' => ?_, fun g => h2 (hg.mpr g)⟩
  obtain ⟨g, e⟩ := h1 r' hr'
  exact ⟨hg.mp g, by rw [e, he g]⟩

/-- The symbolic description of `lsemStepN`. A two-source operation with an immediate `n`
    below `2 ^ w`, for the width `w` of its mnemonic's tag, is described with the second
    source `immW w n`, the term of a move of `n` into a register, so an operation on a
    register that holds a moved constant and the operation on the immediate have one term.
    A count-in-name shift `SHL:k`/`SHR:k` with `k` below `2 ^ w` has the term of the shift by
    the immediate `k`, so the three spellings of one shift (count in the name, immediate
    count, count in a register holding a moved constant) have one term; a count-in-name
    `SAR:k` is the immediate-shift term `shImm`. A shift by the count `0` in the name or as
    an immediate is described as the copy of its source, the term of a register `MOV`. A commutative operation `opn d, [a, d]` with `a ≠ d`
    is described with its sources exchanged (`commSwap`), so it has the term of
    `opn d, [d, a]`. A two-source operation `opn d, [imm n, b]` with an immediate first
    source and a register `b` is the term `bin opn (immW w n) b` at the width `w` of the
    mnemonic's tag, under the guard that `b` has width `w`. A select `CMOV d, [c, a, b]` with register condition `c` and register
    first value `a` is the term `sel a b c`, under the guards that `c` has width `1` and, for
    a register `b`, that `a` and `b` have one width; an immediate `b` is `immAt n a`; a select
    whose first value is an immediate fails. A comparison `SET<cc> d, [a, b]` (`cmpOfName?`)
    with a register `a` is the term `setcc cc a b`, under the guard, for a register `b`, that
    `a` and `b` have one width; an immediate `b` is described as the immediate second source
    of a two-source operation. A load-effective-address `LEA d, [b + x · sc]` is the term `b + x · sc` at width `64`,
    under the guards that `b` and `x` have width `64`. A narrow buffer move `MOV:8 d, [a]` or
    `MOV:16 d, [a]`, the load or store of a byte or halfword cell, is the term
    `a &&& narrowMask opn` at the width of `a`, `bin "AND" a (immAt (narrowMask opn) a)`. -/
def symN (x : LinstrR) (R : String → STerm) : ROut :=
  match x with
  | .Lopn [.reg dst] opn [c, a, b] =>
      if stripWidthTag opn = "CMOV" then
        match c, a, b with
        | .reg rc, .reg ra, .reg rb =>
            .set dst (.sel (R ra) (R rb) (R rc)) [.wid (R rc) 1, .eqW (R ra) (R rb)]
        | .reg rc, .reg ra, .imm n => .set dst (.sel (R ra) (.immAt n (R ra)) (R rc)) [.wid (R rc) 1]
        | _, .imm _, _ => .fail
        | _, _, _ => .unk
      else .fail
  | .Lopn [.reg dst] opn [a, b] =>
      match a with
      | .reg ra =>
          if binOk (stripWidthTag opn) then
            match b with
            | .reg rb =>
                if commSwap opn dst ra rb then
                  .set dst (.bin (stripWidthTag opn) (R rb) (R ra)) [.eqW (R rb) (R ra)]
                else .set dst (.bin (stripWidthTag opn) (R ra) (R rb)) [.eqW (R ra) (R rb)]
            | .imm n =>
                if (stripWidthTag opn = "SHL" ∨ stripWidthTag opn = "SHR") ∧ n = 0 then
                  .set dst (R ra) []
                else if n < 2 ^ widthFromTag opn then
                  .set dst (.bin (stripWidthTag opn) (R ra) (.immW (widthFromTag opn) n)) []
                else .set dst (.bin (stripWidthTag opn) (R ra) (.immAt n (R ra))) []
            | _ => .fail
          else if (cmpOfName? (stripWidthTag opn)).isSome then
            match b with
            | .reg rb =>
                .set dst (.setcc ((cmpOfName? (stripWidthTag opn)).getD .eq) (R ra) (R rb))
                  [.eqW (R ra) (R rb)]
            | .imm n =>
                if n < 2 ^ widthFromTag opn then
                  .set dst (.setcc ((cmpOfName? (stripWidthTag opn)).getD .eq) (R ra)
                    (.immW (widthFromTag opn) n)) []
                else
                  .set dst (.setcc ((cmpOfName? (stripWidthTag opn)).getD .eq) (R ra)
                    (.immAt n (R ra))) []
            | _ => .fail
          else .fail
      | .imm n =>
          if binOk (stripWidthTag opn) then
            match b with
            | .reg rb =>
                .set dst (.bin (stripWidthTag opn) (.immW (widthFromTag opn) n) (R rb))
                  [.wid (R rb) (widthFromTag opn)]
            | _ => .unk
          else .fail
      | _ => .fail
  | .Lopn [.reg dst] opn [.imm n] =>
      if stripWidthTag opn = "MOV" then .set dst (.immW (widthFromTag opn) n) [] else .fail
  | .Lopn [.reg dst] opn [.reg a] =>
      if stripWidthTag opn = "NEG" then .set dst (.un "NEG" (R a)) []
      else if stripWidthTag opn = "MOV" then .set dst (R a) []
      else
        match immShiftMnem? opn with
        | some (m, k) =>
            if shOk m then
              if k = 0 then .set dst (R a) []
              else if (m = "SHL" ∨ m = "SHR") ∧ k < 2 ^ widthFromTag opn then
                .set dst (.bin m (R a) (.immW (widthFromTag opn) k)) []
              else .set dst (.shImm m k (R a)) []
            else .fail
        | none =>
            if opn = "MOV:8" ∨ opn = "MOV:16" then
              .set dst (.bin "AND" (R a) (.immAt (narrowMask opn) (R a))) []
            else .fail
  | .Lopn [.reg dst] opn [.arrIdx b x sc] =>
      if stripWidthTag opn = "LEA" then
        .set dst (.bin "ADD" (R b) (.bin "MUL" (R x) (.immW 64 sc))) [.wid (R b) 64, .wid (R x) 64]
      else .fail
  | .Lopn _ _ _ => .fail
  | .Lalign => .nop
  | .Llabel _ _ => .nop
  | _ => .fail

theorem readReg_reg (r : LstateN) (a : String) : readReg r (.reg a) = some (r.lvm a) := rfl

/-- A mnemonic of `binOk` is no comparison mnemonic. -/
theorem cmpOfName?_of_binOk {m : String} (h : binOk m = true) : cmpOfName? m = none := by
  simp only [binOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) <;> rfl

theorem stepN_bin_reg (r : LstateN) (dst opn ra rb : String)
    (hc : cmpOfName? (stripWidthTag opn) = none) :
    lsemStepN (.Lopn [.reg dst] opn [.reg ra, .reg rb]) r =
      if (r.lvm rb).1 = (r.lvm ra).1 then
        (applyOpnN (r.lvm ra).1 (stripWidthTag opn) [(r.lvm ra).2, castW (r.lvm rb) (r.lvm ra).1]).map
          (fun v => (r.setReg dst v).nextPc)
      else none := by
  simp only [lsemStepN, readReg_reg, evalOperandN, getW_eq]
  split_ifs
  · simp only []
    cases applyOpnN _ _ _ <;> simp [hc]
  · rfl

theorem stepN_bin_imm (r : LstateN) (dst opn ra : String) (n : Nat)
    (hc : cmpOfName? (stripWidthTag opn) = none) :
    lsemStepN (.Lopn [.reg dst] opn [.reg ra, .imm n]) r =
      (applyOpnN (r.lvm ra).1 (stripWidthTag opn) [(r.lvm ra).2, BitVec.ofNat _ n]).map
        (fun v => (r.setReg dst v).nextPc) := by
  simp only [lsemStepN, readReg_reg, evalOperandN]
  cases applyOpnN _ _ _ <;> simp [hc]

@[simp] theorem castW_mk {w : Nat} (v : BitVec w) : castW ⟨w, v⟩ w = v := by
  simp [castW]

theorem stepN_lea (r : LstateN) (dst opn b x : String) (sc : Nat)
    (h : stripWidthTag opn = "LEA") :
    lsemStepN (.Lopn [.reg dst] opn [.arrIdx b x sc]) r =
      if (r.lvm b).1 = 64 ∧ (r.lvm x).1 = 64 then
        some ((r.setReg dst (castW (r.lvm b) 64
          + BitVec.ofNat 64 (sc * (castW (r.lvm x) 64).toNat))).nextPc)
      else none := by
  simp only [lsemStepN, h, ite_true, getW_eq]
  by_cases hb : (r.lvm b).1 = 64 <;> by_cases hx : (r.lvm x).1 = 64 <;> simp [hb, hx]

/-- The effective address `sc · x` of a scaled index is the product of the index word and
    the scale at width `64`. -/
theorem ofNat_mul_toNat (sc : Nat) (v : BitVec 64) :
    BitVec.ofNat 64 (sc * v.toNat) = v * BitVec.ofNat 64 sc := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_mod, Nat.mul_comm]

theorem symN_sound (x : LinstrR) (R : String → STerm) : RSound (lsemStepN x) R (symN x R) := by
  intro V A C O r hr
  unfold symN
  split
  · split_ifs with h
    · split
      · rename_i rc ra rb
        simp only [ROut.Desc, lsemStepN, h, ite_true, operandName, readReg_reg, evalOperandN,
          getW_eq, hr rc, hr ra, hr rb, AllG, List.mem_cons, forall_eq_or_imp, SG.holds,
          STerm.ev]
        generalize STerm.ev V A C O (R ra) = pa
        generalize STerm.ev V A C O (R rb) = pb
        generalize STerm.ev V A C O (R rc) = pc
        obtain ⟨wa, va⟩ := pa
        obtain ⟨wb, vb⟩ := pb
        obtain ⟨wc, vc⟩ := pc
        by_cases hc : wc = 1
        · subst hc
          by_cases hb : wb = wa
          · subst hb
            simp [extW]
          · simp [hb, Ne.symm hb]
        · simp [hc]
      · rename_i rc ra n
        simp only [ROut.Desc, lsemStepN, h, ite_true, operandName, readReg_reg, evalOperandN,
          getW_eq, hr rc, hr ra, AllG, List.mem_cons, forall_eq_or_imp, SG.holds, STerm.ev]
        generalize STerm.ev V A C O (R ra) = pa
        generalize STerm.ev V A C O (R rc) = pc
        obtain ⟨wa, va⟩ := pa
        obtain ⟨wc, vc⟩ := pc
        by_cases hc : wc = 1
        · subst hc
          simp [extW]
        · simp [hc]
      · simp [ROut.Desc, lsemStepN, h, readReg]
      · trivial
    · simp [ROut.Desc, lsemStepN, h]
  · rename_i dst opn a b
    split
    · rename_i ra
      by_cases hb : binOk (stripWidthTag opn) = true
      · rw [ite_eq_left hb]
        split
        · rename_i rb
          have key : ROut.Desc (lsemStepN (.Lopn [.reg dst] opn [.reg ra, .reg rb])) V A C O r
              (.set dst (.bin (stripWidthTag opn) (R ra) (R rb)) [.eqW (R ra) (R rb)]) := by
            simp only [ROut.Desc]
            rw [stepN_bin_reg _ _ _ _ _ (cmpOfName?_of_binOk hb), hr ra, hr rb]
            obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (applyOpnN_bin_some hb
              ((R ra).ev V A C O).2 (castW ((R rb).ev V A C O) ((R ra).ev V A C O).1))
            simp only [AllG, List.mem_singleton, forall_eq, SG.holds, STerm.ev,
              binW_of_binOk hb, hv]
            split_ifs with hw
            · simp [hw, extW_of_eq hw, hv]
            · simp [Ne.symm hw]
          split_ifs with hs
          · simp only [commSwap, Bool.and_eq_true] at hs
            exact desc_bin_swap hs.1.1 key
          · exact key
        · rename_i n
          simp only [ROut.Desc]
          rw [stepN_bin_imm _ _ _ _ _ (cmpOfName?_of_binOk hb), hr ra]
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (applyOpnN_bin_some hb
            ((R ra).ev V A C O).2 (BitVec.ofNat ((R ra).ev V A C O).1 n))
          split_ifs with hs
          · obtain ⟨hs, hz⟩ := hs
            subst hz
            have h0 : ∀ {w : Nat} (x : BitVec w),
                applyOpnN w (stripWidthTag opn) [x, BitVec.ofNat w 0] = some x := by
              intro w x
              rcases hs with hs | hs <;> simp [hs, applyOpnN]
            simp [AllG, h0]
          · rename_i hlt
            simp [AllG, STerm.ev, binW_of_binOk hb, extW_ofNat hlt, hv]
          · simp [AllG, STerm.ev, binW_of_binOk hb, extW_of_eq, hv]
        · rename_i hb1 hb2
          cases b with
          | reg rb => exact absurd rfl (hb1 rb)
          | imm n => exact absurd rfl (hb2 n)
          | arr _ _ => simp [ROut.Desc, lsemStepN, readReg, evalOperandN]
          | arrIdx _ _ _ => simp [ROut.Desc, lsemStepN, readReg, evalOperandN]
      · rw [ite_eq_right hb]
        have hn : ∀ {w : Nat} (x y : BitVec w), applyOpnN w (stripWidthTag opn) [x, y] = none :=
          fun x y => applyOpnN_bin_none (Bool.eq_false_iff.mpr hb) x y
        cases hc : cmpOfName? (stripWidthTag opn) with
        | some c =>
          simp only [Option.isSome_some, ite_true, Option.getD_some]
          cases b with
          | reg rb =>
            simp only [ROut.Desc, lsemStepN, readReg_reg, evalOperandN, getW_eq, hn, hc, hr ra,
              hr rb, AllG, List.mem_singleton, forall_eq, SG.holds, STerm.ev]
            generalize STerm.ev V A C O (R ra) = pa
            generalize STerm.ev V A C O (R rb) = pb
            obtain ⟨wa, va⟩ := pa
            obtain ⟨wb, vb⟩ := pb
            by_cases hw : wb = wa
            · subst hw
              simp [extW]
            · simp [hw, Ne.symm hw]
          | imm n =>
            dsimp only
            split_ifs with hlt
            · simp only [ROut.Desc, lsemStepN, readReg_reg, evalOperandN, hn, hc, hr ra,
                STerm.ev, extW_ofNat hlt]
              simp [AllG]
            · simp only [ROut.Desc, lsemStepN, readReg_reg, evalOperandN, hn, hc, hr ra, STerm.ev]
              generalize STerm.ev V A C O (R ra) = pa
              obtain ⟨wa, va⟩ := pa
              simp [AllG, extW]
          | _ => simp [ROut.Desc, lsemStepN, evalOperandN, readReg]
        | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ite_false, ROut.Desc]
        cases b with
        | reg rb => rw [stepN_bin_reg _ _ _ _ _ hc, hn]; simp
        | imm n => rw [stepN_bin_imm _ _ _ _ _ hc, hn]; simp
        | _ => simp [lsemStepN, evalOperandN, readReg]
    · rename_i n
      by_cases hb : binOk (stripWidthTag opn) = true
      · rw [ite_eq_left hb]
        split
        · rename_i rb
          simp only [ROut.Desc, lsemStepN_immFirst, immFirstN, evalOperandN, getW_eq, hr rb]
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (applyOpnN_bin_some hb
            (BitVec.ofNat (widthFromTag opn) n) (castW ((R rb).ev V A C O) (widthFromTag opn)))
          simp only [AllG, List.mem_singleton, forall_eq, SG.holds, STerm.ev, binW_of_binOk hb]
          split_ifs with hw
          · simp [extW_of_eq hw, hv, hw]
          · simp [hw]
        · trivial
      · rw [ite_eq_right hb]
        simp only [ROut.Desc, lsemStepN_immFirst, immFirstN]
        split
        · rw [applyOpnN_bin_none (Bool.eq_false_iff.mpr hb)]; rfl
        · rfl
    · rename_i ha hi
      cases a with
      | reg ra => exact absurd rfl (ha ra)
      | imm n => exact absurd rfl (hi n)
      | _ => simp [ROut.Desc, lsemStepN, readReg]
  · split_ifs with h
    · simp [ROut.Desc, lsemStepN, h, AllG, STerm.ev]
    · simp [ROut.Desc, lsemStepN, h]
  · rename_i dst opn a
    split_ifs with h1 h2 hk
    · simp [ROut.Desc, lsemStepN, h1, readReg, hr a, AllG, STerm.ev, applyOpnN]
    · simp [ROut.Desc, lsemStepN, h2, readReg, hr a, AllG, applyOpnN]
    · have hn : immShiftMnem? opn = none := by rcases hk with rfl | rfl <;> decide +kernel
      split
      · rename_i m k hm
        rw [hn] at hm
        cases hm
      · simp only [ROut.Desc]
        rw [lsemStepN_narrow r dst opn a hk, hr a]
        simp [AllG, STerm.ev, binW_of_binOk (show binOk "AND" = true from rfl), extW, applyOpnN]
    · split
      · rename_i m k hm
        split_ifs with hs hz hsl
        · subst hz
          simp [ROut.Desc, lsemStepN, h1, h2, hm, readReg, hr a, applyImmShiftN_zero hs, AllG]
        · obtain ⟨hsl, hlt⟩ := hsl
          have hb : binOk m = true := by rcases hsl with rfl | rfl <;> rfl
          have he : ∀ {w : Nat} (x : BitVec w), applyImmShiftN w m k x =
              applyOpnN w m [x, BitVec.ofNat w k] := by
            intro w x
            unfold applyImmShiftN
            rcases hsl with rfl | rfl <;> simp
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
            (applyImmShiftN_some hs k ((R a).ev V A C O).2)
          simp [ROut.Desc, lsemStepN, h1, h2, hm, readReg, hr a, hv, AllG, STerm.ev,
            binW_of_binOk hb, extW_ofNat hlt, ← he]
        · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
            (applyImmShiftN_some hs k ((R a).ev V A C O).2)
          simp [ROut.Desc, lsemStepN, h1, h2, hm, readReg, hr a, hv, AllG, STerm.ev]
        · simp [ROut.Desc, lsemStepN, h1, h2, hm, readReg,
            applyImmShiftN_none (Bool.eq_false_iff.mpr hs)]
      · rename_i hm
        simp [ROut.Desc, lsemStepN, h1, h2, hm, hk]
  · rename_i dst opn b x sc
    split_ifs with h
    · simp only [ROut.Desc]
      rw [stepN_lea r dst opn b x sc h, hr b, hr x]
      simp only [AllG, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
        SG.holds, STerm.ev]
      generalize STerm.ev V A C O (R b) = pb
      generalize STerm.ev V A C O (R x) = px
      obtain ⟨wb, vb⟩ := pb
      obtain ⟨wx, vx⟩ := px
      by_cases hb : wb = 64
      · subst hb
        by_cases hx : wx = 64
        · subst hx
          simp [extW, binW, applyOpnN, ofNat_mul_toNat]
        · simp [hx]
      · simp [hb]
    · simp [ROut.Desc, lsemStepN, h]
  · rename_i hA hB hC hD hE
    simp only [ROut.Desc]
    unfold lsemStepN
    split
    · rename_i heq
      injection heq with h1 _ h3
      exact (hA _ _ _ _ h1 h3).elim
    · rename_i heq
      injection heq with h1 _ h3
      exact (hB _ _ _ h1 h3).elim
    · rename_i heq
      injection heq with h1 _ h3
      exact (hC _ _ h1 h3).elim
    · rename_i heq
      injection heq with h1 _ h3
      exact (hD _ _ h1 h3).elim
    · rename_i heq
      injection heq with h1 _ h3
      exact (hE _ _ _ _ h1 h3).elim
    all_goals first | rfl | (rename_i heq; cases heq)
  · rfl
  · rfl
  · rename_i hA hB hC hD hE hF hG hH
    simp only [ROut.Desc]
    unfold lsemStepN
    split
    · exact (hA _ _ _ _ _ rfl).elim
    · exact (hB _ _ _ _ rfl).elim
    · exact (hC _ _ _ rfl).elim
    · exact (hD _ _ _ rfl).elim
    · exact (hE _ _ _ _ _ rfl).elim
    · exact (hF _ _ _ rfl).elim
    · exact (hG rfl).elim
    · exact (hH _ _ rfl).elim
    all_goals rfl

/-- The symbolic description of `lsemStepSh`: the structured `SAR d, [s, imm n]` is the
    immediate-shift term `shImm "SAR" n` of its source, the term of the count-in-name
    `SAR:n` with `n` positive. -/
def symSh (x : LinstrR) (R : String → STerm) : ROut :=
  match sarStruct? x with
  | some (d, s, n) => .set d (.shImm "SAR" n (R s)) []
  | none => symN x R

theorem symSh_sound (x : LinstrR) (R : String → STerm) : RSound (lsemStepSh x) R (symSh x R) := by
  intro V A C O r hr
  unfold symSh
  split
  · rename_i d s n h
    have hstep : lsemStepSh x r
        = some ((r.setReg d (BitVec.sshiftRight (r.lvm s).2 (shiftMask (r.lvm s).1 n))).nextPc) := by
      simp only [lsemStepSh, h, readReg_reg]
    refine ⟨fun r' h' => ?_, fun _ => by simp [hstep]⟩
    rw [hstep] at h'
    refine ⟨fun g hg => by simp at hg, ?_⟩
    rw [← Option.some.inj h', hr s]
    simp [STerm.ev, applyImmShiftN]
  · rename_i h
    have := symN_sound x R V A C O r hr
    simpa only [ROut.Desc, lsemStepSh_of_not_sar x r h] using this

/-- The symbolic description of `lsemStepMC`: the high word `MULXHI d, a, b` of a product is
    the term `bin "MULXHI"` under the guard that `a` and `b` have one width. A register-carry
    step `ADCX`/`SBB d, a, b, c` is the sum `(a + b) + c` (the difference `(a - b) - c`) at the
    width of `a`, and `ADCXHI`/`SBBHI d, a, b, c` is the carry-out (borrow-out) bit `cout`;
    each under the guards that `a` and `b` have one width and the carry-in `c` has width
    `1`. -/
def symMC (x : LinstrR) (R : String → STerm) : ROut :=
  match mulhiStruct? x with
  | some (d, a, b) => .set d (.bin "MULXHI" (R a) (R b)) [.eqW (R a) (R b)]
  | none =>
  match adcxStruct? x with
  | some (d, a, b, c) =>
      .set d (.bin "ADD" (.bin "ADD" (R a) (R b)) (R c)) [.eqW (R a) (R b), .wid (R c) 1]
  | none =>
  match adcxhiStruct? x with
  | some (d, a, b, c) => .set d (.cout false (R a) (R b) (R c)) [.eqW (R a) (R b), .wid (R c) 1]
  | none =>
  match sbbStruct? x with
  | some (d, a, b, c) =>
      .set d (.bin "SUB" (.bin "SUB" (R a) (R b)) (R c)) [.eqW (R a) (R b), .wid (R c) 1]
  | none =>
  match sbbhiStruct? x with
  | some (d, a, b, c) => .set d (.cout true (R a) (R b) (R c)) [.eqW (R a) (R b), .wid (R c) 1]
  | none => symSh x R

theorem symMC_sound (x : LinstrR) (R : String → STerm) : RSound (lsemStepMC x) R (symMC x R) := by
  intro V A C O r hr
  unfold symMC
  split
  · rename_i d a b h
    simp only [ROut.Desc, lsemStepMC, h, readReg_reg, hr a, getW_eq, hr b, AllG,
      List.mem_singleton, forall_eq, SG.holds, STerm.ev, binW, ite_true]
    split_ifs with hw
    · simp [extW_of_eq hw, hw.symm]
    · simp [Ne.symm hw]
  · rename_i h1
    split
    · rename_i d a b c h
      simp only [ROut.Desc, lsemStepMC, h1, h, readReg_reg, hr a, getW_eq, hr b, hr c, AllG,
        List.mem_cons, forall_eq_or_imp, SG.holds, STerm.ev]
      generalize STerm.ev V A C O (R a) = pa
      generalize STerm.ev V A C O (R b) = pb
      generalize STerm.ev V A C O (R c) = pc
      obtain ⟨wa, va⟩ := pa
      obtain ⟨wb, vb⟩ := pb
      obtain ⟨wc, vc⟩ := pc
      by_cases hb : wb = wa
      · subst hb
        by_cases hc : wc = 1
        · subst hc
          simp [binW, applyOpnN, extW, JasminDialect.addCarryWord]
        · simp [hc]
      · simp [hb, Ne.symm hb]
    · rename_i h2
      split
      · rename_i d a b c h
        simp only [ROut.Desc, lsemStepMC, h1, h2, h, readReg_reg, hr a, getW_eq, hr b, hr c,
          AllG, List.mem_cons, forall_eq_or_imp, SG.holds, STerm.ev]
        generalize STerm.ev V A C O (R a) = pa
        generalize STerm.ev V A C O (R b) = pb
        generalize STerm.ev V A C O (R c) = pc
        obtain ⟨wa, va⟩ := pa
        obtain ⟨wb, vb⟩ := pb
        obtain ⟨wc, vc⟩ := pc
        by_cases hb : wb = wa
        · subst hb
          by_cases hc : wc = 1
          · subst hc
            simp [coutBit, extW]
          · simp [hc]
        · simp [hb, Ne.symm hb]
      · rename_i h3
        split
        · rename_i d a b c h
          simp only [ROut.Desc, lsemStepMC, h1, h2, h3, h, readReg_reg, hr a, getW_eq, hr b,
            hr c, AllG, List.mem_cons, forall_eq_or_imp, SG.holds, STerm.ev]
          generalize STerm.ev V A C O (R a) = pa
          generalize STerm.ev V A C O (R b) = pb
          generalize STerm.ev V A C O (R c) = pc
          obtain ⟨wa, va⟩ := pa
          obtain ⟨wb, vb⟩ := pb
          obtain ⟨wc, vc⟩ := pc
          by_cases hb : wb = wa
          · subst hb
            by_cases hc : wc = 1
            · subst hc
              simp [binW, applyOpnN, extW, JasminDialect.subBorrowWord]
            · simp [hc]
          · simp [hb, Ne.symm hb]
        · rename_i h4
          split
          · rename_i d a b c h
            simp only [ROut.Desc, lsemStepMC, h1, h2, h3, h4, h, readReg_reg, hr a, getW_eq,
              hr b, hr c, AllG, List.mem_cons, forall_eq_or_imp, SG.holds, STerm.ev]
            generalize STerm.ev V A C O (R a) = pa
            generalize STerm.ev V A C O (R b) = pb
            generalize STerm.ev V A C O (R c) = pc
            obtain ⟨wa, va⟩ := pa
            obtain ⟨wb, vb⟩ := pb
            obtain ⟨wc, vc⟩ := pc
            by_cases hb : wb = wa
            · subst hb
              by_cases hc : wc = 1
              · subst hc
                simp [coutBit, extW]
              · simp [hc]
            · simp [hb, Ne.symm hb]
          · rename_i h5
            have := symSh_sound x R V A C O r hr
            simpa only [ROut.Desc, lsemStepMC_of_delegate x r h1 h2 h3 h4 h5] using this

/-- The term of `x` zero-extended or truncated to width `w`: the `OR` at width `w` of the
    zero word and `x`, whose second source `STerm.ev` reads at width `w` (`extW`). -/
def castT (w : Nat) (x : STerm) : STerm := .bin "OR" (.immW w 0) x

theorem castT_ev (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) (w : Nat)
    (x : STerm) : ((castT w x).ev V A C O).2 = (x.ev V A C O).2.zeroExtend w := by
  simp [castT, STerm.ev, binW, applyOpnN, extW]

/-- The symbolic description of `lsemStepCast`: an untagged immediate move with a descriptor
    `w'` sets its destination to the immediate at width `w'`; a cast `d, a` with a
    descriptor `w'` sets its destination to `castT w' (R a)`, the source zero-extended or
    truncated to width `w'`. -/
def symCast (i : LinstrRT) (R : String → STerm) : ROut :=
  match castStruct? i.1 with
  | none =>
      match movImmStruct? i.1, i.2 with
      | some (d, n), some w' => .set d (.immW w' n) []
      | _, _ => symMC i.1 R
  | some (d, a) =>
      match i.2 with
      | none => symMC i.1 R
      | some w' => .set d (castT w' (R a)) []

theorem symCast_sound (i : LinstrRT) (R : String → STerm) :
    RSound (lsemStepCast i) R (symCast i R) := by
  intro V A C O r hr
  unfold symCast
  cases hc : castStruct? i.1 with
  | none =>
    cases hm : movImmStruct? i.1 with
    | none =>
      have := symMC_sound i.1 R V A C O r hr
      simpa only [ROut.Desc, lsemStepCast_of_delegate i r (Or.inl ⟨hc, hm⟩)] using this
    | some p =>
      obtain ⟨d, n⟩ := p
      cases hd : i.2 with
      | none =>
        have := symMC_sound i.1 R V A C O r hr
        simpa only [ROut.Desc, lsemStepCast_of_delegate i r (Or.inr hd)] using this
      | some w' =>
        have hstep : lsemStepCast i r = some ((r.setReg d (BitVec.ofNat w' n)).nextPc) := by
          simp only [lsemStepCast, hc, hm, hd]
        refine ⟨fun r' h' => ?_, fun _ => by simp [hstep]⟩
        rw [hstep] at h'
        exact ⟨fun g hg => by simp at hg, (Option.some.inj h').symm⟩
  | some p =>
    obtain ⟨d, a⟩ := p
    cases hd : i.2 with
    | none =>
      have := symMC_sound i.1 R V A C O r hr
      simpa only [ROut.Desc, lsemStepCast_of_delegate i r (Or.inr hd)] using this
    | some w' =>
      have hstep : lsemStepCast i r
          = some ((r.setReg d ((r.lvm a).2.zeroExtend w')).nextPc) := by
        simp only [lsemStepCast, hc, hd, readReg_reg]
      refine ⟨fun r' h' => ?_, fun _ => by simp [hstep]⟩
      rw [hstep] at h'
      refine ⟨fun g hg => by simp at hg, ?_⟩
      rw [← Option.some.inj h', castT_ev, ← hr a]
      rfl

/-! ## 5. The memory layer and the flag layer -/

/-- The symbolic description of a step: the step succeeds from a described state exactly
    when the guards hold and then ends in a state `ss` describes, the step always fails,
    or the instruction is outside the fragment. -/
inductive SOut where
  | ok (ss : SSt) (gs : List SG)
  | fail
  | unk

/-- A register-file description as a description of the whole state. -/
def liftR (ss : SSt) : ROut → SOut
  | .set d t gs => .ok (ss.setR d t) gs
  | .nop => .ok ss []
  | .fail => .fail
  | .unk => .unk

/-- The registers and arrays of a memref state are described by `ss`. -/
def HoldsM (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) (ss : SSt)
    (m : LstateM) : Prop :=
  (∀ q, m.reg.lvm q = (ss.regs q).ev V A C O) ∧ (∀ q, m.larr q = (ss.arrs q).ev V A C O)

/-- `o` describes the result `res` of a memref step from `m`: the pc advances by one and
    the word memory is kept. -/
def SOut.DescM (res : Option LstateM) (V : String → Σ w, BitVec w)
    (A : String → ArrCell) (C O : Bool) (m : LstateM) : SOut → Prop
  | .ok ss' gs =>
      (∀ m', res = some m' → AllG V A C O gs ∧ HoldsM V A C O ss' m' ∧
          m'.reg.lpc = m.reg.lpc + 1 ∧ m'.lmem = m.lmem) ∧
        (AllG V A C O gs → res.isSome)
  | .fail => res = none
  | .unk => True

theorem HoldsM.setR {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool} {ss : SSt}
    {m : LstateM} (h : HoldsM V A C O ss m) (d : String) (t : STerm) :
    HoldsM V A C O (ss.setR d t) { m with reg := (m.reg.setReg d (t.ev V A C O).2).nextPc } := by
  refine ⟨fun q => ?_, h.2⟩
  simp only [SSt.setR_regs, LstateN.lvm_nextPc, LstateN.lvm_setReg]
  split_ifs
  · rfl
  · exact h.1 q

theorem HoldsM.setA {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool} {ss : SSt}
    {m : LstateM} (h : HoldsM V A C O ss m) (d : String) (a : SArr) :
    HoldsM V A C O (ss.setA d a) ((m.setArr d (a.ev V A C O).2.2).nextPc) := by
  refine ⟨h.1, fun q => ?_⟩
  simp only [SSt.setA, LstateM.larr_nextPc, LstateM.larr_setArr]
  split_ifs
  · rfl
  · exact h.2 q

theorem liftR_sound {f : LstateN → Option LstateN} {ss : SSt} {o : ROut}
    (h : RSound f ss.regs o) (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (m : LstateM) (hm : HoldsM V A C O ss m) :
    (liftR ss o).DescM ((f m.reg).map (fun r => { m with reg := r })) V A C O m := by
  have hr := h V A C O m.reg hm.1
  cases o with
  | set d t gs =>
      refine ⟨fun m' hm' => ?_, fun hg => ?_⟩
      · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hm'
        obtain ⟨hg, rfl⟩ := hr.1 r' hr'
        exact ⟨hg, hm.setR d t, rfl, rfl⟩
      · simpa using hr.2 hg
  | nop =>
      simp only [ROut.Desc] at hr
      refine ⟨fun m' hm' => ?_, fun _ => ?_⟩
      · rw [hr] at hm'
        cases hm'
        exact ⟨allG_nil V A C O, hm, rfl, rfl⟩
      · simp [hr]
  | fail =>
      simp only [ROut.Desc] at hr
      simp [SOut.DescM, liftR, hr]
  | unk => trivial

/-- The symbolic description of `lsemStepMem`: the array load and store, the delegation to
    the register-file layers, and the compile-time-offset moves outside the fragment. -/
def symMem (i : LinstrRM) (ss : SSt) : SOut :=
  match i.2 with
  | .load w n =>
      match loadStruct? i.1 with
      | some (dst, base, idx) =>
          .ok (ss.setR dst (.aget (ss.arrs base) w n (ss.regs idx)))
            [.shp (ss.arrs base) w n, .wid (ss.regs idx) 64]
      | none => liftR ss (symCast (i.1, none) ss.regs)
  | .store w n =>
      match storeStruct? i.1 with
      | some (dst, base, idx, val) =>
          .ok (ss.setA dst (.aset (ss.arrs base) w n (ss.regs idx) (ss.regs val)))
            [.shp (ss.arrs base) w n, .wid (ss.regs idx) 64, .wid (ss.regs val) w]
      | none => liftR ss (symCast (i.1, none) ss.regs)
  | .loadC => .unk
  | .storeC => .unk
  | .zero w n =>
      match i.1 with
      | .Lopn [.reg dst] opn [.imm _, .imm _] =>
          if opn = "ZEROARR" then .ok (ss.setA dst (.zero w n)) [] else .fail
      | _ => .unk
  | .storeImm w n =>
      match storeImmStruct? i.1 with
      | some (dst, base, val, k) =>
          if k < 2 ^ 64 then
            .ok (ss.setA dst (.aset (ss.arrs base) w n (.immW 64 k) (ss.regs val)))
              [.shp (ss.arrs base) w n, .wid (ss.regs val) w]
          else .unk
      | none => .fail
  | .reg cd => liftR ss (symCast (i.1, cd) ss.regs)

theorem symMem_sound (i : LinstrRM) (ss : SSt) (V : String → Σ w, BitVec w)
    (A : String → ArrCell) (C O : Bool) (m : LstateM) (hm : HoldsM V A C O ss m) :
    (symMem i ss).DescM (lsemStepMem i m) V A C O m := by
  obtain ⟨x, tag⟩ := i
  unfold symMem
  cases tag with
  | load w n =>
      dsimp only
      split
      · rename_i dst base idx hl
        have heq : lsemStepMem (x, .load w n) m =
            if ((m.larr base).1 = w ∧ (m.larr base).2.1 = n) ∧ (m.reg.lvm idx).1 = 64 then
              some { m with reg := (m.reg.setReg dst
                (stackGet (castA (m.larr base) w n) (castW (m.reg.lvm idx) 64).toNat)).nextPc }
            else none := by
          simp only [lsemStepMem, hl, getArr_eq, getW_eq]
          split_ifs <;> simp_all [LstateM.setReg, LstateM.nextPc]
        rw [heq, hm.2 base, hm.1 idx]
        refine ⟨fun m' hm' => ?_, fun hg => ?_⟩
        · split_ifs at hm' with hc
          · cases hm'
            refine ⟨?_, hm.setR dst _, rfl, rfl⟩
            simp only [AllG, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
              forall_eq, SG.holds]
            exact ⟨hc.1, hc.2⟩
        · simp only [AllG, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
            forall_eq, SG.holds] at hg
          simp [hg]
      · rename_i hl
        have heq : lsemStepMem (x, .load w n) m =
            (lsemStepCast (x, none) m.reg).map (fun r => { m with reg := r }) := by
          simp [lsemStepMem, hl]
        rw [heq]
        exact liftR_sound (symCast_sound (x, none) ss.regs) V A C O m hm
  | store w n =>
      dsimp only
      split
      · rename_i dst base idx val hl
        have heq : lsemStepMem (x, .store w n) m =
            if ((m.larr base).1 = w ∧ (m.larr base).2.1 = n) ∧ (m.reg.lvm idx).1 = 64 ∧
                (m.reg.lvm val).1 = w then
              some ((m.setArr dst (stackSet (castA (m.larr base) w n)
                (castW (m.reg.lvm idx) 64).toNat (castW (m.reg.lvm val) w))).nextPc)
            else none := by
          simp only [lsemStepMem, hl, getArr_eq, getW_eq]
          split_ifs <;> simp_all
        rw [heq, hm.2 base, hm.1 idx, hm.1 val]
        refine ⟨fun m' hm' => ?_, fun hg => ?_⟩
        · split_ifs at hm' with hc
          cases hm'
          refine ⟨?_, hm.setA dst _, rfl, rfl⟩
          simp only [AllG, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
            forall_eq, SG.holds]
          exact ⟨hc.1, hc.2.1, hc.2.2⟩
        · simp only [AllG, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
            forall_eq, SG.holds] at hg
          simp [hg]
      · rename_i hl
        have heq : lsemStepMem (x, .store w n) m =
            (lsemStepCast (x, none) m.reg).map (fun r => { m with reg := r }) := by
          simp [lsemStepMem, hl]
        rw [heq]
        exact liftR_sound (symCast_sound (x, none) ss.regs) V A C O m hm
  | loadC => trivial
  | storeC => trivial
  | zero w n =>
      dsimp only
      split
      · rename_i dst opn k1 k2
        split
        · rename_i hz
          have heq : lsemStepMem (.Lopn [.reg dst] opn [.imm k1, .imm k2], .zero w n) m =
              some ((m.setArr dst (fun _ : Fin n => (0 : BitVec w))).nextPc) := by
            simp only [lsemStepMem, zeroStruct?, hz, ite_true]
          rw [heq]
          refine ⟨fun m' hm' => ?_, fun _ => rfl⟩
          cases hm'
          exact ⟨allG_nil V A C O, hm.setA dst (.zero w n), rfl, rfl⟩
        · rename_i hz
          simp only [SOut.DescM, lsemStepMem, zeroStruct?, hz, ite_false]
      · trivial
  | storeImm w n =>
      dsimp only
      split
      · rename_i dst base val k hs
        split
        · rename_i hk
          have heq : lsemStepMem (x, .storeImm w n) m =
              if ((m.larr base).1 = w ∧ (m.larr base).2.1 = n) ∧ (m.reg.lvm val).1 = w then
                some ((m.setArr dst (stackSet (castA (m.larr base) w n) k
                  (castW (m.reg.lvm val) w))).nextPc)
              else none := by
            simp only [lsemStepMem, hs, getArr_eq, getW_eq]
            split_ifs <;> simp_all
          rw [heq, hm.2 base, hm.1 val]
          have hk' : (castW ((STerm.immW 64 k).ev V A C O) 64).toNat = k := by
            simpa [STerm.ev, castW] using hk
          refine ⟨fun m' hm' => ?_, fun hg => ?_⟩
          · split_ifs at hm' with hc
            cases hm'
            refine ⟨?_, ?_, rfl, rfl⟩
            · simp only [AllG, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
                forall_eq, SG.holds]
              exact ⟨hc.1, hc.2⟩
            · have := hm.setA dst ((ss.arrs base).aset w n (.immW 64 k) (ss.regs val))
              simpa only [SArr.ev, hk'] using this
          · simp only [AllG, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
              forall_eq, SG.holds] at hg
            simp [hg]
        · trivial
      · rename_i hs
        simp only [SOut.DescM, lsemStepMem, hs]
  | reg cd => exact liftR_sound (symCast_sound (x, cd) ss.regs) V A C O m hm

/-- The symbolic word of an operand read at width `64`, with the guards of the read;
    `none` for an operand that is read at no width. -/
def symOp64 (R : String → STerm) : LOperand → Option (STerm × List SG)
  | .reg r => some (R r, [.wid (R r) 64])
  | .imm n => some (.immW 64 n, [])
  | _ => none

theorem symOp64_some {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {R : String → STerm} {r : LstateN} (hr : ∀ q, r.lvm q = (R q).ev V A C O) {o : LOperand}
    {t : STerm} {g : List SG} (h : symOp64 R o = some (t, g)) :
    evalOperandN r 64 o =
        (if (t.ev V A C O).1 = 64 then some (castW (t.ev V A C O) 64) else none) ∧
      (AllG V A C O g ↔ (t.ev V A C O).1 = 64) := by
  cases o with
  | reg q =>
      simp only [symOp64, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [evalOperandN, getW_eq, hr q, AllG, SG.holds]
  | imm n =>
      simp only [symOp64, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [evalOperandN, STerm.ev, AllG]
  | arr _ _ => cases h
  | arrIdx _ _ _ => cases h

theorem symOp64_none {R : String → STerm} {r : LstateN} {o : LOperand}
    (h : symOp64 R o = none) : evalOperandN r 64 o = none := by
  cases o <;> simp_all [symOp64, evalOperandN]

/-- The sources of the instruction are described in exchanged order (`commSwap`). -/
def aluSwap (i : LinstrRM) : Bool :=
  match i.1 with
  | .Lopn [.reg d] opn [.reg a, .reg b] => commSwap opn d a b
  | _ => false

/-- The flags of a commutative arithmetic or logical operation do not depend on the order
    of its sources. -/
theorem aluBit_comm {op : AluOp} (hop : op ≠ .sub) (ofl : Bool) (a b : BitVec 64) :
    aluBit op ofl a b = aluBit op ofl b a := by
  cases op
  · simp [aluBit, aluB5, Jasmin.x86_ADD, BitVec.add_comm, Nat.add_comm, Int.add_comm]
  · exact absurd rfl hop
  all_goals simp [aluBit, aluB5, Jasmin.x86_AND, Jasmin.x86_OR, Jasmin.x86_XOR,
    BitVec.and_comm, BitVec.or_comm, BitVec.xor_comm]

/-- The symbolic carry flag (`ofl = false`) or overflow flag (`ofl = true`) after the memref
    step of `i` from `ss`: for a recognised arithmetic or logical operation whose sources are
    read at width `64`, the flag it writes (`STerm.aluF`), with the sources exchanged when
    `aluSwap` holds and the operation is commutative; otherwise the flag of `ss`. -/
def aluFlT (i : LinstrRM) (ss : SSt) (ofl : Bool) : STerm :=
  match aluFlagOp? i with
  | some (op, a, b) =>
      match symOp64 ss.regs a, symOp64 ss.regs b with
      | some (ta, _), some (tb, _) =>
          if aluSwap i && op != .sub then .aluF op ofl tb ta (if ofl then ss.of else ss.cf)
          else .aluF op ofl ta tb (if ofl then ss.of else ss.cf)
      | _, _ => if ofl then ss.of else ss.cf
  | none => if ofl then ss.of else ss.cf

/-- A description of the memref step of `i` from `ss` with the flags of `withALUFlags`. -/
def aluFl (i : LinstrRM) (ss : SSt) : SOut → SOut
  | .ok ss' gs => .ok { ss' with cf := aluFlT i ss false, of := aluFlT i ss true } gs
  | .fail => .fail
  | .unk => .unk

/-- The symbolic description of the carry-family step `op d, a, b` (`carryStep`): both
    sources are read at width `64`, and the carry-in is the carry flag, the overflow flag for
    `ADOX`. -/
def symCarry (op : CarryOp) (d : String) (a b : LOperand) (ss : SSt) : SOut :=
  match symOp64 ss.regs a, symOp64 ss.regs b with
  | some (ta, ga), some (tb, gb) =>
      match op with
      | .adc => .ok { ss.setR d (.carryW .adc ta tb ss.cf) with
          cf := .carryF .adc false ta tb ss.cf, of := .carryF .adc true ta tb ss.cf } (ga ++ gb)
      | .sbb => .ok { ss.setR d (.carryW .sbb ta tb ss.cf) with
          cf := .carryF .sbb false ta tb ss.cf, of := .carryF .sbb true ta tb ss.cf } (ga ++ gb)
      | .adcx => .ok { ss.setR d (.carryW .adcx ta tb ss.cf) with
          cf := .carryF .adcx false ta tb ss.cf } (ga ++ gb)
      | .adox => .ok { ss.setR d (.carryW .adox ta tb ss.of) with
          of := .carryF .adox true ta tb ss.of } (ga ++ gb)
  | _, _ => .fail

/-- The term of the low word of the widening product of `x` and `y` read at width `64`: the
    low `MUL` of `x` and `y` masked by the `64`-bit all-ones immediate, the term of a low
    `MUL` followed by its `AND` with a register holding that immediate. -/
def mulLoT (x y : STerm) : STerm := .bin "AND" (.bin "MUL" x y) (.immW 64 (2 ^ 64 - 1))

theorem mulLoT_ev {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {x y : STerm} (hx : (x.ev V A C O).1 = 64) (hy : (y.ev V A C O).1 = 64) :
    (mulLoT x y).ev V A C O
      = ⟨64, (x86_MULX_lo_hi (castW (x.ev V A C O) 64) (castW (y.ev V A C O) 64)).1⟩ := by
  unfold mulLoT
  simp only [STerm.ev]
  generalize x.ev V A C O = p at hx ⊢
  generalize y.ev V A C O = q at hy ⊢
  obtain ⟨w, a⟩ := p
  obtain ⟨w', b⟩ := q
  obtain rfl : w = 64 := hx
  obtain rfl : w' = 64 := hy
  simp only [binW, applyOpnN, extW, castW_mk, x86_MULX_lo_hi, Jasmin.wumul]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp
  rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod]

/-- The symbolic description of the flag-quiet lift step `wideStep`: the sources are read
    at width `64`, the implicit first source of `MULX` is the register `mulxSrc`, the low
    word of `MULX` has the term `mulLoT` of its sources, and the high word of `MULX` is
    written after the low word. -/
def symWide (w : WideOp) (ss : SSt) : SOut :=
  match w with
  | .mov d b =>
      match symOp64 ss.regs b with
      | some (tb, gb) => .ok (ss.setR d tb) gb
      | none => .fail
  | .mulx lo hi b =>
      match symOp64 ss.regs (.reg mulxSrc), symOp64 ss.regs b with
      | some (tx, gx), some (tb, gb) =>
          .ok ((ss.setR lo (mulLoT tx tb)).setR hi (.mulx true tx tb)) (gx ++ gb)
      | _, _ => .fail

/-- The symbolic description of one instruction of `evalInstrPMemF`: the flag `CMP`, the
    register-copy `MOV`, a label, the carry family, the flag-quiet lift instructions, and
    the memref step with the flags of `withALUFlags`; a branch and a jump are outside the
    fragment. -/
def symStep (i : LinstrRM) (ss : SSt) : SOut :=
  match cmpArgs? i with
  | some (a, b) =>
      match symOp64 ss.regs a, symOp64 ss.regs b with
      | some (ta, ga), some (tb, gb) => .ok { ss with zf := .cmp ta tb } (ga ++ gb)
      | _, _ => .fail
  | none =>
      match movRegArgs? i with
      | some (dst, src) => .ok (ss.setR dst (ss.regs src)) []
      | none =>
          match flagCondCC? i with
          | some _ => .unk
          | none =>
              match i.1 with
              | .Llabel _ _ => .ok ss []
              | .Lcond _ _ => .unk
              | .Lgoto _ => .unk
              | _ =>
                  match carryArgs? i with
                  | some (op, d, a, b) => symCarry op d a b ss
                  | none =>
                      match wideArgs? i with
                      | some w => symWide w ss
                      | none => aluFl i ss (symMem i ss)

/-- A flag-machine step keeps the function and the word memory and advances the pc. -/
def Frame (s t : LstateMF) : Prop :=
  t.prog.lfn = s.prog.lfn ∧ t.prog.base.reg.lpc = s.prog.base.reg.lpc + 1 ∧
    t.prog.base.lmem = s.prog.base.lmem

/-- `o` describes the result `res` of a flag-machine step from `s`. -/
def SOut.Desc (res : Option LstateMF) (V : String → Σ w, BitVec w) (A : String → ArrCell)
    (C O : Bool) (Z : Bool) (s : LstateMF) : SOut → Prop
  | .ok ss' gs =>
      (∀ t, res = some t → AllG V A C O gs ∧ Holds V A C O Z ss' t ∧ Frame s t) ∧
        (AllG V A C O gs → res.isSome)
  | .fail => res = none
  | .unk => True

/-- `o` describes the flag-machine step `g` exactly from every state `ss` describes. -/
def StepSound (g : LstateMF → Option LstateMF) (ss : SSt) (o : SOut) : Prop :=
  ∀ (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) (Z : Bool)
    (s : LstateMF), Holds V A C O Z ss s → o.Desc (g s) V A C O Z s

/-- The flags `withALUFlags` writes are described by `aluFlT`, when the step before it
    keeps the flags. -/
theorem aluFlT_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {ss : SSt} {m b : LstateM} (hr : ∀ q, m.reg.lvm q = (ss.regs q).ev V A C O)
    (hc : m.cf = bitOf (ss.cf.ev V A C O)) (ho : m.of = bitOf (ss.of.ev V A C O))
    (hb : b.cf = m.cf ∧ b.of = m.of) (i : LinstrRM) :
    (withALUFlags i m b).cf = bitOf ((aluFlT i ss false).ev V A C O) ∧
      (withALUFlags i m b).of = bitOf ((aluFlT i ss true).ev V A C O) := by
  unfold withALUFlags aluFlT
  cases hi : aluFlagOp? i with
  | none => simp [hb.1, hb.2, hc, ho]
  | some p =>
    obtain ⟨op, a, c⟩ := p
    cases h1 : symOp64 ss.regs a with
    | none => simp [h1, symOp64_none h1, hb.1, hb.2, hc, ho]
    | some p1 =>
      obtain ⟨ta, ga⟩ := p1
      cases h2 : symOp64 ss.regs c with
      | none =>
          simp only [h1, h2, symOp64_none (r := m.reg) h2]
          cases evalOperandN m.reg 64 a <;> simp [hb.1, hb.2, hc, ho]
      | some p2 =>
        obtain ⟨tb, gb⟩ := p2
        obtain ⟨e1, -⟩ := symOp64_some hr h1
        obtain ⟨e2, -⟩ := symOp64_some hr h2
        simp only [h1, h2, e1, e2]
        by_cases hsw : (aluSwap i && op != AluOp.sub) = true
        · have hop : op ≠ .sub := by
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hsw
            exact hsw.2
          simp only [hsw, ↓reduceIte, STerm.ev]
          by_cases w1 : (ta.ev V A C O).1 = 64 <;> by_cases w2 : (tb.ev V A C O).1 = 64 <;>
            simp [w1, w2, aluBit, hb.1, hb.2, hc, ho]
          exact ⟨aluBit_comm hop false _ _, aluBit_comm hop true _ _⟩
        · simp only [hsw, Bool.false_eq_true, ↓reduceIte, STerm.ev]
          by_cases w1 : (ta.ev V A C O).1 = 64 <;> by_cases w2 : (tb.ev V A C O).1 = 64 <;>
            simp [w1, w2, aluBit, hb.1, hb.2, hc, ho]

/-- A description of a memref step from the base of `s`, whose successful results keep the
    flags, describes the flag-machine step with the flags of `withALUFlags`. -/
theorem descM_liftF {res : Option LstateM} {V : String → Σ w, BitVec w} {A : String → ArrCell}
    {C O Z : Bool} {ss : SSt} {s : LstateMF} {o : SOut} (i : LinstrRM)
    (hz : ∀ ss' gs, o = .ok ss' gs → ss'.zf = ss.zf) (hs : Holds V A C O Z ss s)
    (h : o.DescM res V A C O s.prog.base)
    (hfl : ∀ b, res = some b → b.cf = s.prog.base.cf ∧ b.of = s.prog.base.of) :
    (aluFl i ss o).Desc ((res.map (withALUFlags i s.prog.base)).map
      (fun b => { s with prog := { s.prog with base := b } })) V A C O Z s := by
  cases o with
  | ok ss' gs =>
      have hzz := hz ss' gs rfl
      refine ⟨fun t ht => ?_, fun hg => by simpa using h.2 hg⟩
      obtain ⟨b1, hb1, rfl⟩ := Option.map_eq_some_iff.mp ht
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hb1
      obtain ⟨hg, hH, hpc, hmem⟩ := h.1 b hb
      obtain ⟨ec, eo⟩ := aluFlT_sound hs.1 hs.2.2.2.1 hs.2.2.2.2 (hfl b hb) i
      refine ⟨hg, ⟨fun q => ?_, fun q => ?_, ?_, ec, eo⟩, rfl, ?_, ?_⟩
      · rw [withALUFlags_reg]; exact hH.1 q
      · rw [withALUFlags_larr]; exact hH.2 q
      · show s.zf = _
        rw [show ({ ss' with cf := aluFlT i ss false, of := aluFlT i ss true } : SSt).zf
          = ss.zf from hzz]
        exact hs.2.2.1
      · rw [withALUFlags_reg]; exact hpc
      · rw [withALUFlags_lmem]; exact hmem
  | fail =>
      simp only [SOut.DescM] at h
      simp [aluFl, SOut.Desc, h]
  | unk => trivial

theorem liftR_zf (ss : SSt) (o : ROut) : ∀ ss' gs, liftR ss o = .ok ss' gs → ss'.zf = ss.zf := by
  intro ss' gs h
  cases o <;> simp only [liftR, SOut.ok.injEq, reduceCtorEq] at h
  · rw [← h.1]; rfl
  · rw [← h.1]

theorem symMem_zf (i : LinstrRM) (ss : SSt) :
    ∀ ss' gs, symMem i ss = .ok ss' gs → ss'.zf = ss.zf := by
  intro ss' gs h
  obtain ⟨x, tag⟩ := i
  unfold symMem at h
  cases tag with
  | load w n =>
      dsimp only at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; rfl
      · exact liftR_zf ss _ ss' gs h
  | store w n =>
      dsimp only at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; rfl
      · exact liftR_zf ss _ ss' gs h
  | loadC => cases h
  | storeC => cases h
  | zero w n =>
      dsimp only at h
      split at h
      · split at h
        · simp only [SOut.ok.injEq] at h; rw [← h.1]; rfl
        · cases h
      · cases h
  | storeImm w n =>
      dsimp only at h
      split at h
      · split at h
        · simp only [SOut.ok.injEq] at h; rw [← h.1]; rfl
        · cases h
      · cases h
  | reg cd => exact liftR_zf ss _ ss' gs h

/-- The carry-family step is described by `symCarry`. -/
theorem symCarry_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O Z : Bool}
    {ss : SSt} {s : LstateMF} (op : CarryOp) (d : String) (a b : LOperand)
    (hs : Holds V A C O Z ss s) :
    (symCarry op d a b ss).Desc ((carryStep op d a b s.prog.base).map
      (fun b' => { s with prog := { s.prog with base := b' } })) V A C O Z s := by
  unfold symCarry carryStep
  cases h1 : symOp64 ss.regs a with
  | none => simp [SOut.Desc, symOp64_none h1]
  | some p =>
    obtain ⟨ta, ga⟩ := p
    cases h2 : symOp64 ss.regs b with
    | none => simp [SOut.Desc, symOp64_none h2]
    | some q =>
      obtain ⟨tb, gb⟩ := q
      obtain ⟨e1, g1⟩ := symOp64_some hs.1 h1
      obtain ⟨e2, g2⟩ := symOp64_some hs.1 h2
      simp only
      rw [e1, e2]
      have hreg : ∀ (w : BitVec 64) (q : String),
          ((s.prog.base.setReg d w).nextPc).reg.lvm q
            = (if q = d then (⟨64, w⟩ : Σ w, BitVec w) else (ss.regs q).ev V A C O) := by
        intro w q
        simp only [LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.lvm_nextPc,
          LstateN.lvm_setReg]
        split_ifs
        · rfl
        · exact hs.1 q
      cases op <;> refine ⟨fun t ht => ?_, fun hg => ?_⟩
      all_goals first
        | (obtain ⟨h1', h2'⟩ := allG_append.mp hg
           simp [g1.mp h1', g2.mp h2'])
        | (by_cases c1 : (ta.ev V A C O).1 = 64
           · by_cases c2 : (tb.ev V A C O).1 = 64
             · simp only [c1, c2, ite_true, Option.map_some, Option.some.injEq] at ht
               subst ht
               refine ⟨allG_append.mpr ⟨g1.mpr c1, g2.mpr c2⟩,
                 ⟨fun q => (hreg _ q).trans ?_, hs.2.1, hs.2.2.1, ?_, ?_⟩, rfl, rfl, rfl⟩
               all_goals first
                 | (by_cases hq : q = d <;>
                     simp [hq, SSt.setR_regs, STerm.ev, carryWord, hs.2.2.2.1, hs.2.2.2.2])
                 | simp [STerm.ev, carryBit, LstateM.setReg, LstateM.nextPc, SSt.setR,
                     hs.2.2.2.1, hs.2.2.2.2]
             · simp [c1, c2] at ht
           · simp [c1] at ht)

/-- The flag-quiet lift step is described by `symWide`. -/
theorem symWide_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O Z : Bool}
    {ss : SSt} {s : LstateMF} (w : WideOp) (hs : Holds V A C O Z ss s) :
    (symWide w ss).Desc ((wideStep w s.prog.base).map
      (fun b' => { s with prog := { s.prog with base := b' } })) V A C O Z s := by
  cases w with
  | mov d b =>
    simp only [symWide, wideStep]
    cases h1 : symOp64 ss.regs b with
    | none => simp [SOut.Desc, symOp64_none h1]
    | some p =>
      obtain ⟨tb, gb⟩ := p
      obtain ⟨e1, g1⟩ := symOp64_some hs.1 h1
      simp only
      rw [e1]
      refine ⟨fun t ht => ?_, fun hg => ?_⟩
      · by_cases c1 : (tb.ev V A C O).1 = 64
        · simp only [c1, ite_true, Option.map_some, Option.some.injEq] at ht
          subst ht
          refine ⟨g1.mpr c1, ⟨fun q => ?_, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩,
            rfl, rfl, rfl⟩
          simp only [SSt.setR_regs, LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.lvm_nextPc,
            LstateN.lvm_setReg]
          split_ifs
          · exact sigma_of_castW c1
          · exact hs.1 q
        · simp [c1] at ht
      · simp [g1.mp hg]
  | mulx lo hi b =>
    simp only [symWide, wideStep]
    cases h0 : symOp64 ss.regs (.reg mulxSrc) with
    | none => simp [SOut.Desc, symOp64_none h0]
    | some p0 =>
      obtain ⟨tx, gx⟩ := p0
      cases h1 : symOp64 ss.regs b with
      | none => simp [SOut.Desc, symOp64_none h1]
      | some p1 =>
        obtain ⟨tb, gb⟩ := p1
        obtain ⟨e0, g0⟩ := symOp64_some hs.1 h0
        obtain ⟨e1, g1⟩ := symOp64_some hs.1 h1
        simp only
        rw [e0, e1]
        refine ⟨fun t ht => ?_, fun hg => ?_⟩
        · by_cases c0 : (tx.ev V A C O).1 = 64
          · by_cases c1 : (tb.ev V A C O).1 = 64
            · simp only [c0, c1, ite_true, Option.map_some, Option.some.injEq] at ht
              subst ht
              refine ⟨allG_append.mpr ⟨g0.mpr c0, g1.mpr c1⟩,
                ⟨fun q => ?_, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩, rfl, rfl, rfl⟩
              simp only [SSt.setR_regs, LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.lvm_nextPc,
                LstateN.lvm_setReg]
              by_cases hq : q = hi
              · simp [hq, STerm.ev]
              · by_cases hl : q = lo
                · subst hl
                  simp only [hq, ite_false, ite_true]
                  rw [mulLoT_ev c0 c1]
                · simp only [hq, hl, ite_false]
                  exact hs.1 q
            · simp [c0, c1] at ht
          · simp [c0] at ht
        · obtain ⟨h0', h1'⟩ := allG_append.mp hg
          simp [g0.mp h0', g1.mp h1']

theorem symStep_sound (P : LprogM) (i : LinstrRM) (ss : SSt) :
    StepSound (evalInstrPMemF P i) ss (symStep i ss) := by
  intro V A C O Z s hs
  unfold symStep
  split
  · rename_i a b hc
    have he : evalInstrPMemF P i s =
        match evalOperandN s.prog.base.reg 64 a, evalOperandN s.prog.base.reg 64 b with
        | some va, some vb =>
            some { prog := { s.prog with base := s.prog.base.nextPc }, zf := va == vb }
        | _, _ => none := by
      simp only [evalInstrPMemF, hc]
      rfl
    rw [he]
    cases h1 : symOp64 ss.regs a with
    | none => simp [SOut.Desc, symOp64_none h1]
    | some p =>
      obtain ⟨ta, ga⟩ := p
      cases h2 : symOp64 ss.regs b with
      | none => simp [SOut.Desc, symOp64_none h2]
      | some q =>
        obtain ⟨tb, gb⟩ := q
        obtain ⟨e1, g1⟩ := symOp64_some hs.1 h1
        obtain ⟨e2, g2⟩ := symOp64_some hs.1 h2
        simp only
        rw [e1, e2]
        refine ⟨fun t ht => ?_, fun hg => ?_⟩
        · by_cases c1 : (ta.ev V A C O).1 = 64
          · by_cases c2 : (tb.ev V A C O).1 = 64
            · simp only [c1, c2, ite_true, Option.some.injEq] at ht
              subst ht
              exact ⟨allG_append.mpr ⟨g1.mpr c1, g2.mpr c2⟩,
                ⟨hs.1, hs.2.1, rfl, hs.2.2.2⟩, rfl, rfl, rfl⟩
            · simp [c1, c2] at ht
          · simp [c1] at ht
        · obtain ⟨h1', h2'⟩ := allG_append.mp hg
          simp [g1.mp h1', g2.mp h2']
  · rename_i hc
    split
    · rename_i dst src hm
      have he : evalInstrPMemF P i s = some { s with prog := { s.prog with
          base := (s.prog.base.setReg dst (s.prog.base.reg.lvm src).2).nextPc } } := by
        simp only [evalInstrPMemF, hc, hm, readReg]
      rw [he]
      refine ⟨fun t ht => ?_, fun _ => rfl⟩
      cases ht
      refine ⟨allG_nil V A C O, ⟨fun q => ?_, hs.2.1, hs.2.2⟩, rfl, rfl, rfl⟩
      simp only [SSt.setR_regs, LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.lvm_nextPc,
        LstateN.lvm_setReg]
      split_ifs
      · exact hs.1 src
      · exact hs.1 q
    · rename_i hm
      split
      · trivial
      · rename_i hf
        split
        · rename_i hl
          have he : evalInstrPMemF P i s =
              some { s with prog := { s.prog with base := s.prog.base.nextPc } } := by
            have ha : aluFlagOp? i = none := by simp [aluFlagOp?, hl]
            simp only [evalInstrPMemF, hc, hm, hf, evalInstrPMemL, hl, withALUFlags_of_none ha]
          rw [he]
          refine ⟨fun t ht => ?_, fun _ => rfl⟩
          cases ht
          exact ⟨allG_nil V A C O, ⟨hs.1, hs.2.1, hs.2.2⟩, rfl, rfl, rfl⟩
        · trivial
        · trivial
        · rename_i h1 h2 h3
          have hL : evalInstrPMemL P i s.prog
              = (lsemStepMem i s.prog.base).map (fun b => { s.prog with base := b }) := by
            unfold evalInstrPMemL
            split
            · rename_i h; exact (h1 _ _ h).elim
            · rename_i h; exact (h2 _ _ h).elim
            · rename_i h; exact (h3 _ h).elim
            · rfl
          split
          · rename_i op d a b hk
            have he : evalInstrPMemF P i s = (carryStep op d a b s.prog.base).map
                (fun b' => { s with prog := { s.prog with base := b' } }) := by
              simp only [evalInstrPMemF, hc, hm, hf, hL, lsemStepMem_of_carryArgs hk,
                Option.map_none, hk]
            rw [he]
            exact symCarry_sound op d a b hs
          · rename_i hk
            split
            · rename_i w hw
              have he : evalInstrPMemF P i s = (wideStep w s.prog.base).map
                  (fun b' => { s with prog := { s.prog with base := b' } }) := by
                simp only [evalInstrPMemF, hc, hm, hf, hL, lsemStepMem_of_wideArgs hw,
                  Option.map_none, hk, hw]
              rw [he]
              exact symWide_sound w hs
            · rename_i hw
              have he : evalInstrPMemF P i s =
                  ((lsemStepMem i s.prog.base).map (withALUFlags i s.prog.base)).map
                    (fun b => { s with prog := { s.prog with base := b } }) := by
                simp only [evalInstrPMemF, hc, hm, hf, hL]
                cases lsemStepMem i s.prog.base <;> simp [hk, hw]
              rw [he]
              exact descM_liftF i (symMem_zf i ss) hs
                (symMem_sound i ss V A C O s.prog.base ⟨hs.1, hs.2.1⟩)
                (fun b hb => lsemStepMem_flags hb)

/-- The untagged and the `:64`-tagged mnemonics of the commutative bases
    `TwoAddrLegalize.commBases`. -/
def commOpns : List String :=
  ["ADD", "MUL", "AND", "OR", "XOR", "ADD:64", "MUL:64", "AND:64", "OR:64", "XOR:64"]

/-- **Commuted sources have one description.** For a commutative mnemonic, the step of
    `opn d, [x, d]` and the step of `opn d, [d, x]` are described alike. -/
theorem symStep_comm {opn d x : String} (hopn : opn ∈ commOpns) (hxd : x ≠ d) (τ : MemTag)
    (ss : SSt) :
    symStep (.Lopn [.reg d] opn [.reg x, .reg d], τ) ss =
      symStep (.Lopn [.reg d] opn [.reg d, .reg x], τ) ss := by
  have hF : TwoAddrLegalize.commBases.contains (stripWidthTag opn) = true ∧
      binOk (stripWidthTag opn) = true ∧ stripWidthTag opn ≠ "MULXHI" ∧
      stripWidthTag opn ≠ "SAR" ∧ opn ≠ withWidthTag 64 "CMP" ∧
      opn ≠ withWidthTag 64 "ADC" ∧ opn ≠ withWidthTag 64 "SBB" ∧
      opn ≠ withWidthTag 64 "ADCX" ∧ opn ≠ withWidthTag 64 "ADOX" ∧
      opn ≠ withWidthTag 64 "MOV" ∧ opn ≠ withWidthTag 64 "SUB" := by
    simp only [commOpns, List.mem_cons, List.mem_nil_iff, or_false] at hopn
    rcases hopn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  obtain ⟨hc, hb, hmx, hsar, hcmp, hadc, hsbb, hadcx, hadox, hmov, hsub⟩ := hF
  have hs1 : commSwap opn d x d = true := by
    unfold commSwap
    rw [hc]
    simp [hxd]
  have hs2 : commSwap opn d d x = false := by simp [commSwap]
  have hC : ∀ cd, symCast (.Lopn [.reg d] opn [.reg x, .reg d], cd) ss.regs =
      symCast (.Lopn [.reg d] opn [.reg d, .reg x], cd) ss.regs := by
    intro cd
    dsimp only [symCast, castStruct?, movImmStruct?, symMC, mulhiStruct?, adcxStruct?,
      adcxhiStruct?, sbbStruct?, sbbhiStruct?, symSh, sarStruct?]
    simp only [hmx, ite_false]
    dsimp only [symN]
    simp only [hb, hs1, hs2, Bool.false_eq_true, ↓reduceIte]
  have hM : symMem (.Lopn [.reg d] opn [.reg x, .reg d], τ) ss =
      symMem (.Lopn [.reg d] opn [.reg d, .reg x], τ) ss := by
    cases τ <;> simp only [symMem, loadStruct?, storeStruct?, storeImmStruct?, hC]
  have hA : ∀ ofl, aluFlT (.Lopn [.reg d] opn [.reg x, .reg d], τ) ss ofl =
      aluFlT (.Lopn [.reg d] opn [.reg d, .reg x], τ) ss ofl := by
    intro ofl
    simp only [aluFlT, aluFlagOp?, aluSwap, hs1, hs2, hsub, ite_false]
    split_ifs <;> simp [symOp64]
  simp only [symStep, cmpArgs?, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?, hcmp, hadc,
    hsbb, hadcx, hadox, hmov, ite_false, hM]
  cases symMem (.Lopn [.reg d] opn [.reg d, .reg x], τ) ss <;> simp only [aluFl, hA]

/-! ## The x86 instruction set

The x86 instance `X86Isa.x86Isa` of the instruction-set record `LprogIsa.Isa`: its step is
the flag machine `evalInstrPMemF` and its branch condition is `decC`. The checker of the
sections below takes a symbolic step and a symbolic branch condition as trailing arguments
that default to `symStep` and `symDec`; its soundness is proved for every instruction set
whose step they describe (`SymLaws`), and the statements about `evalInstrPMemF` and
`lsemFuelMemF` are the instances at `x86Isa`. The instance, its branch condition `decC` and
its control-step lemmas are in `X86Backend.X86IsaDef`. -/

theorem evalInstrPMemF_ret (P : LprogM) (tag : MemTag) (s : LstateMF) :
    evalInstrPMemF P (.Lret, tag) s = none := by
  rw [evalInstrPMemF_delegate P _ s rfl rfl rfl rfl rfl rfl]
  simp [evalInstrPMemL, AllocCheck.LcmdCFG.lsemStepMem_ret]

open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)

/-! ## 6. Straight-line runs -/

/-- The flag-machine steps of a list of instructions, in order. -/
def runL (P : LprogM) : List LinstrRM → LstateMF → Option LstateMF
  | [], s => some s
  | i :: is, s => (evalInstrPMemF P i s).bind (runL P is)

/-- The generic straight-line run at `x86Isa` is `OwnedLprogTV.runL`, by unfolding both
    definitions. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa.x86Isa_runL :
    x86Isa.runL = OwnedLprogTV.runL := by
  delta Isa.runL OwnedLprogTV.runL; rfl

open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa_lsemFuelMemF x86Isa_runL)

/-- The symbolic run of a list of instructions under the symbolic step `sym`: the final
    symbolic state with the guards of every step, `fail` when a step always fails, `unk`
    when a step is outside the fragment. The step defaults to the x86 step `symStep`. -/
def symRun : List LinstrRM → SSt → optParam (LinstrRM → SSt → SOut) symStep → SOut
  | [], ss, _ => .ok ss []
  | i :: is, ss, sym =>
      match sym i ss with
      | .ok ss1 g1 =>
          match symRun is ss1 sym with
          | .ok ss2 g2 => .ok ss2 (g1 ++ g2)
          | .fail => .fail
          | .unk => .unk
      | .fail => .fail
      | .unk => .unk

/-- `k` flag-machine steps keep the function and the word memory and advance the pc by
    `k`. -/
def FrameN (k : Nat) (s t : LstateMF) : Prop :=
  t.prog.lfn = s.prog.lfn ∧ t.prog.base.reg.lpc = s.prog.base.reg.lpc + k ∧
    t.prog.base.lmem = s.prog.base.lmem

/-- `o` describes the result `res` of `k` flag-machine steps from `s`. -/
def SOut.DescN (k : Nat) (res : Option LstateMF) (V : String → Σ w, BitVec w)
    (A : String → ArrCell) (C O : Bool) (Z : Bool) (s : LstateMF) : SOut → Prop
  | .ok ss' gs =>
      (∀ t, res = some t → AllG V A C O gs ∧ Holds V A C O Z ss' t ∧ FrameN k s t) ∧
        (AllG V A C O gs → res.isSome)
  | .fail => res = none
  | .unk => True

/-- **The symbolic run describes the run exactly**, for every instruction set `I` and every
    symbolic step `sym` that describes its step. From every state `ss` describes, the steps
    of `is` succeed exactly when the guards of `symRun is ss sym` hold, and then end in a
    state its final symbolic state describes; a run `symRun` reports as failing fails. -/
theorem symRun_sound_at {I : Isa} {sym : LinstrRM → SSt → SOut}
    (hsym : ∀ (P : LprogM) (i : LinstrRM) (ss : SSt), StepSound (I.step P i) ss (sym i ss))
    (P : LprogM) :
    ∀ (is : List LinstrRM) (ss : SSt) (V : String → Σ w, BitVec w) (A : String → ArrCell)
      (C O : Bool) (Z : Bool) (s : LstateMF), Holds V A C O Z ss s →
      (symRun is ss sym).DescN is.length (I.runL P is s) V A C O Z s
  | [], ss, V, A, C, O, Z, s, hs => by
      refine ⟨fun t ht => ?_, fun _ => rfl⟩
      cases ht
      exact ⟨allG_nil V A C O, hs, rfl, rfl, rfl⟩
  | i :: is, ss, V, A, C, O, Z, s, hs => by
      have hstep := hsym P i ss V A C O Z s hs
      simp only [symRun, Isa.runL]
      cases h1 : sym i ss with
      | ok ss1 g1 =>
          rw [h1] at hstep
          obtain ⟨hs1, hs2⟩ := hstep
          cases h2 : symRun is ss1 sym with
          | ok ss2 g2 =>
              simp only [h2, SOut.DescN]
              refine ⟨fun t ht => ?_, fun hg => ?_⟩
              · obtain ⟨s1, e1, e2⟩ := Option.bind_eq_some_iff.mp ht
                obtain ⟨hg1, hH1, hF1⟩ := hs1 s1 e1
                have ih := symRun_sound_at hsym P is ss1 V A C O Z s1 hH1
                rw [h2] at ih
                obtain ⟨hg2, hH2, hF2⟩ := ih.1 t e2
                refine ⟨allG_append.mpr ⟨hg1, hg2⟩, hH2, ?_, ?_, ?_⟩
                · rw [hF2.1, hF1.1]
                · rw [hF2.2.1, hF1.2.1, List.length_cons]; omega
                · rw [hF2.2.2, hF1.2.2]
              · obtain ⟨hg1, hg2⟩ := allG_append.mp hg
                obtain ⟨s1, e1⟩ := Option.isSome_iff_exists.mp (hs2 hg1)
                have ih := symRun_sound_at hsym P is ss1 V A C O Z s1 (hs1 s1 e1).2.1
                rw [h2] at ih
                rw [e1, Option.bind_some]
                exact ih.2 hg2
          | fail =>
              simp only [h2, SOut.DescN]
              cases e1 : I.step P i s with
              | none => rfl
              | some s1 =>
                  have ih := symRun_sound_at hsym P is ss1 V A C O Z s1 (hs1 s1 e1).2.1
                  rw [h2] at ih
                  exact ih
          | unk => simp only [h2, SOut.DescN]
      | fail =>
          rw [h1] at hstep
          simp only [SOut.DescN]
          simp only [SOut.Desc] at hstep
          rw [hstep, Option.bind_none]
      | unk => simp only [SOut.DescN]

/-- **The symbolic run describes the run exactly.** From every state `ss` describes, the
    steps of `is` succeed exactly when the guards of `symRun is ss` hold, and then end in
    a state its final symbolic state describes; a run `symRun` reports as failing fails. -/
theorem symRun_sound (P : LprogM) (is : List LinstrRM) (ss : SSt)
    (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) (Z : Bool)
    (s : LstateMF) (hs : Holds V A C O Z ss s) :
    (symRun is ss).DescN is.length (runL P is s) V A C O Z s := by
  have h := symRun_sound_at (I := x86Isa) symStep_sound P is ss V A C O Z s hs
  rwa [x86Isa_runL] at h

/-! ## 7. Written names, labels and the registers a value reads -/

theorem liftR_good {ss : SSt} (hg : ss.Good) {o : ROut} {ss' : SSt} {gs : List SG}
    (h : liftR ss o = .ok ss' gs) : ss'.Good := by
  cases o <;> simp only [liftR, SOut.ok.injEq, reduceCtorEq] at h
  · rw [← h.1]; exact hg.setR _ _
  · rw [← h.1]; exact hg

theorem symMem_good (i : LinstrRM) {ss : SSt} (hg : ss.Good) {ss' : SSt} {gs : List SG}
    (h : symMem i ss = .ok ss' gs) : ss'.Good := by
  obtain ⟨x, tag⟩ := i
  unfold symMem at h
  cases tag with
  | load w n =>
      dsimp only at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact hg.setR _ _
      · exact liftR_good hg h
  | store w n =>
      dsimp only at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact hg.setA _ _
      · exact liftR_good hg h
  | loadC => cases h
  | storeC => cases h
  | zero w n =>
      dsimp only at h
      split at h
      · split at h
        · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact hg.setA _ _
        · cases h
      · cases h
  | storeImm w n =>
      dsimp only at h
      split at h
      · split at h
        · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact hg.setA _ _
        · cases h
      · cases h
  | reg cd => exact liftR_good hg h

theorem symCarry_good {op : CarryOp} {d : String} {a b : LOperand} {ss : SSt} (hg : ss.Good)
    {ss' : SSt} {gs : List SG} (h : symCarry op d a b ss = .ok ss' gs) : ss'.Good := by
  unfold symCarry at h
  split at h
  · cases op <;> simp only [SOut.ok.injEq] at h <;> rw [← h.1] <;> exact hg.setR _ _
  · cases h

theorem symWide_good {w : WideOp} {ss : SSt} (hg : ss.Good) {ss' : SSt} {gs : List SG}
    (h : symWide w ss = .ok ss' gs) : ss'.Good := by
  cases w with
  | mov d b =>
      simp only [symWide] at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact hg.setR _ _
      · cases h
  | mulx lo hi b =>
      simp only [symWide] at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact (hg.setR _ _).setR _ _
      · cases h

theorem symStep_good (i : LinstrRM) {ss : SSt} (hg : ss.Good) {ss' : SSt} {gs : List SG}
    (h : symStep i ss = .ok ss' gs) : ss'.Good := by
  unfold symStep at h
  split at h
  · split at h
    · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact hg
    · cases h
  · split at h
    · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact hg.setR _ _
    · split at h
      · cases h
      · split at h
        · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact hg
        · cases h
        · cases h
        · split at h
          · exact symCarry_good hg h
          · split at h
            · exact symWide_good hg h
            · cases hm : symMem i ss with
              | ok s1 g1 =>
                  rw [hm] at h
                  simp only [aluFl, SOut.ok.injEq] at h
                  rw [← h.1]
                  have := symMem_good i hg hm
                  exact this
              | fail => rw [hm] at h; cases h
              | unk => rw [hm] at h; cases h

/-- A symbolic run keeps `SSt.Good` when every step of `sym` keeps it. -/
theorem symRun_good_at {sym : LinstrRM → SSt → SOut}
    (hgood : ∀ (i : LinstrRM) {ss : SSt}, ss.Good → ∀ {ss' : SSt} {gs : List SG},
      sym i ss = .ok ss' gs → ss'.Good) :
    ∀ (is : List LinstrRM) {ss : SSt}, ss.Good → ∀ {ss' : SSt} {gs : List SG},
    symRun is ss sym = .ok ss' gs → ss'.Good
  | [], ss, hg, ss', gs, h => by
      simp only [symRun, SOut.ok.injEq] at h; rw [← h.1]; exact hg
  | i :: is, ss, hg, ss', gs, h => by
      cases h1 : sym i ss with
      | ok ss1 g1 =>
          cases h2 : symRun is ss1 sym with
          | ok ss2 g2 =>
              simp only [symRun, h1, h2, SOut.ok.injEq] at h
              rw [← h.1]
              exact symRun_good_at hgood is (hgood i hg h1) h2
          | fail => simp [symRun, h1, h2] at h
          | unk => simp [symRun, h1, h2] at h
      | fail => simp [symRun, h1] at h
      | unk => simp [symRun, h1] at h

theorem symRun_good (is : List LinstrRM) {ss : SSt} (hg : ss.Good) {ss' : SSt} {gs : List SG}
    (h : symRun is ss = .ok ss' gs) : ss'.Good :=
  symRun_good_at (fun i _ hg _ _ h => symStep_good i hg h) is hg h

/-- A label declaration. -/
def isLbl (i : LinstrRM) : Bool :=
  match i.1 with
  | .Llabel _ _ => true
  | _ => false

theorem symStep_label {i : LinstrRM} (h : isLbl i = true) (ss : SSt) :
    symStep i ss = .ok ss [] := by
  obtain ⟨x, tag⟩ := i
  cases x <;> simp_all [isLbl, symStep, cmpArgs?, movRegArgs?, flagCondCC?]

/-- A label at the head of a list does not change its symbolic run, when `sym` describes a
    label as the identity. -/
theorem symRun_label_at {sym : LinstrRM → SSt → SOut}
    (hlab : ∀ {i : LinstrRM}, isLbl i = true → ∀ ss : SSt, sym i ss = .ok ss [])
    {i : LinstrRM} (h : isLbl i = true) (is : List LinstrRM) (ss : SSt) :
    symRun (i :: is) ss sym = symRun is ss sym := by
  simp only [symRun, hlab h]
  cases symRun is ss sym <;> simp

theorem symRun_label {i : LinstrRM} (h : isLbl i = true) (is : List LinstrRM) (ss : SSt) :
    symRun (i :: is) ss = symRun is ss :=
  symRun_label_at (fun h ss => symStep_label h ss) h is ss

mutual
/-- The start registers a symbolic word reads. -/
def STerm.vars : STerm → List String
  | .reg r => [r]
  | .immW _ _ => []
  | .immAt _ x => x.vars
  | .bin _ x y => x.vars ++ y.vars
  | .un _ x => x.vars
  | .shImm _ _ x => x.vars
  | .aget a _ _ i => a.vars ++ i.vars
  | .cin _ => []
  | .aluF _ _ x y o => x.vars ++ y.vars ++ o.vars
  | .carryW _ x y c => x.vars ++ y.vars ++ c.vars
  | .carryF _ _ x y c => x.vars ++ y.vars ++ c.vars
  | .mulx _ x y => x.vars ++ y.vars
  | .cout _ x y c => x.vars ++ y.vars ++ c.vars
  | .sel x y c => x.vars ++ y.vars ++ c.vars
  | .setcc _ x y => x.vars ++ y.vars
  | .ref _ => []

/-- The start registers a symbolic array reads. -/
def SArr.vars : SArr → List String
  | .cell _ => []
  | .aset a _ _ i v => a.vars ++ i.vars ++ v.vars
  | .zero _ _ => []
end

mutual
/-- The symbolic word reads the carry or the overflow flag at the start. -/
def STerm.readsF : STerm → Bool
  | .reg _ => false
  | .immW _ _ => false
  | .immAt _ x => x.readsF
  | .bin _ x y => x.readsF || y.readsF
  | .un _ x => x.readsF
  | .shImm _ _ x => x.readsF
  | .aget a _ _ i => a.readsF || i.readsF
  | .cin _ => true
  | .aluF _ _ x y o => x.readsF || y.readsF || o.readsF
  | .carryW _ x y c => x.readsF || y.readsF || c.readsF
  | .carryF _ _ x y c => x.readsF || y.readsF || c.readsF
  | .mulx _ x y => x.readsF || y.readsF
  | .cout _ x y c => x.readsF || y.readsF || c.readsF
  | .sel x y c => x.readsF || y.readsF || c.readsF
  | .setcc _ x y => x.readsF || y.readsF
  | .ref _ => false

/-- The symbolic array reads the carry or the overflow flag at the start. -/
def SArr.readsF : SArr → Bool
  | .cell _ => false
  | .aset a _ _ i v => a.readsF || i.readsF || v.readsF
  | .zero _ _ => false
end

/-- The start registers a symbolic flag reads. -/
def SFlag.vars : SFlag → List String
  | .init => []
  | .cmp x y => x.vars ++ y.vars

/-- The symbolic flag reads a flag at the start. -/
def SFlag.readsInit : SFlag → Bool
  | .init => true
  | .cmp x y => x.readsF || y.readsF

/-- The start registers a guard reads. -/
def SG.vars : SG → List String
  | .wid t _ => t.vars
  | .eqW x y => x.vars ++ y.vars
  | .shp a _ _ => a.vars

/-- The guard reads the carry or the overflow flag at the start. -/
def SG.readsF : SG → Bool
  | .wid t _ => t.readsF
  | .eqW x y => x.readsF || y.readsF
  | .shp a _ _ => a.readsF

mutual
theorem STerm.ev_congr {V V' : String → Σ w, BitVec w} (A : String → ArrCell)
    {C O C' O' : Bool} :
    ∀ (t : STerm), (∀ r ∈ t.vars, V r = V' r) → (t.readsF = true → C = C' ∧ O = O') →
      t.ev V A C O = t.ev V' A C' O'
  | .reg r, h, _ => h r (by simp [STerm.vars])
  | .immW _ _, _, _ => rfl
  | .immAt _ x, h, hf => by
      rw [STerm.ev, STerm.ev, STerm.ev_congr A x
        (fun r hr => h r (by simpa [STerm.vars] using hr))
        (fun e => hf (by simpa [STerm.readsF] using e))]
  | .bin _ x y, h, hf => by
      rw [STerm.ev, STerm.ev,
        STerm.ev_congr A x (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A y (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e]))]
  | .un _ x, h, hf => by
      rw [STerm.ev, STerm.ev, STerm.ev_congr A x
        (fun r hr => h r (by simpa [STerm.vars] using hr))
        (fun e => hf (by simpa [STerm.readsF] using e))]
  | .shImm _ _ x, h, hf => by
      rw [STerm.ev, STerm.ev, STerm.ev_congr A x
        (fun r hr => h r (by simpa [STerm.vars] using hr))
        (fun e => hf (by simpa [STerm.readsF] using e))]
  | .aget a _ _ i, h, hf => by
      simp only [STerm.ev,
        SArr.ev_congr A a (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A i (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e]))]
  | .cin _, _, hf => by
      obtain ⟨rfl, rfl⟩ := hf rfl
      rfl
  | .aluF _ _ x y o, h, hf => by
      simp only [STerm.ev,
        STerm.ev_congr A x (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A y (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A o (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e]))]
  | .carryW _ x y c, h, hf => by
      simp only [STerm.ev,
        STerm.ev_congr A x (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A y (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A c (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e]))]
  | .carryF _ _ x y c, h, hf => by
      simp only [STerm.ev,
        STerm.ev_congr A x (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A y (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A c (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e]))]
  | .mulx _ x y, h, hf => by
      simp only [STerm.ev,
        STerm.ev_congr A x (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A y (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e]))]
  | .cout _ x y c, h, hf => by
      simp only [STerm.ev,
        STerm.ev_congr A x (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A y (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A c (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e]))]
  | .sel x y c, h, hf => by
      rw [STerm.ev, STerm.ev,
        STerm.ev_congr A x (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A y (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A c (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e]))]
  | .setcc _ x y, h, hf => by
      rw [STerm.ev, STerm.ev,
        STerm.ev_congr A x (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e])),
        STerm.ev_congr A y (fun r hr => h r (by simp [STerm.vars, hr]))
          (fun e => hf (by simp [STerm.readsF, e]))]
  | .ref _, _, _ => rfl

theorem SArr.ev_congr {V V' : String → Σ w, BitVec w} (A : String → ArrCell)
    {C O C' O' : Bool} :
    ∀ (a : SArr), (∀ r ∈ a.vars, V r = V' r) → (a.readsF = true → C = C' ∧ O = O') →
      a.ev V A C O = a.ev V' A C' O'
  | .cell _, _, _ => rfl
  | .aset a _ _ i v, h, hf => by
      simp only [SArr.ev,
        SArr.ev_congr A a (fun r hr => h r (by simp [SArr.vars, hr]))
          (fun e => hf (by simp [SArr.readsF, e])),
        STerm.ev_congr A i (fun r hr => h r (by simp [SArr.vars, hr]))
          (fun e => hf (by simp [SArr.readsF, e])),
        STerm.ev_congr A v (fun r hr => h r (by simp [SArr.vars, hr]))
          (fun e => hf (by simp [SArr.readsF, e]))]
  | .zero _ _, _, _ => rfl
end

theorem SFlag.ev_congr {V V' : String → Σ w, BitVec w} (A : String → ArrCell)
    {C O C' O' Z Z' : Bool} (f : SFlag) (h : ∀ r ∈ f.vars, V r = V' r)
    (hz : f.readsInit = true → Z = Z' ∧ C = C' ∧ O = O') :
    f.ev V A C O Z = f.ev V' A C' O' Z' := by
  cases f with
  | init => exact (hz rfl).1
  | cmp x y =>
      simp only [SFlag.ev,
        STerm.ev_congr A x (fun r hr => h r (by simp [SFlag.vars, hr]))
          (fun e => (hz (by simp [SFlag.readsInit, e])).2),
        STerm.ev_congr A y (fun r hr => h r (by simp [SFlag.vars, hr]))
          (fun e => (hz (by simp [SFlag.readsInit, e])).2)]

theorem SG.holds_congr {V V' : String → Σ w, BitVec w} (A : String → ArrCell)
    {C O C' O' : Bool} (g : SG) (h : ∀ r ∈ g.vars, V r = V' r)
    (hf : g.readsF = true → C = C' ∧ O = O') : g.holds V A C O ↔ g.holds V' A C' O' := by
  cases g with
  | wid t w => simp only [SG.holds, STerm.ev_congr A t (fun r hr => h r hr) hf]
  | eqW x y =>
      simp only [SG.holds,
        STerm.ev_congr A x (fun r hr => h r (by simp [SG.vars, hr]))
          (fun e => hf (by simp [SG.readsF, e])),
        STerm.ev_congr A y (fun r hr => h r (by simp [SG.vars, hr]))
          (fun e => hf (by simp [SG.readsF, e]))]
  | shp a w n => rw [SG.holds, SG.holds, SArr.ev_congr A a (fun r hr => h r hr) hf]

/-! ## 8. Straight-line stretches of a run -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG

section Run

variable {fn : String} {B : List LinstrRM}

theorem findInstrMem_single {s : LstateMF} (hfn : s.prog.lfn = fn) :
    findInstrMem (singletonProgM fn B) s.prog = B[s.prog.base.reg.lpc]? := by
  simp [findInstrMem, singletonProgM, hfn]
  rfl

theorem step_plain {x : LinstrRM} (hx : isTermR x.1 = false) {s t : LstateMF}
    (h : evalInstrPMemF (singletonProgM fn B) x s = some t) :
    t.prog.lfn = s.prog.lfn ∧ t.prog.base.reg.lpc = s.prog.base.reg.lpc + 1 := by
  obtain ⟨h1, h2⟩ := evalInstrPMemF_next _ x s t h
  exact ⟨h1, nextPc_plain hx h2⟩

/-- A step of the instruction set `I` at an instruction that is no terminator stays in the
    function and advances the pc by one. -/
def StepPlain (I : Isa) : Prop :=
  ∀ (P : LprogM) {x : LinstrRM}, isTermR x.1 = false → ∀ {s t : LstateMF},
    I.step P x s = some t →
    t.prog.lfn = s.prog.lfn ∧ t.prog.base.reg.lpc = s.prog.base.reg.lpc + 1

theorem stepPlain_x86 : StepPlain x86Isa := by
  intro P x hx s t h
  obtain ⟨h1, h2⟩ := evalInstrPMemF_next P x s t h
  exact ⟨h1, nextPc_plain hx h2⟩

/-- A halting run of the instruction set `I` from the start of a stretch `xs` of
    non-terminators of the body runs `xs` and then the rest, when a non-terminator step of
    `I` stays in the function and advances the pc by one (`StepPlain`). -/
theorem fuel_runL_at {I : Isa} (hpl : StepPlain I) :
    ∀ (xs rest : List LinstrRM) (s t : LstateMF) (fuel : Nat), s.prog.lfn = fn →
      B.drop s.prog.base.reg.lpc = xs ++ rest → (∀ x ∈ xs, isTermR x.1 = false) →
      I.lsemFuelMemF (singletonProgM fn B) fuel s = some t →
      ∃ u f, fuel = xs.length + f ∧ I.runL (singletonProgM fn B) xs s = some u ∧
        I.lsemFuelMemF (singletonProgM fn B) f u = some t
  | [], _, s, t, fuel, _, _, _, h => ⟨s, fuel, by simp, rfl, h⟩
  | x :: xs, rest, s, t, fuel, hfn, hB, hx, h => by
      have hget : B[s.prog.base.reg.lpc]? = some x := by
        rw [← List.head?_drop, hB]; rfl
      cases fuel with
      | zero =>
          simp [Isa.lsemFuelMemF, findInstrMem_single hfn, hget] at h
      | succ f =>
          simp only [Isa.lsemFuelMemF, findInstrMem_single hfn, hget] at h
          cases he : I.step (singletonProgM fn B) x s with
          | none => rw [he] at h; cases h
          | some s1 =>
              rw [he] at h
              obtain ⟨h1, h2⟩ := hpl _ (hx x (by simp)) he
              have hB1 : B.drop s1.prog.base.reg.lpc = xs ++ rest := by
                rw [h2, ← List.drop_drop, hB]; rfl
              obtain ⟨u, f', hf, hu, hrun⟩ := fuel_runL_at hpl xs rest s1 t f (h1.trans hfn) hB1
                (fun y hy => hx y (by simp [hy])) h
              refine ⟨u, f', by simp [hf]; omega, ?_, hrun⟩
              simp [Isa.runL, he, hu]

/-- A halting run from the start of a stretch `xs` of non-terminators of the body runs
    `xs` and then the rest. -/
theorem fuel_runL (xs rest : List LinstrRM) (s t : LstateMF) (fuel : Nat)
    (hfn : s.prog.lfn = fn) (hB : B.drop s.prog.base.reg.lpc = xs ++ rest)
    (hx : ∀ x ∈ xs, isTermR x.1 = false)
    (h : lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ u f, fuel = xs.length + f ∧ runL (singletonProgM fn B) xs s = some u ∧
      lsemFuelMemF (singletonProgM fn B) f u = some t := by
  rw [← x86Isa_lsemFuelMemF] at h
  simpa only [x86Isa_lsemFuelMemF, x86Isa_runL] using
    fuel_runL_at stepPlain_x86 xs rest s t fuel hfn hB hx h

/-- A run of a stretch `xs` of non-terminators of the body is the first `xs.length` steps
    of every run of the instruction set `I` from its start. -/
theorem runL_fuel_at {I : Isa} (hpl : StepPlain I) :
    ∀ (xs rest : List LinstrRM) (s u : LstateMF), s.prog.lfn = fn →
      B.drop s.prog.base.reg.lpc = xs ++ rest → (∀ x ∈ xs, isTermR x.1 = false) →
      I.runL (singletonProgM fn B) xs s = some u → ∀ f,
      I.lsemFuelMemF (singletonProgM fn B) (xs.length + f) s =
        I.lsemFuelMemF (singletonProgM fn B) f u
  | [], _, s, u, _, _, _, h, f => by
      simp only [Isa.runL, Option.some.injEq] at h; subst h; simp
  | x :: xs, rest, s, u, hfn, hB, hx, h, f => by
      have hget : B[s.prog.base.reg.lpc]? = some x := by
        rw [← List.head?_drop, hB]; rfl
      simp only [Isa.runL] at h
      cases he : I.step (singletonProgM fn B) x s with
      | none => rw [he] at h; cases h
      | some s1 =>
          rw [he, Option.bind_some] at h
          obtain ⟨h1, h2⟩ := hpl _ (hx x (by simp)) he
          have hB1 : B.drop s1.prog.base.reg.lpc = xs ++ rest := by
            rw [h2, ← List.drop_drop, hB]; rfl
          rw [List.length_cons, show xs.length + 1 + f = (xs.length + f) + 1 by omega]
          simp only [Isa.lsemFuelMemF, findInstrMem_single hfn, hget, he]
          exact runL_fuel_at hpl xs rest s1 u (h1.trans hfn) hB1
            (fun y hy => hx y (by simp [hy])) h f

/-- A run of a stretch `xs` of non-terminators of the body is the first `xs.length` steps
    of every run from its start. -/
theorem runL_fuel (xs rest : List LinstrRM) (s u : LstateMF) (hfn : s.prog.lfn = fn)
    (hB : B.drop s.prog.base.reg.lpc = xs ++ rest) (hx : ∀ x ∈ xs, isTermR x.1 = false)
    (h : runL (singletonProgM fn B) xs s = some u) (f : Nat) :
    lsemFuelMemF (singletonProgM fn B) (xs.length + f) s =
      lsemFuelMemF (singletonProgM fn B) f u := by
  rw [← x86Isa_runL] at h
  simpa only [x86Isa_lsemFuelMemF] using runL_fuel_at stepPlain_x86 xs rest s u hfn hB hx h f

end Run

/-! ## 9. Terminators -/

theorem evalJumpMem_single {fn : String} {B : List LinstrRM} {l : LLabel} {q : Nat}
    (hq : findLabel l (B.map Prod.fst) = some q) (p : LstatePM) :
    evalJumpMem (singletonProgM fn B) l p = some { p with base := p.base.setLpc (q + 1) } := by
  simp [evalJumpMem, findLabelMem, singletonProgM, hq]

/-- The symbolic value of a branch condition: the zero flag against a polarity, a register
    tested for non-zero at width `64`, or a constant. -/
inductive SDec where
  | flag (pol : Bool) (z : SFlag)
  | nz (t : STerm)
  | const (b : Bool)
  deriving DecidableEq

/-- The symbolic value of the condition `c` in the symbolic state `ss`. -/
def symDec (ss : SSt) (c : LOperand) : SDec :=
  match ccPol c with
  | some pol => .flag pol ss.zf
  | none =>
      match c with
      | .reg r => .nz (ss.regs r)
      | .imm n => .const (decide (BitVec.ofNat 64 n ≠ 0#64))
      | _ => .const false

/-- The value of a symbolic branch condition. -/
def SDec.ev (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) (Z : Bool) :
    SDec → Bool
  | .flag pol z => z.ev V A C O Z == pol
  | .nz t => if (t.ev V A C O).1 = 64 then decide (castW (t.ev V A C O) 64 ≠ 0#64) else false
  | .const b => b

/-- The start registers a symbolic branch condition reads. -/
def SDec.vars : SDec → List String
  | .flag _ z => z.vars
  | .nz t => t.vars
  | .const _ => []

/-- The symbolic branch condition reads a flag at the start. -/
def SDec.readsInit : SDec → Bool
  | .flag _ z => z.readsInit
  | .nz t => t.readsF
  | .const _ => false

theorem decC_eq {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool} {Z : Bool}
    {ss : SSt} {s : LstateMF} (hs : Holds V A C O Z ss s) (c : LOperand) :
    decC s c = (symDec ss c).ev V A C O Z := by
  unfold decC symDec
  cases ccPol c with
  | some pol => simp [SDec.ev, hs.2.2.1]
  | none =>
      cases c with
      | reg r =>
          simp only [SDec.ev, condNZ, evalOperandN, getW_eq, hs.1 r]
          split_ifs <;> rfl
      | imm n => rfl
      | arr _ _ => rfl
      | arrIdx _ _ _ => rfl

theorem SDec.ev_congr {V V' : String → Σ w, BitVec w} (A : String → ArrCell)
    {C O C' O' Z Z' : Bool} (d : SDec) (h : ∀ r ∈ d.vars, V r = V' r)
    (hz : d.readsInit = true → Z = Z' ∧ C = C' ∧ O = O') :
    d.ev V A C O Z = d.ev V' A C' O' Z' := by
  cases d with
  | flag pol z => simp only [SDec.ev, SFlag.ev_congr A z h hz]
  | nz t => rw [SDec.ev, SDec.ev, STerm.ev_congr A t h (fun e => (hz e).2)]
  | const b => rfl

/-! ## 10. The checker -/

/-- The index one past the last instruction of block `b` before its terminator. -/
def bstopOf (T : Term) (b : Block) : Nat :=
  match T with
  | .fall _ => b.stop
  | _ => b.stop - 1

/-- The instructions of block `b` of body `B` before its terminator `T`. -/
def bodyAt (B : List LinstrRM) (b : Block) (T : Term) : List LinstrRM :=
  (B.drop b.start).take (bstopOf T b - b.start)

/-- Every name of `vs` is in the live set `n`. -/
def vIn (n : List String × Bool) (vs : List String) : Bool := vs.all (fun v => n.1.contains v)

/-- A value reading the names `vs` may be compared at a block with live set `n`: every name
    is live, and the flags are live when the value reads a flag at the start (`rf`). -/
def okIn (n : List String × Bool) (vs : List String) (rf : Bool) : Bool :=
  vIn n vs && (!rf || n.2)

/-! ### Agreement at every evaluation

The checker on the term table (`blockOkR`) accepts two exit words that are not one word when
their canonical keys agree (`canonEqT`), and a guard of the rewritten block that is not one
of the source block when the widths of the canonical keys decide it (`SG.impT`). The check
`blockOk` that its soundness is stated for reads these as the facts they establish: the two
words evaluate alike, and the guard holds, at every evaluation where the guards of the source
block hold. These two tests are classical; the checker never evaluates them. -/

/-- The words `t` and `t'` evaluate alike at every evaluation where the guards `gs` hold. -/
noncomputable def STerm.semEqG (gs : List SG) (t t' : STerm) : Bool :=
  @decide (∀ (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool),
    AllG V A C O gs → t.ev V A C O = t'.ev V A C O) (Classical.propDecidable _)

/-- The guard `g` holds at every evaluation where the guards `gs` hold. -/
noncomputable def SG.impG (gs : List SG) (g : SG) : Bool :=
  @decide (∀ (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool),
    AllG V A C O gs → g.holds V A C O) (Classical.propDecidable _)

/-- The exit words `t` (source) and `t'` (rewritten) of a register agree at a block with live
    set `n` under the guards `gs` of the source block: they are one word, or they evaluate
    alike wherever `gs` hold and `t'` may be compared at the block; and `t` may be compared at
    the block. -/
noncomputable def regAgree (n : List String × Bool) (gs : List SG) (t t' : STerm) : Bool :=
  (t == t' || (STerm.semEqG gs t t' && okIn n t'.vars t'.readsF)) && okIn n t.vars t.readsF

theorem STerm.semEqG_spec {gs : List SG} {t t' : STerm} (h : STerm.semEqG gs t t' = true)
    {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool} (hg : AllG V A C O gs) :
    t.ev V A C O = t'.ev V A C O :=
  @of_decide_eq_true _ (Classical.propDecidable _) h V A C O hg

theorem SG.impG_spec {gs : List SG} {g : SG} (h : SG.impG gs g = true)
    {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool} (hg : AllG V A C O gs) :
    g.holds V A C O :=
  @of_decide_eq_true _ (Classical.propDecidable _) h V A C O hg

theorem STerm.semEqG_of {gs : List SG} {t t' : STerm}
    (h : ∀ (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool),
      AllG V A C O gs → t.ev V A C O = t'.ev V A C O) : STerm.semEqG gs t t' = true :=
  @decide_eq_true _ (Classical.propDecidable _) h

theorem SG.impG_of {gs : List SG} {g : SG}
    (h : ∀ (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool),
      AllG V A C O gs → g.holds V A C O) : SG.impG gs g = true :=
  @decide_eq_true _ (Classical.propDecidable _) h

/-- **The laws of a symbolic step against an instruction set.** The symbolic step `sym` and
    the symbolic branch condition `dec` describe the instruction set `I`: `sym` describes
    `I.step` exactly (`step_sound`), `dec` evaluates to `I.condEval` (`dec_sound`), `sym`
    keeps `SSt.Good` (`good`) and describes a label as the identity (`label`), a step of `I`
    at an instruction that is no terminator stays in the function and advances the pc by one
    (`plain`), and `I` takes no step at `Lret` (`ret`). The soundness of the checker is proved
    from these laws. -/
structure SymLaws (I : Isa) (sym : LinstrRM → SSt → SOut) (dec : SSt → LOperand → SDec) :
    Prop where
  /-- The symbolic step describes the step exactly. -/
  step_sound : ∀ (P : LprogM) (i : LinstrRM) (ss : SSt), StepSound (I.step P i) ss (sym i ss)
  /-- The symbolic branch condition evaluates to the branch condition. -/
  dec_sound : ∀ {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O Z : Bool}
    {ss : SSt} {s : LstateMF}, Holds V A C O Z ss s → ∀ c : LOperand,
    I.condEval s c = (dec ss c).ev V A C O Z
  /-- The symbolic step keeps `SSt.Good`. -/
  good : ∀ (i : LinstrRM) {ss : SSt}, ss.Good → ∀ {ss' : SSt} {gs : List SG},
    sym i ss = .ok ss' gs → ss'.Good
  /-- The symbolic step of a label is the identity, with no guard. -/
  label : ∀ {i : LinstrRM}, isLbl i = true → ∀ ss : SSt, sym i ss = .ok ss []
  /-- A step at an instruction that is no terminator stays in the function and advances the
      pc by one. -/
  plain : StepPlain I
  /-- The instruction set takes no step at `Lret`. -/
  ret : ∀ (P : LprogM) (tag : MemTag) (s : LstateMF), I.step P (.Lret, tag) s = none

/-- The x86 symbolic step `symStep` and branch condition `symDec` satisfy the laws against
    `x86Isa`. -/
theorem symLaws_x86 : SymLaws x86Isa symStep symDec where
  step_sound := symStep_sound
  dec_sound := fun hs c => decC_eq hs c
  good := fun i _ hg _ _ h => symStep_good i hg h
  label := fun h ss => symStep_label h ss
  plain := stepPlain_x86
  ret := evalInstrPMemF_ret

/-- The two terminator instructions agree: two jumps name the same function, and two
    branches have the same symbolic condition under `dec`, which reads only live names. -/
def termAgree (T : Term) (n : List String × Bool) (ss ss' : SSt) :
    Option LinstrRM → Option LinstrRM → optParam (SSt → LOperand → SDec) symDec → Bool
  | some (.Lgoto (a, _), _), some (.Lgoto (b, _), _), _ =>
      match T with
      | .goto _ => a == b
      | _ => false
  | some (.Lcond c _, _), some (.Lcond c' _, _), dec =>
      match T with
      | .cond _ _ =>
          dec ss c == dec ss' c' && vIn n (dec ss c).vars &&
            (!(dec ss c).readsInit || n.2)
      | _ => false
  | _, _, _ =>
      match T with
      | .fall _ => true
      | _ => false

/-! ### Arrays up to stores of the element read

A store that writes to an element of an array the word read from that element at the same
shape leaves the array as it is. `SArr.same` relates two symbolic arrays that differ by such
stores; the guards of a run give the shape of the array read. -/

/-- The store of `v` to element `i` of the array `b` at shape `(w, n)` writes the word read
    there: `v` is element `i` of `b` read at shape `(w, n)`, and `gs` has the guard that `b`
    has that shape. -/
def SArr.selfSt (gs : List SG) (b : SArr) (w n : Nat) (i v : STerm) : Bool :=
  v == .aget b w n i && gs.contains (.shp b w n)

/-- The symbolic arrays `a` and `a'` are equal up to stores of the element read
    (`SArr.selfSt`), those of `a` under the guards `gs` and those of `a'` under `gs'`. -/
def SArr.same (gs gs' : List SG) : SArr → SArr → Bool
  | .cell r, .cell r' => r == r'
  | .cell r, .aset b' w' n' i' v' =>
      SArr.selfSt gs' b' w' n' i' v' && SArr.same gs gs' (.cell r) b'
  | .aset b w n i v, .cell r' => SArr.selfSt gs b w n i v && SArr.same gs gs' b (.cell r')
  | .aset b w n i v, .aset b' w' n' i' v' =>
      (SArr.selfSt gs b w n i v && SArr.same gs gs' b (.aset b' w' n' i' v')) ||
        (SArr.selfSt gs' b' w' n' i' v' && SArr.same gs gs' (.aset b w n i v) b') ||
        (w == w' && n == n' && i == i' && v == v' && SArr.same gs gs' b b')
  | .zero w n, .zero w' n' => w == w' && n == n'
  | .zero w n, .aset b' w' n' i' v' =>
      SArr.selfSt gs' b' w' n' i' v' && SArr.same gs gs' (.zero w n) b'
  | .aset b w n i v, .zero w' n' =>
      SArr.selfSt gs b w n i v && SArr.same gs gs' b (.zero w' n')
  | .cell _, .zero _ _ => false
  | .zero _ _, .cell _ => false
termination_by a a' => sizeOf a + sizeOf a'

/-- **A store of the element read leaves the array.** Under guards that hold, the array with
    the store has the value of the array without it. -/
theorem SArr.selfSt_ev {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {gs : List SG} (hg : AllG V A C O gs) {b : SArr} {w n : Nat} {i v : STerm}
    (h : SArr.selfSt gs b w n i v = true) :
    (SArr.aset b w n i v).ev V A C O = b.ev V A C O := by
  simp only [SArr.selfSt, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨rfl, hm⟩ := h
  obtain ⟨hw, hn⟩ := hg _ hm
  simp only [SArr.ev, STerm.ev]
  generalize b.ev V A C O = c at hw hn
  obtain ⟨w0, n0, f⟩ := c
  simp only at hw hn
  subst hw hn
  have hc : castA ⟨w0, n0, f⟩ w0 n0 = f := by simp [castA]
  have hs : ∀ k, stackSet f k (stackGet f k) = f := by
    intro k
    cases n0 with
    | zero => funext j; exact Fin.elim0 j
    | succ m =>
        funext j
        show (if j = _ then _ else f j) = f j
        split
        · next h => subst h; rfl
        · rfl
  rw [hc]
  simp [castW, hs]

/-- **Arrays equal up to stores of the element read have one value**, under guards that
    hold. -/
theorem SArr.same_ev {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {gs gs' : List SG} (hg : AllG V A C O gs) (hg' : AllG V A C O gs') (a a' : SArr)
    (h : SArr.same gs gs' a a' = true) : a.ev V A C O = a'.ev V A C O := by
  fun_induction SArr.same gs gs' a a' with
  | case1 r r' => simp only [beq_iff_eq] at h; rw [h]
  | case2 r b' w' n' i' v' ih =>
      simp only [Bool.and_eq_true] at h
      rw [SArr.selfSt_ev hg' h.1]; exact ih h.2
  | case3 b w n i v r' ih =>
      simp only [Bool.and_eq_true] at h
      rw [SArr.selfSt_ev hg h.1]; exact ih h.2
  | case4 b w n i v b' w' n' i' v' ih1 ih2 ih3 =>
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with (h | h) | h
      · rw [SArr.selfSt_ev hg h.1]; exact ih1 h.2
      · rw [SArr.selfSt_ev hg' h.1]; exact ih2 h.2
      · obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hb⟩ := h
        simp only [SArr.ev, ih3 hb]
  | case5 w n w' n' => grind only
  | case6 w n b' w' n' i' v' ih =>
      simp only [Bool.and_eq_true] at h
      rw [SArr.selfSt_ev hg' h.1]; exact ih h.2
  | case7 b w n i v w' n' ih =>
      simp only [Bool.and_eq_true] at h
      rw [SArr.selfSt_ev hg h.1]; exact ih h.2
  | case8 => simp at h
  | case9 => simp at h

/-- The final arrays `a` and `a'` of one name agree at a block with live set `n`: they are
    one symbolic array that passes `okIn n`, or they are equal up to stores of the element
    read (`SArr.same`, under the guards `gs` and `gs'` of the two runs) and `a'` passes
    `okIn n`. -/
def arrAgree (n : List String × Bool) (gs gs' : List SG) (a a' : SArr) : Bool :=
  (a == a' && okIn n a.vars a.readsF) ||
    (SArr.same gs gs' a a' && okIn n a'.vars a'.readsF)

/-- The two final symbolic states agree at every exit of a block with live set `n` and
    terminator `T`: on the registers live at each successor and, when the flags are live
    there, on the zero, carry and overflow flags; on `outs` when the block may leave the
    body; and on every array written, up to stores of the element read (`arrAgree`, under
    the guards `gs` and `gs'` of the two runs). A register agrees when its two words are one
    word or evaluate alike wherever the guards `gs` of the source run hold (`regAgree`).
    Every value compared passes `okIn n`. -/
noncomputable def exitAgree (outs : List String) (L : Nat → List String × Bool)
    (n : List String × Bool)
    (T : Term) (ss ss' : SSt) (gs gs' : List SG) : Bool :=
  T.succs.all (fun j =>
      (L j).1.all (fun r => regAgree n gs (ss.regs r) (ss'.regs r)) &&
        (!(L j).2 || (ss.zf == ss'.zf && okIn n ss.zf.vars ss.zf.readsInit &&
          ss.cf == ss'.cf && okIn n ss.cf.vars ss.cf.readsF &&
          ss.of == ss'.of && okIn n ss.of.vars ss.of.readsF))) &&
    (!T.halts || outs.all (fun r => regAgree n gs (ss.regs r) (ss'.regs r))) &&
    (ss.awr ++ ss'.awr).all (fun q => arrAgree n gs gs' (ss.arrs q) (ss'.arrs q))

/-- The check of block `k` of the source body `B` (block `b`) against block `k` of the
    rewritten body `B'` (block `b'`), both with terminator `T`, for the live sets `L`, under
    the symbolic step `sym` and branch condition `dec`. -/
noncomputable def blockOk (outs : List String) (L : Nat → List String × Bool) (k : Nat)
    (T : Term) (B B' : List LinstrRM) (b b' : Block) (sym : LinstrRM → SSt → SOut := symStep)
    (dec : SSt → LOperand → SDec := symDec) : Bool :=
  match T with
  | .ret => true
  | _ =>
      match symRun (bodyAt B b T) SSt.start sym with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          match symRun (bodyAt B' b' T) SSt.start sym with
          | .ok ss' gs' =>
              (normG gs').all (fun g =>
                  ((normG gs).contains g || SG.impG gs g) && okIn (L k) g.vars g.readsF) &&
                termAgree T (L k) ss ss' B[b.stop - 1]? B'[b'.stop - 1]? dec &&
                exitAgree outs L (L k) T ss ss' gs gs'
          | _ => false

/-- The checker for the live sets `L`: the two bodies are non-empty, their graphs have the
    same number of blocks and the same terminators, and every block pair passes
    `blockOk`. -/
noncomputable def ownedCheckWith (outs : List String) (L : Nat → List String × Bool)
    (B B' : List LinstrRM) (sym : LinstrRM → SSt → SOut := symStep)
    (dec : SSt → LOperand → SDec := symDec) : Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      !B.isEmpty && !B'.isEmpty && G.blocks.size == G'.blocks.size &&
        (List.range G.blocks.size).all (fun k =>
          (G.blk k).term == (G'.blk k).term &&
            blockOk outs L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym dec)
  | _, _ => false

/-- The agreement of a source state `s` and a rewritten state `s'` at a block entry with
    live set `n`: the function, the arrays, the word memory, the live registers, and the
    zero, carry and overflow flags when the flags are live. -/
def Rel (n : List String × Bool) (s s' : LstateMF) : Prop :=
  s'.prog.lfn = s.prog.lfn ∧ s'.prog.base.larr = s.prog.base.larr ∧
    s'.prog.base.lmem = s.prog.base.lmem ∧
    (∀ r ∈ n.1, s'.prog.base.reg.lvm r = s.prog.base.reg.lvm r) ∧
    (n.2 = true → s'.zf = s.zf ∧ s'.prog.base.cf = s.prog.base.cf ∧
      s'.prog.base.of = s.prog.base.of)

/-- The observable agreement of two end states: the registers `outs`, the arrays and the
    word memory. -/
def Obs (outs : List String) (t t' : LstateMF) : Prop :=
  (∀ r ∈ outs, t'.prog.base.reg.lvm r = t.prog.base.reg.lvm r) ∧
    t'.prog.base.larr = t.prog.base.larr ∧ t'.prog.base.lmem = t.prog.base.lmem

theorem vIn_spec {n : List String × Bool} {vs : List String} (h : vIn n vs = true) :
    ∀ v ∈ vs, v ∈ n.1 := by
  simpa [vIn] using h

theorem okIn_spec {n : List String × Bool} {vs : List String} {rf : Bool}
    (h : okIn n vs rf = true) : (∀ v ∈ vs, v ∈ n.1) ∧ (rf = true → n.2 = true) := by
  simp only [okIn, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨vIn_spec h.1, fun hr => ?_⟩
  rcases h.2 with h2 | h2
  · rw [hr] at h2; cases h2
  · exact h2

theorem exitAgree_spec {outs : List String} {L : Nat → List String × Bool}
    {n : List String × Bool} {T : Term} {ss ss' : SSt} {gs gs' : List SG}
    (h : exitAgree outs L n T ss ss' gs gs' = true) :
    (∀ j ∈ T.succs,
      (∀ r ∈ (L j).1, regAgree n gs (ss.regs r) (ss'.regs r) = true) ∧
      ((L j).2 = true → ss.zf = ss'.zf ∧ okIn n ss.zf.vars ss.zf.readsInit = true ∧
        ss.cf = ss'.cf ∧ okIn n ss.cf.vars ss.cf.readsF = true ∧
        ss.of = ss'.of ∧ okIn n ss.of.vars ss.of.readsF = true)) ∧
    (T.halts = true → ∀ r ∈ outs, regAgree n gs (ss.regs r) (ss'.regs r) = true) ∧
    (∀ q ∈ ss.awr ++ ss'.awr, arrAgree n gs gs' (ss.arrs q) (ss'.arrs q) = true) := by
  simp only [exitAgree, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun j hj => ⟨(h1 j hj).1, fun hl => ?_⟩, fun hh r hr => ?_, h3⟩
  · rcases (h1 j hj).2 with h | ⟨⟨⟨⟨⟨e, z⟩, ec⟩, zc⟩, eo⟩, zo⟩
    · rw [hl] at h; cases h
    · exact ⟨e, z, ec, zc, eo, zo⟩
  · rcases h2 with h2 | h2
    · rw [hh] at h2; cases h2
    · exact h2 r hr

theorem exit_rel {outs : List String} {L : Nat → List String × Bool} {n : List String × Bool}
    {T : Term} {ss ss' : SSt} {V V' : String → Σ w, BitVec w} {A : String → ArrCell}
    {C O C' O' Z Z' : Bool} {u u' : LstateMF} (hH : Holds V A C O Z ss u)
    (hH' : Holds V' A C' O' Z' ss' u') (hV : ∀ r ∈ n.1, V' r = V r)
    (hZ : n.2 = true → Z' = Z ∧ C' = C ∧ O' = O) (hg : ss.Good) (hg' : ss'.Good)
    (hlfn : u'.prog.lfn = u.prog.lfn) (hmem : u'.prog.base.lmem = u.prog.base.lmem)
    {gs gs' : List SG} (hG : AllG V A C O gs) (hG' : AllG V A C O gs')
    (hex : exitAgree outs L n T ss ss' gs gs' = true) :
    (∀ j ∈ T.succs, Rel (L j) u u') ∧ (T.halts = true → Obs outs u u') := by
  obtain ⟨hs, hh, ha⟩ := exitAgree_spec hex
  have hterm : ∀ t : STerm, okIn n t.vars t.readsF = true → t.ev V' A C' O' = t.ev V A C O :=
    fun t ht => STerm.ev_congr A t (fun r hr => hV r ((okIn_spec ht).1 r hr))
      (fun e => (hZ ((okIn_spec ht).2 e)).2)
  have harr : u'.prog.base.larr = u.prog.base.larr := by
    funext q
    rw [hH'.2.1 q, hH.2.1 q]
    by_cases hq : q ∈ ss.awr ++ ss'.awr
    · have hq' := ha q hq
      simp only [arrAgree, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hq'
      rcases hq' with ⟨e, v⟩ | ⟨e, v⟩
      · rw [← e]
        exact SArr.ev_congr A _ (fun r hr => hV r ((okIn_spec v).1 r hr))
          (fun e => (hZ ((okIn_spec v).2 e)).2)
      · rw [SArr.same_ev hG hG' _ _ e]
        exact SArr.ev_congr A _ (fun r hr => hV r ((okIn_spec v).1 r hr))
          (fun e => (hZ ((okIn_spec v).2 e)).2)
    · simp only [List.mem_append, not_or] at hq
      rw [hg.2 q hq.1, hg'.2 q hq.2]
      rfl
  have hreg : ∀ r, regAgree n gs (ss.regs r) (ss'.regs r) = true →
      u'.prog.base.reg.lvm r = u.prog.base.reg.lvm r := by
    intro r h
    simp only [regAgree, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨e | ⟨hs, v'⟩, v⟩ := h
    · rw [hH'.1 r, hH.1 r, ← e]
      exact hterm _ v
    · rw [hH'.1 r, hH.1 r, hterm _ v']
      exact (STerm.semEqG_spec hs hG).symm
  refine ⟨fun j hj => ⟨hlfn, harr, hmem, fun r hr => ?_, fun hl => ?_⟩, fun hT => ?_⟩
  · exact hreg r ((hs j hj).1 r hr)
  · obtain ⟨e, z, ec, zc, eo, zo⟩ := (hs j hj).2 hl
    refine ⟨?_, ?_, ?_⟩
    · rw [hH'.2.2.1, hH.2.2.1, ← e]
      exact SFlag.ev_congr A _ (fun r hr => hV r ((okIn_spec z).1 r hr))
        (fun hr => hZ ((okIn_spec z).2 hr))
    · rw [hH'.2.2.2.1, hH.2.2.2.1, ← ec, hterm _ zc]
    · rw [hH'.2.2.2.2, hH.2.2.2.2, ← eo, hterm _ zo]
  · exact ⟨fun r hr => hreg r (hh hT r hr), harr, hmem⟩

/-! ## 11. Blocks of a checked body -/

theorem drop_split (B : List LinstrRM) {p q : Nat} (hpq : p ≤ q) :
    B.drop p = (B.drop p).take (q - p) ++ B.drop q := by
  conv_lhs => rw [← List.take_append_drop (q - p) (B.drop p)]
  rw [List.drop_drop]
  congr 2
  omega

theorem take_cons (B : List LinstrRM) {p q : Nat} (h : p < q) {x : LinstrRM}
    (hx : B[p]? = some x) : (B.drop p).take (q - p) = x :: (B.drop (p + 1)).take (q - (p + 1)) := by
  have hd : B.drop p = x :: B.drop (p + 1) := by
    rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hx).1]
    rw [List.getElem?_eq_some_iff] at hx
    obtain ⟨_, hx⟩ := hx
    rw [hx]
  rw [hd, show q - p = (q - (p + 1)) + 1 by omega, List.take_succ_cons]

theorem getElem?_map_fst {B : List LinstrRM} {i : Nat} {x : LinstrR}
    (h : (B.map Prod.fst)[i]? = some x) : ∃ y, B[i]? = some y ∧ y.1 = x := by
  rw [List.getElem?_map] at h
  cases hB : B[i]? with
  | none => rw [hB] at h; cases h
  | some y => rw [hB] at h; cases h; exact ⟨y, rfl, rfl⟩

/-- The instructions of a block before its terminator are not terminators. -/
theorem body_plain {B : List LinstrRM} {G : CFG} (hG : cfgOf (B.map Prod.fst) = some G)
    {k : Nat} (hk : k < G.blocks.size) {p : Nat} (hp : (G.blk k).start ≤ p) :
    ∀ x ∈ (B.drop p).take (bstopOf (G.blk k).term (G.blk k) - p), isTermR x.1 = false := by
  have F := blockFacts hG hk
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  simp only [List.length_take, List.length_drop, lt_min_iff] at hi
  have hget : B[p + i]? = some ((B.drop p).take (bstopOf (G.blk k).term (G.blk k) - p))[i] := by
    simp [List.getElem?_eq_getElem (show p + i < B.length by omega)]
  have hw : (B.map Prod.fst)[p + i]? =
      some ((B.drop p).take (bstopOf (G.blk k).term (G.blk k) - p))[i].1 := by
    rw [List.getElem?_map, hget]; rfl
  have hstop : bstopOf (G.blk k).term (G.blk k) ≤ (G.blk k).stop := by
    unfold bstopOf; split <;> omega
  by_cases hin : p + i + 1 < (G.blk k).stop
  · exact F.inner (p + i) _ (by omega) hin hw
  · have hlast : p + i = (G.blk k).stop - 1 := by omega
    have hterm := F.term
    rw [← hlast, hw] at hterm
    rcases termOk_spec hterm with ⟨nx, hT, hnt, _⟩ | ⟨_, _, _, hT, _, _, _⟩ |
        ⟨_, _, _, _, hT, _, _, _, _⟩ | ⟨hT, _⟩
    · exact hnt
    all_goals (simp only [bstopOf, hT] at hi; omega)

/-- A run of a stretch of non-terminators of the instruction set `I` stays in the function
    and advances the pc by the length of the stretch. -/
theorem runL_frame_at {fn : String} {B : List LinstrRM} {I : Isa} (hpl : StepPlain I) :
    ∀ (xs : List LinstrRM) (s u : LstateMF), (∀ x ∈ xs, isTermR x.1 = false) →
      I.runL (singletonProgM fn B) xs s = some u →
      u.prog.lfn = s.prog.lfn ∧ u.prog.base.reg.lpc = s.prog.base.reg.lpc + xs.length
  | [], s, u, _, h => by simp only [Isa.runL, Option.some.injEq] at h; subst h; simp
  | x :: xs, s, u, hx, h => by
      simp only [Isa.runL] at h
      cases he : I.step (singletonProgM fn B) x s with
      | none => rw [he] at h; cases h
      | some s1 =>
          rw [he, Option.bind_some] at h
          obtain ⟨h1, h2⟩ := hpl _ (hx x (by simp)) he
          obtain ⟨h3, h4⟩ := runL_frame_at hpl xs s1 u (fun y hy => hx y (by simp [hy])) h
          refine ⟨h3.trans h1, ?_⟩
          rw [h4, h2, List.length_cons]
          omega

theorem runL_frame {fn : String} {B : List LinstrRM} (xs : List LinstrRM) (s u : LstateMF)
    (hx : ∀ x ∈ xs, isTermR x.1 = false) (h : runL (singletonProgM fn B) xs s = some u) :
    u.prog.lfn = s.prog.lfn ∧ u.prog.base.reg.lpc = s.prog.base.reg.lpc + xs.length := by
  rw [← x86Isa_runL] at h
  exact runL_frame_at stepPlain_x86 xs s u hx h

/-- The first step of a halting run of the instruction set `I` from a state that fetches
    `i`. -/
theorem run_inv_at {I : Isa} {P : LprogM} {f : Nat} {s t : LstateMF} {i : LinstrRM}
    (h : I.lsemFuelMemF P f s = some t) (hi : findInstrMem P s.prog = some i) :
    ∃ f1 s1, f = f1 + 1 ∧ I.step P i s = some s1 ∧ I.lsemFuelMemF P f1 s1 = some t := by
  cases f with
  | zero => simp [Isa.lsemFuelMemF, hi] at h
  | succ f1 =>
      simp only [Isa.lsemFuelMemF, hi] at h
      cases he : I.step P i s with
      | none => rw [he] at h; cases h
      | some s1 => rw [he] at h; exact ⟨f1, s1, rfl, rfl, h⟩

theorem run_inv {P : LprogM} {f : Nat} {s t : LstateMF} {i : LinstrRM}
    (h : lsemFuelMemF P f s = some t) (hi : findInstrMem P s.prog = some i) :
    ∃ f1 s1, f = f1 + 1 ∧ evalInstrPMemF P i s = some s1 ∧ lsemFuelMemF P f1 s1 = some t := by
  rw [← x86Isa_lsemFuelMemF] at h
  obtain ⟨f1, s1, e, he, hr⟩ := run_inv_at (I := x86Isa) h hi
  exact ⟨f1, s1, e, he, by rwa [x86Isa_lsemFuelMemF] at hr⟩

/-- Control enters block `b` at its start, or one past it when the block starts with a
    label. -/
def EntryAt (B : List LinstrRM) (b : Block) (p : Nat) : Prop :=
  p = b.start ∨ (p = b.start + 1 ∧ ∃ x, B[b.start]? = some x ∧ isLbl x = true)

theorem entry_le {B : List LinstrRM} {G : CFG} (hG : cfgOf (B.map Prod.fst) = some G)
    {k : Nat} (hk : k < G.blocks.size) {p : Nat} (hp : EntryAt B (G.blk k) p) :
    (G.blk k).start ≤ p ∧ p ≤ bstopOf (G.blk k).term (G.blk k) := by
  have F := blockFacts hG hk
  rcases hp with rfl | ⟨rfl, x, hx, hl⟩
  · refine ⟨le_refl _, ?_⟩
    unfold bstopOf; split <;> have := F.lt <;> omega
  · refine ⟨by omega, ?_⟩
    unfold bstopOf
    split
    · have := F.lt; omega
    · by_contra hc
      have hs : (G.blk k).stop - 1 = (G.blk k).start := by have := F.lt; omega
      have hterm := F.term
      rw [hs, List.getElem?_map, hx] at hterm
      obtain ⟨xi, xt⟩ := x
      rename_i hT
      cases xi <;> simp only [isLbl, reduceCtorEq] at hl
      simp only [Option.map_some] at hterm
      cases h : (G.blk k).term <;> simp_all [termOk]

/-- The symbolic run from an entry of a block is the symbolic run of the block body, when
    `sym` describes a label as the identity. -/
theorem symRun_entry_at {sym : LinstrRM → SSt → SOut}
    (hlab : ∀ {i : LinstrRM}, isLbl i = true → ∀ ss : SSt, sym i ss = .ok ss [])
    {B : List LinstrRM} {b : Block} {T : Term} {p : Nat}
    (hp : EntryAt B b p) (hle : p ≤ bstopOf T b) :
    symRun ((B.drop p).take (bstopOf T b - p)) SSt.start sym =
      symRun (bodyAt B b T) SSt.start sym := by
  rcases hp with rfl | ⟨rfl, x, hx, hl⟩
  · rfl
  · unfold bodyAt
    rw [take_cons B (by omega) hx, symRun_label_at hlab hl]

theorem symRun_entry {B : List LinstrRM} {b : Block} {T : Term} {p : Nat}
    (hp : EntryAt B b p) (hle : p ≤ bstopOf T b) :
    symRun ((B.drop p).take (bstopOf T b - p)) SSt.start = symRun (bodyAt B b T) SSt.start :=
  symRun_entry_at (fun h ss => symStep_label h ss) hp hle

theorem blockOk_spec {outs : List String} {L : Nat → List String × Bool} {k : Nat} {T : Term}
    {B B' : List LinstrRM} {b b' : Block} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (h : blockOk outs L k T B B' b b' sym dec = true)
    (hT : T ≠ .ret) :
    symRun (bodyAt B b T) SSt.start sym = .fail ∨
      ∃ ss gs ss' gs', symRun (bodyAt B b T) SSt.start sym = .ok ss gs ∧
        symRun (bodyAt B' b' T) SSt.start sym = .ok ss' gs' ∧
        (∀ g ∈ normG gs',
          (∀ (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool),
            AllG V A C O gs → g.holds V A C O) ∧ (∀ v ∈ g.vars, v ∈ (L k).1) ∧
          (g.readsF = true → (L k).2 = true)) ∧
        termAgree T (L k) ss ss' B[b.stop - 1]? B'[b'.stop - 1]? dec = true ∧
        exitAgree outs L (L k) T ss ss' gs gs' = true := by
  have h2 : (match symRun (bodyAt B b T) SSt.start sym with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          match symRun (bodyAt B' b' T) SSt.start sym with
          | .ok ss' gs' =>
              (normG gs').all (fun g =>
                  ((normG gs).contains g || SG.impG gs g) && okIn (L k) g.vars g.readsF) &&
                termAgree T (L k) ss ss' B[b.stop - 1]? B'[b'.stop - 1]? dec &&
                exitAgree outs L (L k) T ss ss' gs gs'
          | _ => false) = true := by
    cases T with
    | ret => exact absurd rfl hT
    | _ => exact h
  cases hs : symRun (bodyAt B b T) SSt.start sym with
  | fail => exact Or.inl rfl
  | unk => rw [hs] at h2; cases h2
  | ok ss gs =>
      rw [hs] at h2
      cases ht : symRun (bodyAt B' b' T) SSt.start sym with
      | ok ss' gs' =>
          rw [ht] at h2
          simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
            List.contains_iff_mem] at h2
          obtain ⟨⟨hg, hta⟩, hex⟩ := h2
          refine Or.inr ⟨ss, gs, ss', gs', rfl, rfl, fun g hg' => ⟨fun V A C O hA => ?_,
            okIn_spec (hg g hg').2⟩, hta, hex⟩
          rcases (hg g hg').1 with hm | hi
          · exact allG_normG.mpr hA g hm
          · exact SG.impG_spec hi hA
      | fail => rw [ht] at h2; cases h2
      | unk => rw [ht] at h2; cases h2

theorem stop_next {B : List LinstrRM} {G : CFG} (hG : cfgOf (B.map Prod.fst) = some G)
    {k : Nat} (hk : k < G.blocks.size) :
    (G.next k = none → (G.blk k).stop = B.length) ∧
      (∀ j, G.next k = some j → j = k + 1 ∧ j < G.blocks.size ∧
        (G.blk k).stop = (G.blk j).start) := by
  have hse := (blockFacts hG hk).stop_eq
  refine ⟨fun hn => ?_, fun j hj => ?_⟩
  · rw [CFG.nextStart, hn] at hse
    simpa using hse
  · rw [CFG.nextStart, hj] at hse
    simp only [CFG.next] at hj
    split at hj
    · cases hj
      exact ⟨rfl, by assumption, hse⟩
    · cases hj

/-! ## 12. Soundness -/

/-- The facts `ownedCheckWith` establishes about the two bodies and their graphs. -/
structure Checked (outs : List String) (L : Nat → List String × Bool) (B B' : List LinstrRM)
    (G G' : CFG) (sym : LinstrRM → SSt → SOut := symStep)
    (dec : SSt → LOperand → SDec := symDec) : Prop where
  hG : cfgOf (B.map Prod.fst) = some G
  hG' : cfgOf (B'.map Prod.fst) = some G'
  size : G'.blocks.size = G.blocks.size
  blk : ∀ k < G.blocks.size, (G'.blk k).term = (G.blk k).term ∧
    blockOk outs L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym dec = true

/-- The two runs enter block `k` in the same way: both at the start, or both one past a
    label at the start. -/
def Pair (B B' : List LinstrRM) (b b' : Block) (p p' : Nat) : Prop :=
  (p = b.start ∧ p' = b'.start) ∨
    (p = b.start + 1 ∧ (∃ x, B[b.start]? = some x ∧ isLbl x = true) ∧ p' = b'.start + 1 ∧
      ∃ x, B'[b'.start]? = some x ∧ isLbl x = true)

theorem Pair.entry {B B' : List LinstrRM} {b b' : Block} {p p' : Nat} (h : Pair B B' b b' p p') :
    EntryAt B b p ∧ EntryAt B' b' p' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · exact ⟨Or.inl h1, Or.inl h2⟩
  · exact ⟨Or.inr ⟨h1, h2⟩, Or.inr ⟨h3, h4⟩⟩

/-- The simulation up to the measure `N` on the instruction set `I`: a halting source run
    from a block entry is matched by a halting run of the rewritten body. -/
def SimAt (I : Isa) (outs : List String) (L : Nat → List String × Bool)
    (B B' : List LinstrRM) (G G' : CFG) (fn : String) (N : Nat) : Prop :=
  ∀ (fuel k : Nat) (s s' t : LstateMF),
    fuel * (G.blocks.size + 1) + (G.blocks.size - k) < N → k < G.blocks.size →
    Pair B B' (G.blk k) (G'.blk k) s.prog.base.reg.lpc s'.prog.base.reg.lpc →
    Rel (L k) s s' → s.prog.lfn = fn →
    I.lsemFuelMemF (singletonProgM fn B) fuel s = some t →
    ∃ f' t', I.lsemFuelMemF (singletonProgM fn B') f' s' = some t' ∧ Obs outs t t'

/-- A state of the instruction set `I` at the end of the body is halted. -/
theorem halt_at_end_at (I : Isa) {fn : String} {B : List LinstrRM} {w : LstateMF}
    (hfn : w.prog.lfn = fn) (hw : w.prog.base.reg.lpc = B.length) (f : Nat) :
    I.lsemFuelMemF (singletonProgM fn B) f w = some w := by
  apply I.lsemFuelMemF_halt
  rw [findInstrMem_single hfn, hw]
  simp

theorem halt_at_end {fn : String} {B : List LinstrRM} {w : LstateMF} (hfn : w.prog.lfn = fn)
    (hw : w.prog.base.reg.lpc = B.length) (f : Nat) :
    lsemFuelMemF (singletonProgM fn B) f w = some w := by
  apply lsemFuelMemF_halt
  rw [findInstrMem_single hfn, hw]
  simp

/-- Control that falls out of block `k` continues in the next block, or leaves both
    bodies. -/
theorem fall_cont {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G' sym dec) {N k : Nat}
    (ih : SimAt I outs L B B' G G' fn N) (hk : k < G.blocks.size) {nx : Option Nat}
    (hn : G.next k = nx) (hn' : G'.next k = nx) {w w' t : LstateMF} {f0 : Nat}
    (hw : w.prog.base.reg.lpc = (G.blk k).stop) (hw' : w'.prog.base.reg.lpc = (G'.blk k).stop)
    (hfn : w.prog.lfn = fn) (hfn' : w'.prog.lfn = fn)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) f0 w = some t)
    (hmeas : f0 * (G.blocks.size + 1) + (G.blocks.size - (k + 1)) < N)
    (hrel : ∀ j, nx = some j → Rel (L j) w w') (hobs : nx = none → Obs outs w w') :
    ∃ f' t', I.lsemFuelMemF (singletonProgM fn B') f' w' = some t' ∧ Obs outs t t' := by
  have hk' : k < G'.blocks.size := hc.size ▸ hk
  cases nx with
  | none =>
      have e1 := (stop_next hc.hG hk).1 hn
      have e2 := (stop_next hc.hG' hk').1 hn'
      rw [halt_at_end_at I hfn (hw.trans e1)] at hrun
      cases hrun
      exact ⟨0, w', halt_at_end_at I hfn' (hw'.trans e2) 0, hobs rfl⟩
  | some j =>
      obtain ⟨hj, hjlt, e1⟩ := (stop_next hc.hG hk).2 j hn
      obtain ⟨-, -, e2⟩ := (stop_next hc.hG' hk').2 j hn'
      subst hj
      exact ih f0 (k + 1) w w' t hmeas hjlt (Or.inl ⟨hw.trans e1, hw'.trans e2⟩) (hrel _ rfl)
        hfn hrun

theorem label_at {B : List LinstrRM} {l : LLabel} {q : Nat}
    (h : findLabel l (B.map Prod.fst) = some q) : ∃ x, B[q]? = some x ∧ isLbl x = true := by
  obtain ⟨i, hi, hl⟩ := JasminLsemLabeled.findLabel_sound l _ q h
  obtain ⟨y, hy, rfl⟩ := getElem?_map_fst hi
  refine ⟨y, hy, ?_⟩
  obtain ⟨yi, yt⟩ := y
  cases yi <;> simp_all [isLbl, JasminLsemLabeled.isLabel]

/-- A jump to block `tg` continues there, one past its label. -/
theorem jump_cont {I : Isa} {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} {N tg : Nat} (ih : SimAt I outs L B B' G G' fn N)
    (htg : tg < G.blocks.size) {l l' : LLabel}
    (hl : findLabel l (B.map Prod.fst) = some (G.blk tg).start)
    (hl' : findLabel l' (B'.map Prod.fst) = some (G'.blk tg).start) {w w' t : LstateMF}
    {f1 : Nat} (hw : w.prog.base.reg.lpc = (G.blk tg).start + 1)
    (hw' : w'.prog.base.reg.lpc = (G'.blk tg).start + 1) (hfn : w.prog.lfn = fn)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) f1 w = some t)
    (hmeas : f1 * (G.blocks.size + 1) + (G.blocks.size - tg) < N) (hrel : Rel (L tg) w w') :
    ∃ f' t', I.lsemFuelMemF (singletonProgM fn B') f' w' = some t' ∧ Obs outs t t' :=
  ih f1 tg w w' t hmeas htg (Or.inr ⟨hw, label_at hl, hw', label_at hl'⟩) hrel hfn hrun

theorem measure_lt {nb fuel f k j N : Nat} (hN : fuel * (nb + 1) + (nb - k) < N + 1)
    (hf : f + 1 ≤ fuel) : f * (nb + 1) + (nb - j) < N := by
  have := Nat.mul_le_mul_right (nb + 1) hf
  rw [Nat.succ_mul] at this
  omega

theorem measure_le {nb fuel f k N : Nat} (hN : fuel * (nb + 1) + (nb - k) < N + 1)
    (hf : f ≤ fuel) (hk : k < nb) : f * (nb + 1) + (nb - (k + 1)) < N := by
  have := Nat.mul_le_mul_right (nb + 1) hf
  omega

theorem sim_step {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G' sym dec) {N : Nat}
    (ih : SimAt I outs L B B' G G' fn N) : SimAt I outs L B B' G G' fn (N + 1) := by
  intro fuel k s s' t hN hk hpair hrel hfn hrun
  obtain ⟨hTk, hok⟩ := hc.blk k hk
  have hk' : k < G'.blocks.size := hc.size ▸ hk
  have F := blockFacts hc.hG hk
  have F' := blockFacts hc.hG' hk'
  obtain ⟨hE, hE'⟩ := hpair.entry
  obtain ⟨hs1, hle⟩ := entry_le hc.hG hk hE
  obtain ⟨hs1', hle'⟩ := entry_le hc.hG' hk' hE'
  have hfn' : s'.prog.lfn = fn := hrel.1.trans hfn
  -- the source runs the block body
  have hplain := body_plain hc.hG hk hs1
  obtain ⟨u, f, hf, hu, hru⟩ :=
    fuel_runL_at hL.plain _ _ s t fuel hfn (drop_split B hle) hplain hrun
  obtain ⟨hul, hup⟩ := runL_frame_at hL.plain _ s u hplain hu
  have hbstop : bstopOf (G.blk k).term (G.blk k) ≤ B.length := by
    unfold bstopOf; split <;> have := F.le <;> simp at this <;> omega
  have hbstop' : bstopOf (G'.blk k).term (G'.blk k) ≤ B'.length := by
    unfold bstopOf; split <;> have := F'.le <;> simp at this <;> omega
  simp only [List.length_take, List.length_drop] at hup hf
  have hupc : u.prog.base.reg.lpc = bstopOf (G.blk k).term (G.blk k) := by
    rw [hup]; omega
  have hul' : u.prog.lfn = fn := hul.trans hfn
  -- the last instruction of the source block
  have hlt : (G.blk k).stop - 1 < B.length := by have := F.le; have := F.lt; simp at *; omega
  obtain ⟨z, hz⟩ : ∃ z, B[(G.blk k).stop - 1]? = some z :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have hterm := F.term
  rw [List.getElem?_map, hz, Option.map_some] at hterm
  have hlt' : (G'.blk k).stop - 1 < B'.length := by
    have := F'.le; have := F'.lt; simp at *; omega
  obtain ⟨z', hz'⟩ : ∃ z', B'[(G'.blk k).stop - 1]? = some z' :=
    ⟨_, List.getElem?_eq_getElem hlt'⟩
  have hterm' := F'.term
  rw [List.getElem?_map, hz', Option.map_some, hTk] at hterm'
  -- a block ending in `Lret` is never left by a halting run
  by_cases hret : (G.blk k).term = .ret
  · rcases termOk_spec hterm with ⟨_, hT, _⟩ | ⟨_, _, _, hT, _⟩ | ⟨_, _, _, _, hT, _⟩ | ⟨_, hzr⟩
    all_goals try (rw [hret] at hT; cases hT)
    have hupc2 : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by
      rw [hupc]; simp [bstopOf, hret]
    obtain ⟨_, _, _, he, _⟩ :=
      run_inv_at hru (by rw [findInstrMem_single hul', hupc2, hz])
    obtain ⟨zi, zt⟩ := z
    simp only at hzr
    subst hzr
    rw [hL.ret] at he
    cases he
  -- the symbolic runs of the two block bodies
  have hD := symRun_sound_at hL.step_sound (singletonProgM fn B)
    ((B.drop s.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) SSt.start _ _ _ _ _ s
    (holds_start s)
  rw [symRun_entry_at hL.label hE hle] at hD
  rcases blockOk_spec hok hret with hfail | ⟨ss, gs, ss', gs', hS, hS', hgs, hta, hex⟩
  · rw [hfail] at hD
    simp only [SOut.DescN] at hD
    rw [hD] at hu
    cases hu
  rw [hS] at hD
  obtain ⟨hAll, hH, hFr⟩ := hD.1 u hu
  have hV : ∀ r ∈ (L k).1, s'.prog.base.reg.lvm r = s.prog.base.reg.lvm r := hrel.2.2.2.1
  have hH0' : Holds s'.prog.base.reg.lvm s.prog.base.larr s'.prog.base.cf s'.prog.base.of s'.zf
      SSt.start s' :=
    ⟨fun _ => rfl, fun q => by rw [hrel.2.1]; rfl, rfl, by simp [SSt.start, STerm.ev],
      by simp [SSt.start, STerm.ev]⟩
  rw [hTk] at hle'
  have hD' := symRun_sound_at hL.step_sound (singletonProgM fn B')
    ((B'.drop s'.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)) SSt.start _ _ _ _ _ s' hH0'
  rw [symRun_entry_at hL.label hE' hle', hS'] at hD'
  have hAll' : AllG s'.prog.base.reg.lvm s.prog.base.larr s'.prog.base.cf s'.prog.base.of gs' :=
    allG_normG.mp fun g hg =>
      (SG.holds_congr _ g (fun r hr => (hV r ((hgs g hg).2.1 r hr)).symm)
        (fun e => by
          obtain ⟨-, hc, ho⟩ := hrel.2.2.2.2 ((hgs g hg).2.2 e)
          exact ⟨hc.symm, ho.symm⟩)).mp
      ((hgs g hg).1 _ _ _ _ hAll)
  obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp (hD'.2 hAll')
  obtain ⟨-, hH', hFr'⟩ := hD'.1 u' hu'
  have hplain' := body_plain hc.hG' hk' hs1'
  rw [hTk] at hplain' hbstop'
  have hrun' := runL_fuel_at hL.plain _ _ s' u' hfn' (drop_split B' hle') hplain' hu'
  simp only [List.length_take, List.length_drop] at hrun'
  have hupc' : u'.prog.base.reg.lpc = bstopOf (G.blk k).term (G'.blk k) := by
    rw [hFr'.2.1]; simp only [List.length_take, List.length_drop]; omega
  have hul'' : u'.prog.lfn = fn := hFr'.1.trans hfn'
  obtain ⟨hsucc, hhalt⟩ := exit_rel hH hH' hV (fun hz => hrel.2.2.2.2 hz)
    (symRun_good_at hL.good _ SSt.good_start hS) (symRun_good_at hL.good _ SSt.good_start hS')
    (by rw [hul'', hul']) (by rw [hFr'.2.2, hrel.2.2.1, hFr.2.2]) hAll
    (allG_normG.mp fun g hg => (hgs g hg).1 _ _ _ _ hAll) hex
  have hfle : f ≤ fuel := by omega
  obtain ⟨m', hm'⟩ : ∃ m', ∀ f0, I.lsemFuelMemF (singletonProgM fn B') (m' + f0) s' =
      I.lsemFuelMemF (singletonProgM fn B') f0 u' := ⟨_, hrun'⟩
  clear hrun'
  obtain ⟨zi, zt⟩ := z
  obtain ⟨zi', zt'⟩ := z'
  rw [hz, hz'] at hta
  simp only at hterm hterm'
  rcases termOk_spec hterm with ⟨nx, hT, _, hnx⟩ | ⟨tg, x, l, hT, hzi, htg, hl⟩ |
      ⟨tg, nx, c, l, hT, hzi, htg, hl, hnx⟩ | ⟨hT, _⟩
  · -- fall through
    obtain ⟨nx', hT', _, hnx'⟩ | ⟨_, _, _, hT', _⟩ | ⟨_, _, _, _, hT', _⟩ | ⟨hT', _⟩ :=
      termOk_spec hterm'
    all_goals rw [hT] at hT'
    all_goals try cases hT'
    have hw : u.prog.base.reg.lpc = (G.blk k).stop := by rw [hupc, hT]; rfl
    have hw' : u'.prog.base.reg.lpc = (G'.blk k).stop := by rw [hupc', hT]; rfl
    obtain ⟨f'', t', hr, hobs⟩ := fall_cont hc ih hk hnx.symm hnx'.symm hw hw' hul' hul'' hru
      (measure_le hN hfle hk) (fun j hj => hsucc j (by simp [hT, Term.succs, hj]))
      (fun hn => hhalt (by simp [hT, hn, Term.halts]))
    exact ⟨m' + f'', t', by rw [hm']; exact hr, hobs⟩
  · -- jump
    obtain ⟨_, hT', _⟩ | ⟨tg', x', l', hT', hzi', htg', hl'⟩ | ⟨_, _, _, _, hT', _⟩ |
        ⟨hT', _⟩ := termOk_spec hterm'
    all_goals rw [hT] at hT'
    all_goals try cases hT'
    subst hzi hzi'
    have hxx : x = x' := by simpa [termAgree, hT] using hta
    subst hxx
    have hw : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [hupc, hT]; rfl
    have hw' : u'.prog.base.reg.lpc = (G'.blk k).stop - 1 := by rw [hupc', hT]; rfl
    obtain ⟨f1, u1, hf1, he, hr1⟩ :=
      run_inv_at hru (by rw [findInstrMem_single hul', hw, hz])
    rw [I.step_goto] at he
    by_cases hx : x = (singletonProgM fn B).lfn
    · rw [ite_eq_left hx, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      have he' : I.step (singletonProgM fn B') (.Lgoto (x, l'), zt') u' =
          some { u' with prog := { u'.prog with
            base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } } := by
        rw [I.step_goto, ite_eq_left (by simpa [singletonProgM, hul'', hul'] using hx),
          evalJumpMem_single hl']
        rfl
      obtain ⟨f'', t', hr, hobs⟩ := jump_cont (w' := { u' with prog := { u'.prog with
          base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } }) ih htg hl hl' rfl rfl
        (by exact hul') hr1
        (measure_lt hN (show f1 + 1 ≤ fuel by omega)) (hsucc tg (by simp [hT, Term.succs]))
      refine ⟨m' + (f'' + 1), t', ?_, hobs⟩
      rw [hm', I.lsemFuelMemF_step _ _ _ _ _ (by rw [findInstrMem_single hul'', hw', hz']) he']
      exact hr
    · rw [ite_eq_right hx] at he
      cases he
  · -- branch
    obtain ⟨_, hT', _⟩ | ⟨_, _, _, hT', _⟩ | ⟨tg', nx', c', l', hT', hzi', htg', hl', hnx'⟩ |
        ⟨hT', _⟩ := termOk_spec hterm'
    all_goals rw [hT] at hT'
    all_goals try cases hT'
    subst hzi hzi'
    simp only [termAgree, hT, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
      Bool.not_eq_true'] at hta
    obtain ⟨⟨hdeq, hdv⟩, hdz⟩ := hta
    have hdec : I.condEval u' c' = I.condEval u c := by
      rw [hL.dec_sound hH' c', hL.dec_sound hH c, ← hdeq]
      exact SDec.ev_congr _ _ (fun r hr => hV r (vIn_spec hdv r hr))
        (fun hz => hrel.2.2.2.2 (by
          rcases hdz with h | h
          · rw [hz] at h; cases h
          · exact h))
    have hw : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [hupc, hT]; rfl
    have hw' : u'.prog.base.reg.lpc = (G'.blk k).stop - 1 := by rw [hupc', hT]; rfl
    obtain ⟨f1, u1, hf1, he, hr1⟩ :=
      run_inv_at hru (by rw [findInstrMem_single hul', hw, hz])
    rw [I.step_cond] at he
    have hstop : 0 < (G.blk k).stop := by have := F.lt; omega
    have hstop' : 0 < (G'.blk k).stop := by have := F'.lt; omega
    by_cases hd : I.condEval u c = true
    · rw [ite_eq_left hd, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      have he' : I.step (singletonProgM fn B') (.Lcond c' l', zt') u' =
          some { u' with prog := { u'.prog with
            base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } } := by
        rw [I.step_cond, ite_eq_left (hdec.trans hd), evalJumpMem_single hl']
        rfl
      obtain ⟨f'', t', hr, hobs⟩ := jump_cont (w' := { u' with prog := { u'.prog with
          base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } }) ih htg hl hl' rfl rfl
        (by exact hul') hr1
        (measure_lt hN (show f1 + 1 ≤ fuel by omega)) (hsucc tg (by simp [hT, Term.succs]))
      refine ⟨m' + (f'' + 1), t', ?_, hobs⟩
      rw [hm', I.lsemFuelMemF_step _ _ _ _ _ (by rw [findInstrMem_single hul'', hw', hz']) he']
      exact hr
    · rw [ite_eq_right hd] at he
      simp only [Option.some.injEq] at he
      have he' : I.step (singletonProgM fn B') (.Lcond c' l', zt') u' =
          some { u' with prog := { u'.prog with base := u'.prog.base.nextPc } } := by
        rw [I.step_cond, ite_eq_right (by rw [hdec]; exact hd)]
      obtain ⟨f'', t', hr, hobs⟩ := fall_cont (w := u1)
        (w' := { u' with prog := { u'.prog with base := u'.prog.base.nextPc } })
        hc ih hk hnx.symm hnx'.symm
        (by rw [← he]; show u.prog.base.reg.lpc + 1 = _; omega)
        (by show u'.prog.base.reg.lpc + 1 = _; omega)
        (by rw [← he]; exact hul') hul'' hr1 (measure_le hN (show f1 ≤ fuel by omega) hk)
        (fun j hj => by rw [← he]; exact hsucc j (by simp [hT, Term.succs, hj]))
        (fun hn => by rw [← he]; exact hhalt (by simp [hT, hn, Term.halts]))
      refine ⟨m' + (f'' + 1), t', ?_, hobs⟩
      rw [hm', I.lsemFuelMemF_step _ _ _ _ _ (by rw [findInstrMem_single hul'', hw', hz']) he']
      exact hr
  · exact absurd hT hret

theorem simAt_all {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hL : SymLaws I sym dec) {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G' sym dec) :
    ∀ N, SimAt I outs L B B' G G' fn N
  | 0 => fun _ _ _ _ _ hN => absurd hN (Nat.not_lt_zero _)
  | N + 1 => sim_step hL hc (simAt_all hL hc N)

/-- **Soundness of the checker for given live sets, over an instruction set.** If the
    symbolic step `sym` and branch condition `dec` satisfy the laws `SymLaws I sym dec` and
    `ownedCheckWith outs L B B' sym dec` accepts, every halting run of `I` on the singleton
    program over `B` from a state at pc `0` of that function is matched by a halting run on
    the singleton program over `B'` from the same state, and the two end states agree on the
    registers `outs`, on the arrays and on the word memory. -/
theorem ownedCheckWith_sound_at {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} (h : ownedCheckWith outs L B B' sym dec = true) (fn : String)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', I.lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' := by
  unfold ownedCheckWith at h
  split at h
  · rename_i G G' hG hG'
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq,
      List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨hne, hne'⟩, hsz⟩, hblk⟩ := h
    have hc : Checked outs L B B' G G' sym dec :=
      ⟨hG, hG', hsz.symm, fun k hk => ⟨(hblk k hk).1.symm, (hblk k hk).2⟩⟩
    have hwl : B.map Prod.fst ≠ [] := by simpa using hne
    have hwl' : B'.map Prod.fst ≠ [] := by simpa using hne'
    obtain ⟨h0, hs0⟩ := cfgOf_start_zero hG hwl
    obtain ⟨-, hs0'⟩ := cfgOf_start_zero hG' hwl'
    exact simAt_all hL hc _ fuel 0 s s t (Nat.lt_succ_self _) h0
      (Or.inl ⟨hpc.trans hs0.symm, hpc.trans hs0'.symm⟩)
      ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩ hfn hrun
  · cases h

/-- **Soundness of the checker for given live sets.** If `ownedCheckWith outs L B B'`
    accepts, every halting `lsemFuelMemF` run of the singleton program over `B` from a
    state at pc `0` of that function is matched by a halting run of the singleton program
    over `B'` from the same state, and the two end states agree on the registers `outs`,
    on the arrays and on the word memory. -/
theorem ownedCheckWith_sound {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} (h : ownedCheckWith outs L B B' = true) (fn : String)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' := by
  rw [← x86Isa_lsemFuelMemF] at hrun
  simpa only [x86Isa_lsemFuelMemF] using
    ownedCheckWith_sound_at symLaws_x86 h fn s t hfn hpc fuel hrun

/-! ## 13. Substitution

A substitution `σ : Nat → STerm` replaces each table entry `STerm.ref k` by `σ k`. The
symbolic step never inspects a word, so it commutes with every substitution
(`symStep_subst`, `symRun_subst`). -/

mutual
/-- The symbolic word `t` with each table entry `ref k` replaced by `σ k`. -/
def STerm.subst (σ : Nat → STerm) : STerm → STerm
  | .reg r => .reg r
  | .immW w n => .immW w n
  | .immAt n x => .immAt n (x.subst σ)
  | .bin m x y => .bin m (x.subst σ) (y.subst σ)
  | .un m x => .un m (x.subst σ)
  | .shImm m k x => .shImm m k (x.subst σ)
  | .aget a w n i => .aget (a.subst σ) w n (i.subst σ)
  | .cin ofl => .cin ofl
  | .aluF op ofl x y o => .aluF op ofl (x.subst σ) (y.subst σ) (o.subst σ)
  | .carryW op x y c => .carryW op (x.subst σ) (y.subst σ) (c.subst σ)
  | .carryF op ofl x y c => .carryF op ofl (x.subst σ) (y.subst σ) (c.subst σ)
  | .mulx hi x y => .mulx hi (x.subst σ) (y.subst σ)
  | .cout sub x y c => .cout sub (x.subst σ) (y.subst σ) (c.subst σ)
  | .sel x y c => .sel (x.subst σ) (y.subst σ) (c.subst σ)
  | .setcc cc x y => .setcc cc (x.subst σ) (y.subst σ)
  | .ref k => σ k

/-- The symbolic array `a` with each table entry `ref k` replaced by `σ k`. -/
def SArr.subst (σ : Nat → STerm) : SArr → SArr
  | .cell r => .cell r
  | .aset a w n i v => .aset (a.subst σ) w n (i.subst σ) (v.subst σ)
  | .zero w n => .zero w n
end

/-- The symbolic flag `f` under the substitution `σ`. -/
def SFlag.subst (σ : Nat → STerm) : SFlag → SFlag
  | .init => .init
  | .cmp x y => .cmp (x.subst σ) (y.subst σ)

/-- The guard `g` under the substitution `σ`. -/
def SG.subst (σ : Nat → STerm) : SG → SG
  | .wid t w => .wid (t.subst σ) w
  | .eqW x y => .eqW (x.subst σ) (y.subst σ)
  | .shp a w n => .shp (a.subst σ) w n

/-- The symbolic branch condition `d` under the substitution `σ`. -/
def SDec.subst (σ : Nat → STerm) : SDec → SDec
  | .flag pol z => .flag pol (z.subst σ)
  | .nz t => .nz (t.subst σ)
  | .const b => .const b

theorem RegMap.rd_map (σ : Nat → STerm) (m : RegMap) (r : String) :
    RegMap.rd (m.map (fun _ t => t.subst σ)) r = (RegMap.rd m r).subst σ := by
  simp only [RegMap.rd, Std.TreeMap.getD_eq_getD_getElem?, Std.TreeMap.getElem?_map]
  cases m[r]? <;> rfl

/-- The register file `f` under the substitution `σ`. -/
def RegFile.subst (σ : Nat → STerm) (f : RegFile) : RegFile :=
  Quotient.liftOn f (fun m => Quotient.mk _ (m.map (fun _ t => t.subst σ))) (fun _ _ h =>
    Quotient.sound fun r => by simp only [RegMap.rd_map, h r])

theorem RegFile.get_subst (σ : Nat → STerm) (f : RegFile) (r : String) :
    (f.subst σ).get r = (f.get r).subst σ :=
  Quotient.inductionOn f fun m => RegMap.rd_map σ m r

/-- The symbolic state `ss` under the substitution `σ`. -/
def SSt.subst (σ : Nat → STerm) (ss : SSt) : SSt :=
  { rf := ss.rf.subst σ, arrs := fun r => (ss.arrs r).subst σ, zf := ss.zf.subst σ,
    wr := ss.wr, awr := ss.awr, cf := ss.cf.subst σ, of := ss.of.subst σ, nwr := ss.nwr,
    nwr_eq := ss.nwr_eq }

@[simp] theorem SSt.subst_regs_apply (σ : Nat → STerm) (ss : SSt) (r : String) :
    (ss.subst σ).regs r = (ss.regs r).subst σ :=
  RegFile.get_subst σ ss.rf r

theorem SSt.subst_regs (σ : Nat → STerm) (ss : SSt) :
    (ss.subst σ).regs = fun r => (ss.regs r).subst σ :=
  funext (SSt.subst_regs_apply σ ss)

/-- A register-file description under the substitution `σ`. -/
def ROut.subst (σ : Nat → STerm) : ROut → ROut
  | .set d t gs => .set d (t.subst σ) (gs.map (SG.subst σ))
  | .nop => .nop
  | .fail => .fail
  | .unk => .unk

/-- A step description under the substitution `σ`. -/
def SOut.subst (σ : Nat → STerm) : SOut → SOut
  | .ok ss gs => .ok (ss.subst σ) (gs.map (SG.subst σ))
  | .fail => .fail
  | .unk => .unk

theorem SSt.subst_start (σ : Nat → STerm) : SSt.start.subst σ = SSt.start := rfl

theorem SSt.subst_setR (σ : Nat → STerm) (ss : SSt) (d : String) (t : STerm) :
    (ss.setR d t).subst σ = (ss.subst σ).setR d (t.subst σ) := by
  refine SSt.ext (fun r => ?_) rfl rfl rfl rfl rfl rfl
  rw [SSt.subst_regs_apply, SSt.setR_regs, SSt.setR_regs, SSt.subst_regs_apply]
  split <;> rfl

theorem SSt.subst_setA (σ : Nat → STerm) (ss : SSt) (d : String) (a : SArr) :
    (ss.setA d a).subst σ = (ss.subst σ).setA d (a.subst σ) := by
  simp only [SSt.subst, SSt.setA, SSt.mk.injEq, and_true, true_and]
  funext r
  split <;> rfl

theorem SSt.subst_with (σ : Nat → STerm) (ss : SSt) (c o : STerm) :
    ({ ss with cf := c, of := o } : SSt).subst σ =
      { ss.subst σ with cf := c.subst σ, of := o.subst σ } := rfl

theorem symOp64_subst (σ : Nat → STerm) (R : String → STerm) (o : LOperand) :
    symOp64 (fun r => (R r).subst σ) o =
      (symOp64 R o).map (fun p => (p.1.subst σ, p.2.map (SG.subst σ))) := by
  cases o <;> rfl

theorem symN_subst (σ : Nat → STerm) (x : LinstrR) (R : String → STerm) :
    symN x (fun r => (R r).subst σ) = (symN x R).subst σ := by
  unfold symN
  split <;> (try split) <;> (try split_ifs) <;> (try split) <;> (try split_ifs) <;> rfl

theorem symSh_subst (σ : Nat → STerm) (x : LinstrR) (R : String → STerm) :
    symSh x (fun r => (R r).subst σ) = (symSh x R).subst σ := by
  unfold symSh
  split
  · rfl
  · exact symN_subst σ x R

theorem symMC_subst (σ : Nat → STerm) (x : LinstrR) (R : String → STerm) :
    symMC x (fun r => (R r).subst σ) = (symMC x R).subst σ := by
  unfold symMC
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · exact symSh_subst σ x R

theorem symCast_subst (σ : Nat → STerm) (i : LinstrRT) (R : String → STerm) :
    symCast i (fun r => (R r).subst σ) = (symCast i R).subst σ := by
  unfold symCast
  split
  · split
    · rfl
    · exact symMC_subst σ i.1 R
  · split
    · exact symMC_subst σ i.1 R
    · rfl

theorem liftR_subst (σ : Nat → STerm) (ss : SSt) (o : ROut) :
    liftR (ss.subst σ) (o.subst σ) = (liftR ss o).subst σ := by
  cases o with
  | set d t gs => simp only [ROut.subst, liftR, SOut.subst, SSt.subst_setR]
  | nop => rfl
  | fail => rfl
  | unk => rfl

theorem symMem_subst (σ : Nat → STerm) (i : LinstrRM) (ss : SSt) :
    symMem i (ss.subst σ) = (symMem i ss).subst σ := by
  unfold symMem
  split
  · split
    · simp only [SOut.subst, SSt.subst_setR, List.map_cons, List.map_nil,
        SG.subst, STerm.subst, SSt.subst_regs_apply]
      rfl
    · rw [← liftR_subst, ← symCast_subst, SSt.subst_regs σ ss]
  · split
    · simp only [SOut.subst, SSt.subst_setA, List.map_cons, List.map_nil,
        SG.subst, SArr.subst, SSt.subst_regs_apply]
      rfl
    · rw [← liftR_subst, ← symCast_subst, SSt.subst_regs σ ss]
  · rfl
  · rfl
  · split
    · split
      · simp only [SOut.subst, SSt.subst_setA, List.map_nil, SArr.subst]
      · rfl
    · rfl
  · split
    · split
      · simp only [SOut.subst, SSt.subst_setA, List.map_cons, List.map_nil,
          SG.subst, SArr.subst, STerm.subst, SSt.subst_regs_apply]
        rfl
      · rfl
    · rfl
  · rw [← liftR_subst, ← symCast_subst, SSt.subst_regs σ ss]

theorem aluFlT_subst (σ : Nat → STerm) (i : LinstrRM) (ss : SSt) (ofl : Bool) :
    aluFlT i (ss.subst σ) ofl = (aluFlT i ss ofl).subst σ := by
  unfold aluFlT
  split
  · rw [SSt.subst_regs σ ss, symOp64_subst,
      symOp64_subst]
    cases symOp64 ss.regs _ <;> cases symOp64 ss.regs _ <;> cases ofl <;> dsimp only <;>
      (try split_ifs) <;> rfl
  · cases ofl <;> rfl

theorem aluFl_subst (σ : Nat → STerm) (i : LinstrRM) (ss : SSt) (o : SOut) :
    aluFl i (ss.subst σ) (o.subst σ) = (aluFl i ss o).subst σ := by
  cases o with
  | ok ss' gs => simp only [SOut.subst, aluFl, aluFlT_subst]; rfl
  | fail => rfl
  | unk => rfl

theorem symCarry_subst (σ : Nat → STerm) (op : CarryOp) (d : String) (a b : LOperand)
    (ss : SSt) : symCarry op d a b (ss.subst σ) = (symCarry op d a b ss).subst σ := by
  unfold symCarry
  rw [SSt.subst_regs σ ss, symOp64_subst,
    symOp64_subst]
  cases symOp64 ss.regs a with
  | none => rfl
  | some p =>
      cases symOp64 ss.regs b with
      | none => rfl
      | some q =>
          cases op <;>
            simp only [Option.map_some, SOut.subst, List.map_append, SSt.subst_with,
              SSt.subst_setR, STerm.subst] <;>
            rfl

theorem symWide_subst (σ : Nat → STerm) (w : WideOp) (ss : SSt) :
    symWide w (ss.subst σ) = (symWide w ss).subst σ := by
  unfold symWide
  rw [SSt.subst_regs σ ss]
  cases w with
  | mov d b =>
      simp only [symOp64_subst]
      cases symOp64 ss.regs b <;> simp [SOut.subst, SSt.subst_setR]
  | mulx lo hi b =>
      simp only [symOp64_subst]
      cases symOp64 ss.regs (.reg mulxSrc) <;> cases symOp64 ss.regs b <;>
        simp [SOut.subst, SSt.subst_setR, STerm.subst, mulLoT]

/-- **The symbolic step commutes with substitution.** -/
theorem symStep_subst (σ : Nat → STerm) (i : LinstrRM) (ss : SSt) :
    symStep i (ss.subst σ) = (symStep i ss).subst σ := by
  unfold symStep
  split
  · rw [SSt.subst_regs σ ss, symOp64_subst,
      symOp64_subst]
    cases symOp64 ss.regs _ <;> cases symOp64 ss.regs _ <;> simp [SOut.subst, List.map_append]
    rfl
  · split
    · simp only [SOut.subst, SSt.subst_setR, List.map_nil, SSt.subst_regs_apply]
    · split
      · rfl
      · split
        · rfl
        · rfl
        · rfl
        · split
          · exact symCarry_subst σ _ _ _ _ ss
          · split
            · exact symWide_subst σ _ ss
            · rw [symMem_subst, aluFl_subst]

/-- **The symbolic run commutes with substitution**, for every symbolic step that does. -/
theorem symRun_subst_at {sym : LinstrRM → SSt → SOut}
    (hsub : ∀ (σ : Nat → STerm) (i : LinstrRM) (ss : SSt),
      sym i (ss.subst σ) = (sym i ss).subst σ) (σ : Nat → STerm) :
    ∀ (is : List LinstrRM) (ss : SSt),
      symRun is (ss.subst σ) sym = (symRun is ss sym).subst σ
  | [], _ => rfl
  | i :: is, ss => by
      simp only [symRun, hsub]
      cases sym i ss with
      | ok ss1 g1 =>
          simp only [SOut.subst, symRun_subst_at hsub σ is ss1]
          cases symRun is ss1 sym <;> simp
      | fail => rfl
      | unk => rfl

/-- **The symbolic run commutes with substitution.** -/
theorem symRun_subst (σ : Nat → STerm) (is : List LinstrRM) (ss : SSt) :
    symRun is (ss.subst σ) = (symRun is ss).subst σ :=
  symRun_subst_at symStep_subst σ is ss

/-! ## 14. The term table

A symbolic word of a long block shares its subterms, and a structural walk over it (an
equality test, `STerm.vars`) takes time exponential in the length of the block. A term
table (`TEnt`, `Tbl`) stores each distinct node once, with its children as entries
`STerm.ref k`; equal words get equal entries, so they are compared by index. Each entry
caches the registers its word reads, whether it reads a start flag, and its width base
(`STerm.wbase`) with the width the base fixes. A substitution `σ` agrees with a table
(`TblOK`) when `σ k` is the word of entry `k` with `σ` substituted, and the cached data
describe `σ k`. Every table built by `Tbl.intern` from the empty table has such a
substitution (`Tbl.Valid`). -/

mutual
/-- The word `t` reads only table entries below `n`. -/
def STerm.refsLt (n : Nat) : STerm → Bool
  | .reg _ => true
  | .immW _ _ => true
  | .immAt _ x => x.refsLt n
  | .bin _ x y => x.refsLt n && y.refsLt n
  | .un _ x => x.refsLt n
  | .shImm _ _ x => x.refsLt n
  | .aget a _ _ i => a.refsLt n && i.refsLt n
  | .cin _ => true
  | .aluF _ _ x y o => x.refsLt n && y.refsLt n && o.refsLt n
  | .carryW _ x y c => x.refsLt n && y.refsLt n && c.refsLt n
  | .carryF _ _ x y c => x.refsLt n && y.refsLt n && c.refsLt n
  | .mulx _ x y => x.refsLt n && y.refsLt n
  | .cout _ x y c => x.refsLt n && y.refsLt n && c.refsLt n
  | .sel x y c => x.refsLt n && y.refsLt n && c.refsLt n
  | .setcc _ x y => x.refsLt n && y.refsLt n
  | .ref k => decide (k < n)

/-- The array `a` reads only table entries below `n`. -/
def SArr.refsLt (n : Nat) : SArr → Bool
  | .cell _ => true
  | .aset a _ _ i v => a.refsLt n && i.refsLt n && v.refsLt n
  | .zero _ _ => true
end

mutual
theorem STerm.refsLt_mono {n m : Nat} (hnm : n ≤ m) :
    ∀ t : STerm, t.refsLt n = true → t.refsLt m = true
  | .reg _, _ => rfl
  | .immW _ _, _ => rfl
  | .immAt _ x, h => STerm.refsLt_mono hnm x h
  | .bin _ x y, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h ⊢
      exact ⟨STerm.refsLt_mono hnm x h.1, STerm.refsLt_mono hnm y h.2⟩
  | .un _ x, h => STerm.refsLt_mono hnm x h
  | .shImm _ _ x, h => STerm.refsLt_mono hnm x h
  | .aget a _ _ i, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h ⊢
      exact ⟨SArr.refsLt_mono hnm a h.1, STerm.refsLt_mono hnm i h.2⟩
  | .cin _, _ => rfl
  | .aluF _ _ x y o, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨STerm.refsLt_mono hnm x h.1.1, STerm.refsLt_mono hnm y h.1.2⟩,
        STerm.refsLt_mono hnm o h.2⟩
  | .carryW _ x y c, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨STerm.refsLt_mono hnm x h.1.1, STerm.refsLt_mono hnm y h.1.2⟩,
        STerm.refsLt_mono hnm c h.2⟩
  | .carryF _ _ x y c, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨STerm.refsLt_mono hnm x h.1.1, STerm.refsLt_mono hnm y h.1.2⟩,
        STerm.refsLt_mono hnm c h.2⟩
  | .mulx _ x y, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h ⊢
      exact ⟨STerm.refsLt_mono hnm x h.1, STerm.refsLt_mono hnm y h.2⟩
  | .cout _ x y c, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨STerm.refsLt_mono hnm x h.1.1, STerm.refsLt_mono hnm y h.1.2⟩,
        STerm.refsLt_mono hnm c h.2⟩
  | .sel x y c, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨STerm.refsLt_mono hnm x h.1.1, STerm.refsLt_mono hnm y h.1.2⟩,
        STerm.refsLt_mono hnm c h.2⟩
  | .setcc _ x y, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h ⊢
      exact ⟨STerm.refsLt_mono hnm x h.1, STerm.refsLt_mono hnm y h.2⟩
  | .ref _, h => by
      simp only [STerm.refsLt, decide_eq_true_eq] at h ⊢
      omega

theorem SArr.refsLt_mono {n m : Nat} (hnm : n ≤ m) :
    ∀ a : SArr, a.refsLt n = true → a.refsLt m = true
  | .cell _, _ => rfl
  | .aset a _ _ i v, h => by
      simp only [SArr.refsLt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨SArr.refsLt_mono hnm a h.1.1, STerm.refsLt_mono hnm i h.1.2⟩,
        STerm.refsLt_mono hnm v h.2⟩
  | .zero _ _, _ => rfl
end

mutual
/-- Two substitutions that agree below `n` agree on a word that reads only entries below
    `n`. -/
theorem STerm.subst_congr {n : Nat} {σ σ' : Nat → STerm} (hσ : ∀ k, k < n → σ k = σ' k) :
    ∀ t : STerm, t.refsLt n = true → t.subst σ = t.subst σ'
  | .reg _, _ => rfl
  | .immW _ _, _ => rfl
  | .immAt _ x, h => by rw [STerm.subst, STerm.subst, STerm.subst_congr hσ x h]
  | .bin _ x y, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      rw [STerm.subst, STerm.subst, STerm.subst_congr hσ x h.1, STerm.subst_congr hσ y h.2]
  | .un _ x, h => by rw [STerm.subst, STerm.subst, STerm.subst_congr hσ x h]
  | .shImm _ _ x, h => by rw [STerm.subst, STerm.subst, STerm.subst_congr hσ x h]
  | .aget a _ _ i, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      rw [STerm.subst, STerm.subst, SArr.subst_congr hσ a h.1, STerm.subst_congr hσ i h.2]
  | .cin _, _ => rfl
  | .aluF _ _ x y o, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      rw [STerm.subst, STerm.subst, STerm.subst_congr hσ x h.1.1, STerm.subst_congr hσ y h.1.2,
        STerm.subst_congr hσ o h.2]
  | .carryW _ x y c, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      rw [STerm.subst, STerm.subst, STerm.subst_congr hσ x h.1.1, STerm.subst_congr hσ y h.1.2,
        STerm.subst_congr hσ c h.2]
  | .carryF _ _ x y c, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      rw [STerm.subst, STerm.subst, STerm.subst_congr hσ x h.1.1, STerm.subst_congr hσ y h.1.2,
        STerm.subst_congr hσ c h.2]
  | .mulx _ x y, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      rw [STerm.subst, STerm.subst, STerm.subst_congr hσ x h.1, STerm.subst_congr hσ y h.2]
  | .cout _ x y c, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      rw [STerm.subst, STerm.subst, STerm.subst_congr hσ x h.1.1, STerm.subst_congr hσ y h.1.2,
        STerm.subst_congr hσ c h.2]
  | .sel x y c, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      rw [STerm.subst, STerm.subst, STerm.subst_congr hσ x h.1.1, STerm.subst_congr hσ y h.1.2,
        STerm.subst_congr hσ c h.2]
  | .setcc _ x y, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      rw [STerm.subst, STerm.subst, STerm.subst_congr hσ x h.1, STerm.subst_congr hσ y h.2]
  | .ref k, h => by
      simp only [STerm.refsLt, decide_eq_true_eq] at h
      exact hσ k h

theorem SArr.subst_congr {n : Nat} {σ σ' : Nat → STerm} (hσ : ∀ k, k < n → σ k = σ' k) :
    ∀ a : SArr, a.refsLt n = true → a.subst σ = a.subst σ'
  | .cell _, _ => rfl
  | .aset a _ _ i v, h => by
      simp only [SArr.refsLt, Bool.and_eq_true] at h
      rw [SArr.subst, SArr.subst, SArr.subst_congr hσ a h.1.1, STerm.subst_congr hσ i h.1.2,
        STerm.subst_congr hσ v h.2]
  | .zero _ _, _ => rfl
end

/-- An entry of a term table: a node whose children are entries or leaves, the start
    registers its word reads, whether its word reads a start flag, its width base and the
    width the base fixes. -/
structure TEnt where
  /-- The node. -/
  node : STerm
  /-- The start registers the word reads. -/
  vars : List String
  /-- The word reads the carry or the overflow flag at the start. -/
  rf : Bool
  /-- The width base (`STerm.wbase`) of the word. -/
  wb : STerm
  /-- The width the width base fixes (`STerm.wknown`). -/
  wbk : Option Nat

mutual
/-- The start registers the word `t` over the table `E` reads. -/
def STerm.varsT (E : Array TEnt) : STerm → List String
  | .reg r => [r]
  | .immW _ _ => []
  | .immAt _ x => x.varsT E
  | .bin _ x y => x.varsT E ++ y.varsT E
  | .un _ x => x.varsT E
  | .shImm _ _ x => x.varsT E
  | .aget a _ _ i => a.varsT E ++ i.varsT E
  | .cin _ => []
  | .aluF _ _ x y o => x.varsT E ++ y.varsT E ++ o.varsT E
  | .carryW _ x y c => x.varsT E ++ y.varsT E ++ c.varsT E
  | .carryF _ _ x y c => x.varsT E ++ y.varsT E ++ c.varsT E
  | .mulx _ x y => x.varsT E ++ y.varsT E
  | .cout _ x y c => x.varsT E ++ y.varsT E ++ c.varsT E
  | .sel x y c => x.varsT E ++ y.varsT E ++ c.varsT E
  | .setcc _ x y => x.varsT E ++ y.varsT E
  | .ref k => (E[k]?.map TEnt.vars).getD []

/-- The start registers the array `a` over the table `E` reads. -/
def SArr.varsT (E : Array TEnt) : SArr → List String
  | .cell _ => []
  | .aset a _ _ i v => a.varsT E ++ i.varsT E ++ v.varsT E
  | .zero _ _ => []
end

mutual
/-- The word `t` over the table `E` reads the carry or the overflow flag at the start. -/
def STerm.readsFT (E : Array TEnt) : STerm → Bool
  | .reg _ => false
  | .immW _ _ => false
  | .immAt _ x => x.readsFT E
  | .bin _ x y => x.readsFT E || y.readsFT E
  | .un _ x => x.readsFT E
  | .shImm _ _ x => x.readsFT E
  | .aget a _ _ i => a.readsFT E || i.readsFT E
  | .cin _ => true
  | .aluF _ _ x y o => x.readsFT E || y.readsFT E || o.readsFT E
  | .carryW _ x y c => x.readsFT E || y.readsFT E || c.readsFT E
  | .carryF _ _ x y c => x.readsFT E || y.readsFT E || c.readsFT E
  | .mulx _ x y => x.readsFT E || y.readsFT E
  | .cout _ x y c => x.readsFT E || y.readsFT E || c.readsFT E
  | .sel x y c => x.readsFT E || y.readsFT E || c.readsFT E
  | .setcc _ x y => x.readsFT E || y.readsFT E
  | .ref k => (E[k]?.map TEnt.rf).getD true

/-- The array `a` over the table `E` reads the carry or the overflow flag at the start. -/
def SArr.readsFT (E : Array TEnt) : SArr → Bool
  | .cell _ => false
  | .aset a _ _ i v => a.readsFT E || i.readsFT E || v.readsFT E
  | .zero _ _ => false
end

/-- The width base of the word `t` over the table `E`. -/
def STerm.wbT (E : Array TEnt) : STerm → STerm
  | .immAt _ x => x.wbT E
  | .bin _ x _ => x.wbT E
  | .un _ x => x.wbT E
  | .shImm _ _ x => x.wbT E
  | .sel x _ _ => x.wbT E
  | .ref k => (E[k]?.map TEnt.wb).getD (.ref k)
  | .reg r => .reg r
  | .immW w n => .immW w n
  | .aget a w n i => .aget a w n i
  | .cin ofl => .cin ofl
  | .aluF op ofl x y o => .aluF op ofl x y o
  | .carryW op x y c => .carryW op x y c
  | .carryF op ofl x y c => .carryF op ofl x y c
  | .mulx hi x y => .mulx hi x y
  | .cout sub x y c => .cout sub x y c
  | .setcc cc x y => .setcc cc x y

/-- The width the width base of the word `t` over the table `E` fixes. -/
def STerm.wbkT (E : Array TEnt) : STerm → Option Nat
  | .immAt _ x => x.wbkT E
  | .bin _ x _ => x.wbkT E
  | .un _ x => x.wbkT E
  | .shImm _ _ x => x.wbkT E
  | .sel x _ _ => x.wbkT E
  | .ref k => (E[k]?.map TEnt.wbk).getD none
  | .reg _ => none
  | .immW w _ => some w
  | .aget _ w _ _ => some w
  | .cin _ => some 1
  | .aluF .. => none
  | .carryW .. => some 64
  | .carryF .. => some 1
  | .mulx .. => some 64
  | .cout .. => some 1
  | .setcc .. => some 1

/-- Entry `e` at index `k` describes `σ k`: `σ k` is its node with `σ` substituted, and its
    cached registers, flag reading, width base and width hold of `σ k`. -/
def EntOK (σ : Nat → STerm) (k : Nat) (e : TEnt) : Prop :=
  σ k = e.node.subst σ ∧ (∀ v ∈ (σ k).vars, v ∈ e.vars) ∧
    ((σ k).readsF = true → e.rf = true) ∧ (σ k).wbase = e.wb.subst σ ∧
    (σ k).wbase.wknown = e.wbk

/-- The substitution `σ` agrees with every entry of the table `E`. -/
def TblOK (σ : Nat → STerm) (E : Array TEnt) : Prop :=
  ∀ k (h : k < E.size), EntOK σ k E[k]

/-- The table `E'` extends the table `E`. -/
def TExt (E E' : Array TEnt) : Prop :=
  ∀ k (h : k < E.size), E'[k]? = some E[k]

theorem TExt.refl (E : Array TEnt) : TExt E E := fun k h => by simp [h]

theorem TExt.trans {E E' E'' : Array TEnt} (h1 : TExt E E') (h2 : TExt E' E'') :
    TExt E E'' := fun k h => by
  have e1 := h1 k h
  have hk' : k < E'.size := by
    rcases Nat.lt_or_ge k E'.size with hk | hk
    · exact hk
    · rw [Array.getElem?_eq_none hk] at e1; cases e1
  rw [h2 k hk', ← e1, Array.getElem?_eq_getElem hk']

theorem TExt.push (E : Array TEnt) (e : TEnt) : TExt E (E.push e) := fun k h => by
  simp [Array.getElem?_push, h, Nat.ne_of_lt h]

theorem TblOK.mono {σ : Nat → STerm} {E E' : Array TEnt} (h : TblOK σ E') (hx : TExt E E') :
    TblOK σ E := fun k hk => by
  have e1 := hx k hk
  have hk' : k < E'.size := by
    rcases Nat.lt_or_ge k E'.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at e1; cases e1
  have := h k hk'
  rw [Array.getElem?_eq_getElem hk', Option.some.injEq] at e1
  rwa [e1] at this

theorem TblOK.entry {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E) {k : Nat} {e : TEnt}
    (he : E[k]? = some e) : EntOK σ k e := by
  have hk : k < E.size := by
    rcases Nat.lt_or_ge k E.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at he; cases he
  rw [Array.getElem?_eq_getElem hk, Option.some.injEq] at he
  rw [← he]
  exact h k hk

section TblOK

variable {σ : Nat → STerm} {E : Array TEnt}

theorem TblOK.get {k : Nat} (h : TblOK σ E) (hk : k < E.size) : ∃ e, E[k]? = some e ∧ EntOK σ k e :=
  ⟨E[k], Array.getElem?_eq_getElem hk, h k hk⟩

mutual
theorem STerm.varsT_spec (h : TblOK σ E) :
    ∀ t : STerm, t.refsLt E.size = true → ∀ v ∈ (t.subst σ).vars, v ∈ t.varsT E
  | .reg _, _, v, hv => by simpa [STerm.subst, STerm.vars, STerm.varsT] using hv
  | .immW _ _, _, v, hv => by simp [STerm.subst, STerm.vars] at hv
  | .immAt _ x, hb, v, hv => STerm.varsT_spec h x hb v (by simpa [STerm.subst, STerm.vars] using hv)
  | .bin _ x y, hb, v, hv => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (STerm.varsT_spec h x hb.1 v) (STerm.varsT_spec h y hb.2 v)
  | .un _ x, hb, v, hv => STerm.varsT_spec h x hb v (by simpa [STerm.subst, STerm.vars] using hv)
  | .shImm _ _ x, hb, v, hv =>
      STerm.varsT_spec h x hb v (by simpa [STerm.subst, STerm.vars] using hv)
  | .aget a _ _ i, hb, v, hv => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (SArr.varsT_spec h a hb.1 v) (STerm.varsT_spec h i hb.2 v)
  | .cin _, _, v, hv => by simp [STerm.subst, STerm.vars] at hv
  | .aluF _ _ x y o, hb, v, hv => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (Or.imp (STerm.varsT_spec h x hb.1.1 v) (STerm.varsT_spec h y hb.1.2 v))
        (STerm.varsT_spec h o hb.2 v)
  | .carryW _ x y c, hb, v, hv => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (Or.imp (STerm.varsT_spec h x hb.1.1 v) (STerm.varsT_spec h y hb.1.2 v))
        (STerm.varsT_spec h c hb.2 v)
  | .carryF _ _ x y c, hb, v, hv => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (Or.imp (STerm.varsT_spec h x hb.1.1 v) (STerm.varsT_spec h y hb.1.2 v))
        (STerm.varsT_spec h c hb.2 v)
  | .mulx _ x y, hb, v, hv => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (STerm.varsT_spec h x hb.1 v) (STerm.varsT_spec h y hb.2 v)
  | .cout _ x y c, hb, v, hv => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (Or.imp (STerm.varsT_spec h x hb.1.1 v) (STerm.varsT_spec h y hb.1.2 v))
        (STerm.varsT_spec h c hb.2 v)
  | .sel x y c, hb, v, hv => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (Or.imp (STerm.varsT_spec h x hb.1.1 v) (STerm.varsT_spec h y hb.1.2 v))
        (STerm.varsT_spec h c hb.2 v)
  | .setcc _ x y, hb, v, hv => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (STerm.varsT_spec h x hb.1 v) (STerm.varsT_spec h y hb.2 v)
  | .ref k, hb, v, hv => by
      simp only [STerm.refsLt, decide_eq_true_eq] at hb
      obtain ⟨e, he, ok⟩ := h.get hb
      simp only [STerm.varsT, he, Option.map_some, Option.getD_some]
      exact ok.2.1 v hv

theorem SArr.varsT_spec (h : TblOK σ E) :
    ∀ a : SArr, a.refsLt E.size = true → ∀ v ∈ (a.subst σ).vars, v ∈ a.varsT E
  | .cell _, _, v, hv => by simp [SArr.subst, SArr.vars] at hv
  | .aset a _ _ i w, hb, v, hv => by
      simp only [SArr.refsLt, Bool.and_eq_true] at hb
      simp only [SArr.subst, SArr.vars, List.mem_append] at hv
      simp only [SArr.varsT, List.mem_append]
      exact hv.imp (Or.imp (SArr.varsT_spec h a hb.1.1 v) (STerm.varsT_spec h i hb.1.2 v))
        (STerm.varsT_spec h w hb.2 v)
  | .zero _ _, _, v, hv => by simp [SArr.subst, SArr.vars] at hv
end

mutual
theorem STerm.readsFT_spec (h : TblOK σ E) :
    ∀ t : STerm, t.refsLt E.size = true → (t.subst σ).readsF = true → t.readsFT E = true
  | .reg _, _, hf => by simp [STerm.subst, STerm.readsF] at hf
  | .immW _ _, _, hf => by simp [STerm.subst, STerm.readsF] at hf
  | .immAt _ x, hb, hf => STerm.readsFT_spec h x hb (by simpa [STerm.subst, STerm.readsF] using hf)
  | .bin _ x y, hb, hf => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.readsF, Bool.or_eq_true] at hf
      simp only [STerm.readsFT, Bool.or_eq_true]
      exact hf.imp (STerm.readsFT_spec h x hb.1) (STerm.readsFT_spec h y hb.2)
  | .un _ x, hb, hf => STerm.readsFT_spec h x hb (by simpa [STerm.subst, STerm.readsF] using hf)
  | .shImm _ _ x, hb, hf =>
      STerm.readsFT_spec h x hb (by simpa [STerm.subst, STerm.readsF] using hf)
  | .aget a _ _ i, hb, hf => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.readsF, Bool.or_eq_true] at hf
      simp only [STerm.readsFT, Bool.or_eq_true]
      exact hf.imp (SArr.readsFT_spec h a hb.1) (STerm.readsFT_spec h i hb.2)
  | .cin _, _, _ => rfl
  | .aluF _ _ x y o, hb, hf => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.readsF, Bool.or_eq_true] at hf
      simp only [STerm.readsFT, Bool.or_eq_true]
      exact hf.imp (Or.imp (STerm.readsFT_spec h x hb.1.1) (STerm.readsFT_spec h y hb.1.2))
        (STerm.readsFT_spec h o hb.2)
  | .carryW _ x y c, hb, hf => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.readsF, Bool.or_eq_true] at hf
      simp only [STerm.readsFT, Bool.or_eq_true]
      exact hf.imp (Or.imp (STerm.readsFT_spec h x hb.1.1) (STerm.readsFT_spec h y hb.1.2))
        (STerm.readsFT_spec h c hb.2)
  | .carryF _ _ x y c, hb, hf => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.readsF, Bool.or_eq_true] at hf
      simp only [STerm.readsFT, Bool.or_eq_true]
      exact hf.imp (Or.imp (STerm.readsFT_spec h x hb.1.1) (STerm.readsFT_spec h y hb.1.2))
        (STerm.readsFT_spec h c hb.2)
  | .mulx _ x y, hb, hf => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.readsF, Bool.or_eq_true] at hf
      simp only [STerm.readsFT, Bool.or_eq_true]
      exact hf.imp (STerm.readsFT_spec h x hb.1) (STerm.readsFT_spec h y hb.2)
  | .cout _ x y c, hb, hf => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.readsF, Bool.or_eq_true] at hf
      simp only [STerm.readsFT, Bool.or_eq_true]
      exact hf.imp (Or.imp (STerm.readsFT_spec h x hb.1.1) (STerm.readsFT_spec h y hb.1.2))
        (STerm.readsFT_spec h c hb.2)
  | .sel x y c, hb, hf => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.readsF, Bool.or_eq_true] at hf
      simp only [STerm.readsFT, Bool.or_eq_true]
      exact hf.imp (Or.imp (STerm.readsFT_spec h x hb.1.1) (STerm.readsFT_spec h y hb.1.2))
        (STerm.readsFT_spec h c hb.2)
  | .setcc _ x y, hb, hf => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simp only [STerm.subst, STerm.readsF, Bool.or_eq_true] at hf
      simp only [STerm.readsFT, Bool.or_eq_true]
      exact hf.imp (STerm.readsFT_spec h x hb.1) (STerm.readsFT_spec h y hb.2)
  | .ref k, hb, hf => by
      simp only [STerm.refsLt, decide_eq_true_eq] at hb
      obtain ⟨e, he, ok⟩ := h.get hb
      simp only [STerm.readsFT, he, Option.map_some, Option.getD_some]
      exact ok.2.2.1 hf

theorem SArr.readsFT_spec (h : TblOK σ E) :
    ∀ a : SArr, a.refsLt E.size = true → (a.subst σ).readsF = true → a.readsFT E = true
  | .cell _, _, hf => by simp [SArr.subst, SArr.readsF] at hf
  | .aset a _ _ i w, hb, hf => by
      simp only [SArr.refsLt, Bool.and_eq_true] at hb
      simp only [SArr.subst, SArr.readsF, Bool.or_eq_true] at hf
      simp only [SArr.readsFT, Bool.or_eq_true]
      exact hf.imp (Or.imp (SArr.readsFT_spec h a hb.1.1) (STerm.readsFT_spec h i hb.1.2))
        (STerm.readsFT_spec h w hb.2)
  | .zero _ _, _, hf => by simp [SArr.subst, SArr.readsF] at hf
end

theorem STerm.wbT_spec (h : TblOK σ E) :
    ∀ t : STerm, t.refsLt E.size = true →
      (t.subst σ).wbase = (t.wbT E).subst σ ∧ (t.subst σ).wbase.wknown = t.wbkT E
  | .immAt _ x, hb => by
      simpa only [STerm.subst, STerm.wbase, STerm.wbT, STerm.wbkT] using STerm.wbT_spec h x hb
  | .bin _ x _, hb => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simpa only [STerm.subst, STerm.wbase, STerm.wbT, STerm.wbkT] using STerm.wbT_spec h x hb.1
  | .un _ x, hb => by
      simpa only [STerm.subst, STerm.wbase, STerm.wbT, STerm.wbkT] using STerm.wbT_spec h x hb
  | .shImm _ _ x, hb => by
      simpa only [STerm.subst, STerm.wbase, STerm.wbT, STerm.wbkT] using STerm.wbT_spec h x hb
  | .sel x _ _, hb => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      simpa only [STerm.subst, STerm.wbase, STerm.wbT, STerm.wbkT] using
        STerm.wbT_spec h x hb.1.1
  | .ref k, hb => by
      simp only [STerm.refsLt, decide_eq_true_eq] at hb
      obtain ⟨e, he, ok⟩ := h.get hb
      simp only [STerm.subst, STerm.wbT, STerm.wbkT, he, Option.map_some, Option.getD_some]
      exact ⟨ok.2.2.2.1, ok.2.2.2.2⟩
  | .reg _, _ => ⟨rfl, rfl⟩
  | .immW _ _, _ => ⟨rfl, rfl⟩
  | .aget _ _ _ _, _ => ⟨rfl, rfl⟩
  | .cin _, _ => ⟨rfl, rfl⟩
  | .aluF _ _ _ _ _, _ => ⟨rfl, rfl⟩
  | .carryW _ _ _ _, _ => ⟨rfl, rfl⟩
  | .carryF _ _ _ _ _, _ => ⟨rfl, rfl⟩
  | .mulx _ _ _, _ => ⟨rfl, rfl⟩
  | .cout _ _ _ _, _ => ⟨rfl, rfl⟩
  | .setcc _ _ _, _ => ⟨rfl, rfl⟩

end TblOK

/-- The entries of `E` read only entries below `E.size`, by node and by width base. -/
def TBnd (E : Array TEnt) : Prop :=
  ∀ k (h : k < E.size), E[k].node.refsLt E.size = true ∧ E[k].wb.refsLt E.size = true

theorem STerm.wbT_refsLt {E : Array TEnt} (hE : TBnd E) :
    ∀ t : STerm, t.refsLt E.size = true → (t.wbT E).refsLt E.size = true
  | .immAt _ x, hb => STerm.wbT_refsLt hE x hb
  | .bin _ x _, hb => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      exact STerm.wbT_refsLt hE x hb.1
  | .sel x _ _, hb => by
      simp only [STerm.refsLt, Bool.and_eq_true] at hb
      exact STerm.wbT_refsLt hE x hb.1.1
  | .un _ x, hb => STerm.wbT_refsLt hE x hb
  | .shImm _ _ x, hb => STerm.wbT_refsLt hE x hb
  | .ref k, hb => by
      simp only [STerm.refsLt, decide_eq_true_eq] at hb
      simp only [STerm.wbT, Array.getElem?_eq_getElem hb, Option.map_some, Option.getD_some]
      exact (hE k hb).2
  | .reg _, hb => hb
  | .immW _ _, hb => hb
  | .aget _ _ _ _, hb => hb
  | .cin _, hb => hb
  | .aluF _ _ _ _ _, hb => hb
  | .carryW _ _ _ _, hb => hb
  | .carryF _ _ _ _ _, hb => hb
  | .mulx _ _ _, hb => hb
  | .cout _ _ _ _, hb => hb
  | .setcc _ _ _, hb => hb

/-- The entry of the node `n` over the table `E`. -/
def mkEnt (E : Array TEnt) (n : STerm) : TEnt :=
  ⟨n, (n.varsT E).eraseDups, n.readsFT E, n.wbT E, n.wbkT E⟩

/-- A table that some substitution agrees with, and whose entries read only its own
    entries. -/
def TValid (E : Array TEnt) : Prop := (∃ σ, TblOK σ E) ∧ TBnd E

theorem tValid_empty : TValid #[] :=
  ⟨⟨fun k => .ref k, fun k h => by simp at h⟩, fun k h => by simp at h⟩

theorem TValid.push {E : Array TEnt} (hv : TValid E) {n : STerm}
    (hn : n.refsLt E.size = true) : TValid (E.push (mkEnt E n)) := by
  obtain ⟨⟨σ, hσ⟩, hb⟩ := hv
  let σ' : Nat → STerm := fun j => if j = E.size then n.subst σ else σ j
  have hag : ∀ k, k < E.size → σ k = σ' k := fun k hk => by
    simp only [σ', ite_eq_right (Nat.ne_of_lt hk)]
  have hwb := STerm.wbT_refsLt hb n hn
  refine ⟨⟨σ', fun k hk => ?_⟩, fun k hk => ?_⟩
  · rw [Array.size_push] at hk
    rcases Nat.lt_or_ge k E.size with hk' | hk'
    · rw [Array.getElem_push_lt hk']
      obtain ⟨h1, h2, h3, h4, h5⟩ := hσ k hk'
      have e : σ' k = σ k := (hag k hk').symm
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [e, h1]; exact STerm.subst_congr hag _ (hb k hk').1
      · rw [e]; exact h2
      · rw [e]; exact h3
      · rw [e, h4]; exact STerm.subst_congr hag _ (hb k hk').2
      · rw [e]; exact h5
    · have hk2 : k = E.size := by omega
      subst hk2
      rw [Array.getElem_push_eq]
      have e : σ' E.size = n.subst σ := by simp [σ']
      obtain ⟨w1, w2⟩ := STerm.wbT_spec hσ n hn
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [e]; exact STerm.subst_congr hag _ hn
      · intro v hv
        rw [e] at hv
        exact List.mem_eraseDups.mpr (STerm.varsT_spec hσ n hn v hv)
      · intro hf
        rw [e] at hf
        exact STerm.readsFT_spec hσ n hn hf
      · rw [e, w1]; exact STerm.subst_congr hag _ hwb
      · rw [e]; exact w2
  · rw [Array.size_push] at hk ⊢
    rcases Nat.lt_or_ge k E.size with hk' | hk'
    · rw [Array.getElem_push_lt hk']
      exact ⟨STerm.refsLt_mono (by omega) _ (hb k hk').1,
        STerm.refsLt_mono (by omega) _ (hb k hk').2⟩
    · have hk2 : k = E.size := by omega
      subst hk2
      rw [Array.getElem_push_eq]
      exact ⟨STerm.refsLt_mono (by omega) _ hn, STerm.refsLt_mono (by omega) _ hwb⟩

/-- A term table with an index from nodes to entries. -/
structure Tbl where
  /-- The entries. -/
  ents : Array TEnt
  /-- The index of each node. -/
  idx : Std.HashMap STerm Nat

/-- The empty term table. -/
def Tbl.empty : Tbl := ⟨#[], {}⟩

/-- The table `T` with the node `n` appended, and the entry of `n`; `n` itself when it reads
    an entry outside the table. -/
def Tbl.push (T : Tbl) (n : STerm) : Tbl × STerm :=
  if n.refsLt T.ents.size then
    (⟨T.ents.push (mkEnt T.ents n), T.idx.insert n T.ents.size⟩, .ref T.ents.size)
  else (T, n)

/-- The entry of the node `n` in the table `T`, added when `T` has none. The index is a
    hint: its answer is checked against the table. -/
def Tbl.share (T : Tbl) (n : STerm) : Tbl × STerm :=
  match T.idx[n]? with
  | some k => if T.ents[k]?.map TEnt.node = some n then (T, .ref k) else T.push n
  | none => T.push n

/-- The word `t` as an entry of the table `T`, bottom-up: each node with children
    interned is shared. -/
def Tbl.intern (T : Tbl) : STerm → Tbl × STerm
  | .immAt n x => let p := T.intern x; p.1.share (.immAt n p.2)
  | .bin m x y =>
      let p := T.intern x
      let q := p.1.intern y
      q.1.share (.bin m p.2 q.2)
  | .un m x => let p := T.intern x; p.1.share (.un m p.2)
  | .shImm m k x => let p := T.intern x; p.1.share (.shImm m k p.2)
  | .aget a w n i => let p := T.intern i; p.1.share (.aget a w n p.2)
  | .aluF op ofl x y o =>
      let p := T.intern x
      let q := p.1.intern y
      let r := q.1.intern o
      r.1.share (.aluF op ofl p.2 q.2 r.2)
  | .carryW op x y c =>
      let p := T.intern x
      let q := p.1.intern y
      let r := q.1.intern c
      r.1.share (.carryW op p.2 q.2 r.2)
  | .carryF op ofl x y c =>
      let p := T.intern x
      let q := p.1.intern y
      let r := q.1.intern c
      r.1.share (.carryF op ofl p.2 q.2 r.2)
  | .mulx hi x y =>
      let p := T.intern x
      let q := p.1.intern y
      q.1.share (.mulx hi p.2 q.2)
  | .cout sub x y c =>
      let p := T.intern x
      let q := p.1.intern y
      let r := q.1.intern c
      r.1.share (.cout sub p.2 q.2 r.2)
  | .sel x y c =>
      let p := T.intern x
      let q := p.1.intern y
      let r := q.1.intern c
      r.1.share (.sel p.2 q.2 r.2)
  | .setcc cc x y =>
      let p := T.intern x
      let q := p.1.intern y
      q.1.share (.setcc cc p.2 q.2)
  | .reg r => (T, .reg r)
  | .immW w n => (T, .immW w n)
  | .cin ofl => (T, .cin ofl)
  | .ref k => (T, .ref k)

theorem Tbl.push_ext (T : Tbl) (n : STerm) : TExt T.ents (T.push n).1.ents := by
  unfold Tbl.push
  split
  · exact TExt.push _ _
  · exact TExt.refl _

theorem Tbl.share_ext (T : Tbl) (n : STerm) : TExt T.ents (T.share n).1.ents := by
  unfold Tbl.share
  split
  · split
    · exact TExt.refl _
    · exact Tbl.push_ext T n
  · exact Tbl.push_ext T n

theorem Tbl.push_valid {T : Tbl} (hv : TValid T.ents) (n : STerm) :
    TValid (T.push n).1.ents := by
  unfold Tbl.push
  split
  · exact hv.push (by assumption)
  · exact hv

theorem Tbl.share_valid {T : Tbl} (hv : TValid T.ents) (n : STerm) :
    TValid (T.share n).1.ents := by
  unfold Tbl.share
  split
  · split
    · exact hv
    · exact Tbl.push_valid hv n
  · exact Tbl.push_valid hv n

theorem Tbl.push_subst {σ : Nat → STerm} {E : Array TEnt} (T : Tbl) (n : STerm)
    (hx : TExt (T.push n).1.ents E) (h : TblOK σ E) : (T.push n).2.subst σ = n.subst σ := by
  unfold Tbl.push at hx ⊢
  split
  · rename_i hn
    rw [ite_eq_left hn] at hx
    have he : E[T.ents.size]? = some (mkEnt T.ents n) := by
      have := hx T.ents.size (by simp)
      simpa using this
    exact (h.entry he).1
  · rfl

theorem Tbl.share_subst {σ : Nat → STerm} {E : Array TEnt} (T : Tbl) (n : STerm)
    (hx : TExt (T.share n).1.ents E) (h : TblOK σ E) : (T.share n).2.subst σ = n.subst σ := by
  unfold Tbl.share at hx ⊢
  split
  · rename_i k hidx
    rw [hidx] at hx
    split
    · rename_i hk
      simp only [hk, ↓reduceIte] at hx
      obtain ⟨e, he, hn⟩ := Option.map_eq_some_iff.mp hk
      have hks : k < T.ents.size := by
        rcases Nat.lt_or_ge k T.ents.size with h' | h'
        · exact h'
        · rw [Array.getElem?_eq_none h'] at he; cases he
      have he' : E[k]? = some e := by
        rw [hx k hks, ← Array.getElem?_eq_getElem hks, he]
      rw [STerm.subst, (h.entry he').1, hn]
    · rename_i hk
      simp only [hk, ↓reduceIte] at hx
      exact Tbl.push_subst T n hx h
  · rename_i hidx
    rw [hidx] at hx
    exact Tbl.push_subst T n hx h

/-! ### Interning -/

theorem Tbl.intern_ext : ∀ (T : Tbl) (t : STerm), TExt T.ents (T.intern t).1.ents
  | T, .immAt _ x => (Tbl.intern_ext T x).trans (Tbl.share_ext _ _)
  | T, .bin _ x y =>
      ((Tbl.intern_ext T x).trans (Tbl.intern_ext _ y)).trans (Tbl.share_ext _ _)
  | T, .un _ x => (Tbl.intern_ext T x).trans (Tbl.share_ext _ _)
  | T, .shImm _ _ x => (Tbl.intern_ext T x).trans (Tbl.share_ext _ _)
  | T, .aget _ _ _ i => (Tbl.intern_ext T i).trans (Tbl.share_ext _ _)
  | T, .aluF _ _ x y o =>
      (((Tbl.intern_ext T x).trans (Tbl.intern_ext _ y)).trans (Tbl.intern_ext _ o)).trans
        (Tbl.share_ext _ _)
  | T, .carryW _ x y c =>
      (((Tbl.intern_ext T x).trans (Tbl.intern_ext _ y)).trans (Tbl.intern_ext _ c)).trans
        (Tbl.share_ext _ _)
  | T, .carryF _ _ x y c =>
      (((Tbl.intern_ext T x).trans (Tbl.intern_ext _ y)).trans (Tbl.intern_ext _ c)).trans
        (Tbl.share_ext _ _)
  | T, .mulx _ x y =>
      ((Tbl.intern_ext T x).trans (Tbl.intern_ext _ y)).trans (Tbl.share_ext _ _)
  | T, .cout _ x y c =>
      (((Tbl.intern_ext T x).trans (Tbl.intern_ext _ y)).trans (Tbl.intern_ext _ c)).trans
        (Tbl.share_ext _ _)
  | T, .sel x y c =>
      (((Tbl.intern_ext T x).trans (Tbl.intern_ext _ y)).trans (Tbl.intern_ext _ c)).trans
        (Tbl.share_ext _ _)
  | T, .setcc _ x y =>
      ((Tbl.intern_ext T x).trans (Tbl.intern_ext _ y)).trans (Tbl.share_ext _ _)
  | _, .reg _ => TExt.refl _
  | _, .immW _ _ => TExt.refl _
  | _, .cin _ => TExt.refl _
  | _, .ref _ => TExt.refl _

theorem Tbl.intern_valid : ∀ (T : Tbl) (t : STerm), TValid T.ents → TValid (T.intern t).1.ents
  | T, .immAt _ x, hv => Tbl.share_valid (Tbl.intern_valid T x hv) _
  | T, .bin _ x y, hv =>
      Tbl.share_valid (Tbl.intern_valid _ y (Tbl.intern_valid T x hv)) _
  | T, .un _ x, hv => Tbl.share_valid (Tbl.intern_valid T x hv) _
  | T, .shImm _ _ x, hv => Tbl.share_valid (Tbl.intern_valid T x hv) _
  | T, .aget _ _ _ i, hv => Tbl.share_valid (Tbl.intern_valid T i hv) _
  | T, .aluF _ _ x y o, hv =>
      Tbl.share_valid (Tbl.intern_valid _ o (Tbl.intern_valid _ y (Tbl.intern_valid T x hv))) _
  | T, .carryW _ x y c, hv =>
      Tbl.share_valid (Tbl.intern_valid _ c (Tbl.intern_valid _ y (Tbl.intern_valid T x hv))) _
  | T, .carryF _ _ x y c, hv =>
      Tbl.share_valid (Tbl.intern_valid _ c (Tbl.intern_valid _ y (Tbl.intern_valid T x hv))) _
  | T, .mulx _ x y, hv =>
      Tbl.share_valid (Tbl.intern_valid _ y (Tbl.intern_valid T x hv)) _
  | T, .cout _ x y c, hv =>
      Tbl.share_valid (Tbl.intern_valid _ c (Tbl.intern_valid _ y (Tbl.intern_valid T x hv))) _
  | T, .sel x y c, hv =>
      Tbl.share_valid (Tbl.intern_valid _ c (Tbl.intern_valid _ y (Tbl.intern_valid T x hv))) _
  | T, .setcc _ x y, hv =>
      Tbl.share_valid (Tbl.intern_valid _ y (Tbl.intern_valid T x hv)) _
  | _, .reg _, hv => hv
  | _, .immW _ _, hv => hv
  | _, .cin _, hv => hv
  | _, .ref _, hv => hv

/-- **Interning keeps the word.** For every substitution that agrees with a table extending
    the one interning ends in, the interned word and the word have one substitution
    instance. -/
theorem Tbl.intern_subst {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E) :
    ∀ (T : Tbl) (t : STerm), TExt (T.intern t).1.ents E →
      (T.intern t).2.subst σ = t.subst σ
  | T, .immAt _ x, hx => by
      simp only [Tbl.intern] at hx ⊢
      rw [Tbl.share_subst _ _ hx h, STerm.subst, STerm.subst,
        Tbl.intern_subst h T x ((Tbl.share_ext _ _).trans hx)]
  | T, .bin _ x y, hx => by
      simp only [Tbl.intern] at hx ⊢
      have h2 := (Tbl.share_ext _ _).trans hx
      have h1 := (Tbl.intern_ext _ y).trans h2
      rw [Tbl.share_subst _ _ hx h, STerm.subst, STerm.subst, Tbl.intern_subst h T x h1,
        Tbl.intern_subst h _ y h2]
  | T, .un _ x, hx => by
      simp only [Tbl.intern] at hx ⊢
      rw [Tbl.share_subst _ _ hx h, STerm.subst, STerm.subst,
        Tbl.intern_subst h T x ((Tbl.share_ext _ _).trans hx)]
  | T, .shImm _ _ x, hx => by
      simp only [Tbl.intern] at hx ⊢
      rw [Tbl.share_subst _ _ hx h, STerm.subst, STerm.subst,
        Tbl.intern_subst h T x ((Tbl.share_ext _ _).trans hx)]
  | T, .aget _ _ _ i, hx => by
      simp only [Tbl.intern] at hx ⊢
      rw [Tbl.share_subst _ _ hx h, STerm.subst, STerm.subst,
        Tbl.intern_subst h T i ((Tbl.share_ext _ _).trans hx)]
  | T, .aluF _ _ x y o, hx => by
      simp only [Tbl.intern] at hx ⊢
      have h3 := (Tbl.share_ext _ _).trans hx
      have h2 := (Tbl.intern_ext _ o).trans h3
      have h1 := (Tbl.intern_ext _ y).trans h2
      rw [Tbl.share_subst _ _ hx h, STerm.subst, STerm.subst, Tbl.intern_subst h T x h1,
        Tbl.intern_subst h _ y h2, Tbl.intern_subst h _ o h3]
  | T, .carryW _ x y c, hx => by
      simp only [Tbl.intern] at hx ⊢
      have h3 := (Tbl.share_ext _ _).trans hx
      have h2 := (Tbl.intern_ext _ c).trans h3
      have h1 := (Tbl.intern_ext _ y).trans h2
      rw [Tbl.share_subst _ _ hx h, STerm.subst, STerm.subst, Tbl.intern_subst h T x h1,
        Tbl.intern_subst h _ y h2, Tbl.intern_subst h _ c h3]
  | T, .carryF _ _ x y c, hx => by
      simp only [Tbl.intern] at hx ⊢
      have h3 := (Tbl.share_ext _ _).trans hx
      have h2 := (Tbl.intern_ext _ c).trans h3
      have h1 := (Tbl.intern_ext _ y).trans h2
      rw [Tbl.share_subst _ _ hx h, STerm.subst, STerm.subst, Tbl.intern_subst h T x h1,
        Tbl.intern_subst h _ y h2, Tbl.intern_subst h _ c h3]
  | T, .mulx _ x y, hx => by
      simp only [Tbl.intern] at hx ⊢
      have h2 := (Tbl.share_ext _ _).trans hx
      have h1 := (Tbl.intern_ext _ y).trans h2
      rw [Tbl.share_subst _ _ hx h, STerm.subst, STerm.subst, Tbl.intern_subst h T x h1,
        Tbl.intern_subst h _ y h2]
  | T, .cout _ x y c, hx => by
      simp only [Tbl.intern] at hx ⊢
      have h3 := (Tbl.share_ext _ _).trans hx
      have h2 := (Tbl.intern_ext _ c).trans h3
      have h1 := (Tbl.intern_ext _ y).trans h2
      rw [Tbl.share_subst _ _ hx h, STerm.subst, STerm.subst, Tbl.intern_subst h T x h1,
        Tbl.intern_subst h _ y h2, Tbl.intern_subst h _ c h3]
  | T, .sel x y c, hx => by
      simp only [Tbl.intern] at hx ⊢
      have h3 := (Tbl.share_ext _ _).trans hx
      have h2 := (Tbl.intern_ext _ c).trans h3
      have h1 := (Tbl.intern_ext _ y).trans h2
      rw [Tbl.share_subst _ _ hx h, STerm.subst, STerm.subst, Tbl.intern_subst h T x h1,
        Tbl.intern_subst h _ y h2, Tbl.intern_subst h _ c h3]
  | T, .setcc _ x y, hx => by
      simp only [Tbl.intern] at hx ⊢
      have h2 := (Tbl.share_ext _ _).trans hx
      have h1 := (Tbl.intern_ext _ y).trans h2
      rw [Tbl.share_subst _ _ hx h, STerm.subst, STerm.subst, Tbl.intern_subst h T x h1,
        Tbl.intern_subst h _ y h2]
  | _, .reg _, _ => rfl
  | _, .immW _ _, _ => rfl
  | _, .cin _, _ => rfl
  | _, .ref _, _ => rfl

/-! ### The shared run -/

/-- The registers `ds` of `ss` interned in `T`. -/
def Tbl.internRegs (T : Tbl) (ss : SSt) : List String → Tbl × SSt
  | [] => (T, ss)
  | d :: ds =>
      let p := T.intern (ss.regs d)
      p.1.internRegs (ss.putR d p.2) ds

/-- The registers `ds` and the carry and overflow flags of `ss` interned in `T`. -/
def Tbl.internSt (T : Tbl) (ss : SSt) (ds : List String) : Tbl × SSt :=
  let p := T.internRegs ss ds
  let c := p.1.intern p.2.cf
  let o := c.1.intern p.2.of
  (o.1, { p.2 with cf := c.2, of := o.2 })

theorem Tbl.internRegs_ext : ∀ (T : Tbl) (ss : SSt) (ds : List String),
    TExt T.ents (T.internRegs ss ds).1.ents
  | T, _, [] => TExt.refl T.ents
  | T, ss, d :: ds => (Tbl.intern_ext T (ss.regs d)).trans (Tbl.internRegs_ext _ _ ds)

theorem Tbl.internRegs_valid : ∀ (T : Tbl) (ss : SSt) (ds : List String), TValid T.ents →
    TValid (T.internRegs ss ds).1.ents
  | _, _, [], hv => hv
  | T, ss, d :: ds, hv => Tbl.internRegs_valid _ _ ds (Tbl.intern_valid T (ss.regs d) hv)

theorem Tbl.internRegs_subst {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E) :
    ∀ (T : Tbl) (ss : SSt) (ds : List String), TExt (T.internRegs ss ds).1.ents E →
      (T.internRegs ss ds).2.subst σ = ss.subst σ
  | _, _, [], _ => rfl
  | T, ss, d :: ds, hx => by
      simp only [Tbl.internRegs] at hx ⊢
      rw [Tbl.internRegs_subst h _ _ ds hx]
      have hd := Tbl.intern_subst h T (ss.regs d) ((Tbl.internRegs_ext _ _ ds).trans hx)
      refine SSt.ext (fun r => ?_) rfl rfl rfl rfl rfl rfl
      rw [SSt.subst_regs_apply, SSt.putR_regs, SSt.subst_regs_apply]
      split
      · subst r; exact hd
      · rfl

theorem Tbl.internSt_ext (T : Tbl) (ss : SSt) (ds : List String) :
    TExt T.ents (T.internSt ss ds).1.ents :=
  ((Tbl.internRegs_ext T ss ds).trans (Tbl.intern_ext _ _)).trans (Tbl.intern_ext _ _)

theorem Tbl.internSt_valid {T : Tbl} (hv : TValid T.ents) (ss : SSt) (ds : List String) :
    TValid (T.internSt ss ds).1.ents :=
  Tbl.intern_valid _ _ (Tbl.intern_valid _ _ (Tbl.internRegs_valid T ss ds hv))

theorem Tbl.internSt_subst {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E) (T : Tbl)
    (ss : SSt) (ds : List String) (hx : TExt (T.internSt ss ds).1.ents E) :
    (T.internSt ss ds).2.subst σ = ss.subst σ := by
  simp only [Tbl.internSt] at hx ⊢
  have h3 := hx
  have h2 := (Tbl.intern_ext _ _).trans h3
  have h1 := (Tbl.intern_ext _ _).trans h2
  have e := Tbl.internRegs_subst h T ss ds h1
  rw [SSt.subst_with, Tbl.intern_subst h _ _ h2, Tbl.intern_subst h _ _ h3, ← e]
  rfl

/-- The symbolic run of a list of instructions over the table `T` under the symbolic step
    `sym`: after each step the registers it writes and the carry and overflow flags are
    interned. The result is the final table and the description `symRun` gives, with words
    over the table. -/
def tRun : List LinstrRM → SSt → Tbl → optParam (LinstrRM → SSt → SOut) symStep → Tbl × SOut
  | [], ss, T, _ => (T, .ok ss [])
  | i :: is, ss, T, sym =>
      match sym i ss with
      | .ok ss1 g1 =>
          let p := T.internSt ss1 (ss1.newWr ss)
          let r := tRun is p.2 p.1 sym
          match r.2 with
          | .ok ss2 g2 => (r.1, .ok ss2 (g1 ++ g2))
          | .fail => (r.1, .fail)
          | .unk => (r.1, .unk)
      | .fail => (T, .fail)
      | .unk => (T, .unk)

theorem tRun_ext_at (sym : LinstrRM → SSt → SOut) :
    ∀ (is : List LinstrRM) (ss : SSt) (T : Tbl), TExt T.ents (tRun is ss T sym).1.ents
  | [], _, T => TExt.refl T.ents
  | i :: is, ss, T => by
      simp only [tRun]
      split
      · rename_i ss1 _ _
        have := (Tbl.internSt_ext T ss1 (ss1.newWr ss)).trans
          (tRun_ext_at sym is (T.internSt ss1 (ss1.newWr ss)).2 _)
        split <;> exact this
      · exact TExt.refl _
      · exact TExt.refl _

theorem tRun_ext (is : List LinstrRM) (ss : SSt) (T : Tbl) :
    TExt T.ents (tRun is ss T).1.ents := tRun_ext_at symStep is ss T

theorem tRun_valid_at (sym : LinstrRM → SSt → SOut) :
    ∀ (is : List LinstrRM) (ss : SSt) (T : Tbl), TValid T.ents →
    TValid (tRun is ss T sym).1.ents
  | [], _, _, hv => hv
  | i :: is, ss, T, hv => by
      simp only [tRun]
      split
      · rename_i ss1 _ _
        have := tRun_valid_at sym is
          (T.internSt ss1 (ss1.newWr ss)).2 _
          (Tbl.internSt_valid hv ss1 (ss1.newWr ss))
        split <;> exact this
      · exact hv
      · exact hv

theorem tRun_valid (is : List LinstrRM) (ss : SSt) (T : Tbl) (hv : TValid T.ents) :
    TValid (tRun is ss T).1.ents := tRun_valid_at symStep is ss T hv

/-- **The shared run describes the symbolic run**, for every symbolic step that commutes
    with substitution. For every substitution that agrees with a table extending the final
    table of `tRun`, its description is the description `symRun` gives from the substituted
    start. -/
theorem tRun_subst_at {sym : LinstrRM → SSt → SOut}
    (hsub : ∀ (σ : Nat → STerm) (i : LinstrRM) (ss : SSt),
      sym i (ss.subst σ) = (sym i ss).subst σ) {σ : Nat → STerm} {E : Array TEnt}
    (h : TblOK σ E) :
    ∀ (is : List LinstrRM) (ss : SSt) (T : Tbl), TExt (tRun is ss T sym).1.ents E →
      (tRun is ss T sym).2.subst σ = symRun is (ss.subst σ) sym
  | [], _, _, _ => rfl
  | i :: is, ss, T, hx => by
      simp only [symRun, hsub]
      simp only [tRun] at hx ⊢
      cases hs : sym i ss with
      | ok ss1 g1 =>
          simp only [hs] at hx ⊢
          generalize hp : T.internSt ss1 (ss1.newWr ss) = p at hx ⊢
          have hx' : TExt (tRun is p.2 p.1 sym).1.ents E := by split at hx <;> exact hx
          have ih := tRun_subst_at hsub h is _ _ hx'
          have e2 := Tbl.internSt_subst h T ss1 (ss1.newWr ss)
            (by rw [hp]; exact (tRun_ext_at sym is _ _).trans hx')
          rw [hp] at e2
          rw [e2] at ih
          simp only [SOut.subst]
          rw [← ih]
          generalize tRun is p.2 p.1 sym = r
          obtain ⟨T', o⟩ := r
          cases o <;> simp [SOut.subst]
      | fail => rfl
      | unk => rfl

/-- **The shared run describes the symbolic run.** For every substitution that agrees with a
    table extending the final table of `tRun`, its description is the description `symRun`
    gives from the substituted start. -/
theorem tRun_subst {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E) (is : List LinstrRM)
    (ss : SSt) (T : Tbl) (hx : TExt (tRun is ss T).1.ents E) :
    (tRun is ss T).2.subst σ = symRun is (ss.subst σ) :=
  tRun_subst_at symStep_subst h is ss T hx

/-! ## 14b. Canonical keys

A carry step has two forms. In the value form the carry is a register: the three-source `ADCX
d, [a, b, c]` of `lsemStepMC` is the word `(a + b) + c` (`bin "ADD"`) and `ADCXHI` its
carry-out (`STerm.cout`). In the flag form the carry is the carry flag: `ADD`, `ADC`, `ADCX`
(and `ADOX` on the overflow flag) are the words `bin "ADD"` and `carryW`, and their carry-out
the flag terms `aluF` and `carryF`. The two forms of one computation have different terms.

`STerm.normC` is a normal form of one node over the normal forms of its children: a sum of
two words of width `64` is `carryW .adcx x y 0`, a sum of such a word and a bit is
`carryW .adcx x y c`, the words of `ADC`, `ADCX` and `ADOX` are `carryW .adcx`, every
carry-out of an addition of words of width `64` is `carryF .adcx false`, the carry and
overflow flags of `AND`, `OR`, `XOR` are the zero bit, the sources of an addition are in a
canonical order, and differences and borrows are normalised alike to `carryW .sbb` and
`carryF .sbb false`. The widths it needs are the widths that the outermost constructors fix
(`STerm.swC`), and those that facts `F` state of start registers. `CanonT.build F E` computes
the canonical keys of a term table `E` in one pass, hash-consing the keys, so that two words
with one canonical form (`canonEqT`) evaluate alike at every evaluation where the facts hold
(`canonEqT_ev`); `SG.impT` is a guard that the widths of the keys decide. The facts that the
check uses are the widths that the normalised guards of the source block state of start
registers (`guardFacts`), which hold wherever those guards hold (`guardFacts_sound`). -/

section Canon

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
  (x86_ADD x86_SUB x86_AND x86_OR x86_XOR waddcarry add_carry sub_borrow rflags_of_aluop
   rflags_of_bwop wunsigned)

/-! ### The words of one carry step -/

theorem carryWord_adc (a b : BitVec 64) (c : Bool) :
    carryWord .adc a b c = carryWord .adcx a b c := by
  simp only [carryWord, x86_ADC, x86_ADCX, waddcarry, rflags_of_aluop, add_carry]

theorem carryWord_adcx_comm (a b : BitVec 64) (c : Bool) :
    carryWord .adcx a b c = carryWord .adcx b a c := by
  simp only [carryWord, x86_ADCX, waddcarry, Nat.add_comm a.toNat b.toNat]

theorem carryBit_adc (a b : BitVec 64) (c : Bool) :
    carryBit .adc false a b c = carryBit .adcx false a b c := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [carryBit, x86_ADC, x86_ADCX, waddcarry, rflags_of_aluop, add_carry, wunsigned,
    Option.getD_some, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
  rw [decide_eq_decide]
  constructor
  · intro h
    by_contra h'
    exact h (Nat.mod_eq_of_lt (by omega))
  · intro h e
    have := Nat.mod_lt (a.toNat + b.toNat + (if c then 1 else 0)) (by norm_num : 0 < 2 ^ 64)
    omega

theorem carryBit_adcx_comm (a b : BitVec 64) (c : Bool) :
    carryBit .adcx false a b c = carryBit .adcx false b a c := by
  simp only [carryBit, x86_ADCX, waddcarry, Nat.add_comm a.toNat b.toNat]

theorem carryBit_adcx_zero (c : Bool) : carryBit .adcx false 0 0 c = false := by
  cases c <;> simp [carryBit, x86_ADCX, waddcarry]

theorem aluBit_add (a b : BitVec 64) : aluBit .add false a b = carryBit .adcx false a b false := by
  rw [← carryBit_adc]
  simp [aluBit, aluB5, x86_ADD, carryBit, x86_ADC, add_carry, rflags_of_aluop, BitVec.toNat_add]

theorem aluBit_logic {op : AluOp} (h : op = .and ∨ op = .or ∨ op = .xor) (ofl : Bool)
    (a b : BitVec 64) : aluBit op ofl a b = false := by
  rcases h with rfl | rfl | rfl <;> cases ofl <;>
    simp [aluBit, aluB5, x86_AND, x86_OR, x86_XOR, rflags_of_bwop]

theorem binW_add (a b : BitVec 64) : binW 64 "ADD" a b = carryWord .adcx a b false := by
  simp only [binW, applyOpnN, carryWord, x86_ADCX, waddcarry]
  apply BitVec.eq_of_toNat_eq
  simp

theorem binW_add_carry (a b : BitVec 64) (c : BitVec 1) :
    binW 64 "ADD" (carryWord .adcx a b false) (c.setWidth 64) =
      carryWord .adcx a b (c.getLsbD 0) := by
  simp only [binW, applyOpnN, carryWord, x86_ADCX, waddcarry]
  apply BitVec.eq_of_toNat_eq
  have hc : c.toNat = if c.getLsbD 0 then 1 else 0 := by
    have : c = 0#1 ∨ c = 1#1 := by bv_omega
    rcases this with rfl | rfl <;> rfl
  simp [BitVec.toNat_setWidth, hc]

theorem bv1_toNat (c : BitVec 1) : c.toNat = if c.getLsbD 0 then 1 else 0 := by
  have : c = 0#1 ∨ c = 1#1 := by bv_omega
  rcases this with rfl | rfl <;> rfl

theorem ite_bv1 (p : Prop) [Decidable p] :
    (if p then 1#1 else 0#1) = BitVec.ofBool (decide p) := by
  by_cases h : p <;> simp [h]

theorem carryBit_adcx_eq (a b : BitVec 64) (c : Bool) :
    carryBit .adcx false a b c = decide (2 ^ 64 ≤ a.toNat + b.toNat + (if c then 1 else 0)) := by
  simp only [carryBit, x86_ADCX, waddcarry, Option.getD_some]

theorem carryOutBit_eq (a b : BitVec 64) (c : BitVec 1) :
    JasminDialect.carryOutBit a b c = BitVec.ofBool (carryBit .adcx false a b (c.getLsbD 0)) := by
  rw [carryBit_adcx_eq, JasminDialect.carryOutBit, bv1_toNat]
  exact ite_bv1 _

theorem carryBit_sbb (a b : BitVec 64) (c : Bool) :
    carryBit .sbb false a b c = decide (a.toNat < b.toNat + (if c then 1 else 0)) := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [carryBit, x86_SBB, sub_borrow, wunsigned, Option.getD_some, Bool.false_eq_true,
    ↓reduceIte, BitVec.toNat_ofInt]
  rw [decide_eq_decide]
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem borrowOutBit_eq (a b : BitVec 64) (c : BitVec 1) :
    JasminDialect.borrowOutBit a b c = BitVec.ofBool (carryBit .sbb false a b (c.getLsbD 0)) := by
  rw [carryBit_sbb, JasminDialect.borrowOutBit, bv1_toNat]
  exact ite_bv1 _

theorem aluBit_sub (a b : BitVec 64) : aluBit .sub false a b = carryBit .sbb false a b false := by
  have ha := a.isLt
  have hb := b.isLt
  rw [carryBit_sbb]
  simp only [aluBit, aluB5, x86_SUB, Option.getD_some, Bool.false_eq_true, ↓reduceIte]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hd
    have h := of_decide_eq_true hd
    simp only [wunsigned, BitVec.toNat_sub] at h
    exact decide_eq_true (by omega)
  · intro hd
    have h := of_decide_eq_true hd
    exact decide_eq_true (by simp only [wunsigned, BitVec.toNat_sub]; omega)

theorem binW_sub (a b : BitVec 64) : binW 64 "SUB" a b = carryWord .sbb a b false := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [binW,
    ite_eq_right_iff.mpr (fun h : ("SUB" : String) = "MULXHI" => absurd h (by decide)), applyOpnN,
    Option.getD_some, carryWord, x86_SBB, sub_borrow, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofInt]
  omega

theorem binW_sub_borrow (a b : BitVec 64) (c : BitVec 1) :
    binW 64 "SUB" (carryWord .sbb a b false) (c.setWidth 64) =
      carryWord .sbb a b (c.getLsbD 0) := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := bv1_toNat c
  rw [← binW_sub]
  simp only [binW,
    ite_eq_right_iff.mpr (fun h : ("SUB" : String) = "MULXHI" => absurd h (by decide)), applyOpnN,
    Option.getD_some, carryWord, x86_SBB, sub_borrow]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofInt, BitVec.toNat_setWidth]
  cases h : c.getLsbD 0 <;> rw [h] at hc <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] <;>
    omega

/-! ### Substitution and evaluation -/

mutual
/-- Substitutions whose images evaluate alike give words that evaluate alike. -/
theorem STerm.ev_subst_congr {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {σ τ : Nat → STerm} (h : ∀ k, (σ k).ev V A C O = (τ k).ev V A C O) :
    ∀ t : STerm, (t.subst σ).ev V A C O = (t.subst τ).ev V A C O
  | .reg _ => rfl
  | .immW _ _ => rfl
  | .immAt _ x => by simp only [STerm.subst, STerm.ev]; rw [STerm.ev_subst_congr h x]
  | .bin _ x y => by
      simp only [STerm.subst, STerm.ev]; rw [STerm.ev_subst_congr h x, STerm.ev_subst_congr h y]
  | .un _ x => by simp only [STerm.subst, STerm.ev]; rw [STerm.ev_subst_congr h x]
  | .shImm _ _ x => by simp only [STerm.subst, STerm.ev]; rw [STerm.ev_subst_congr h x]
  | .aget a _ _ i => by
      simp only [STerm.subst, STerm.ev]; rw [SArr.ev_subst_congr h a, STerm.ev_subst_congr h i]
  | .cin _ => rfl
  | .aluF _ _ x y o => by
      simp only [STerm.subst, STerm.ev];
      rw [STerm.ev_subst_congr h x, STerm.ev_subst_congr h y, STerm.ev_subst_congr h o]
  | .carryW _ x y c => by
      simp only [STerm.subst, STerm.ev];
      rw [STerm.ev_subst_congr h x, STerm.ev_subst_congr h y, STerm.ev_subst_congr h c]
  | .carryF _ _ x y c => by
      simp only [STerm.subst, STerm.ev];
      rw [STerm.ev_subst_congr h x, STerm.ev_subst_congr h y, STerm.ev_subst_congr h c]
  | .mulx _ x y => by
      simp only [STerm.subst, STerm.ev]; rw [STerm.ev_subst_congr h x, STerm.ev_subst_congr h y]
  | .cout _ x y c => by
      simp only [STerm.subst, STerm.ev];
      rw [STerm.ev_subst_congr h x, STerm.ev_subst_congr h y, STerm.ev_subst_congr h c]
  | .sel x y c => by
      simp only [STerm.subst, STerm.ev];
      rw [STerm.ev_subst_congr h x, STerm.ev_subst_congr h y, STerm.ev_subst_congr h c]
  | .setcc _ x y => by
      simp only [STerm.subst, STerm.ev]; rw [STerm.ev_subst_congr h x, STerm.ev_subst_congr h y]
  | .ref k => h k

/-- Substitutions whose images evaluate alike give arrays that evaluate alike. -/
theorem SArr.ev_subst_congr {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {σ τ : Nat → STerm} (h : ∀ k, (σ k).ev V A C O = (τ k).ev V A C O) :
    ∀ a : SArr, (a.subst σ).ev V A C O = (a.subst τ).ev V A C O
  | .cell _ => rfl
  | .aset a _ _ i v => by
      simp only [SArr.subst, SArr.ev];
      rw [SArr.ev_subst_congr h a, STerm.ev_subst_congr h i, STerm.ev_subst_congr h v]
  | .zero _ _ => rfl
end

mutual
/-- Two substitutions in a row are one substitution. -/
theorem STerm.subst_subst (ρ σ : Nat → STerm) :
    ∀ t : STerm, (t.subst ρ).subst σ = t.subst (fun k => (ρ k).subst σ)
  | .reg _ => rfl
  | .immW _ _ => rfl
  | .immAt _ x => by simp only [STerm.subst, STerm.subst_subst ρ σ x]
  | .bin _ x y => by simp only [STerm.subst, STerm.subst_subst ρ σ x, STerm.subst_subst ρ σ y]
  | .un _ x => by simp only [STerm.subst, STerm.subst_subst ρ σ x]
  | .shImm _ _ x => by simp only [STerm.subst, STerm.subst_subst ρ σ x]
  | .aget a _ _ i => by simp only [STerm.subst, SArr.subst_subst ρ σ a, STerm.subst_subst ρ σ i]
  | .cin _ => rfl
  | .aluF _ _ x y o => by
      simp only [STerm.subst, STerm.subst_subst ρ σ x, STerm.subst_subst ρ σ y,
        STerm.subst_subst ρ σ o]
  | .carryW _ x y c => by
      simp only [STerm.subst, STerm.subst_subst ρ σ x, STerm.subst_subst ρ σ y,
        STerm.subst_subst ρ σ c]
  | .carryF _ _ x y c => by
      simp only [STerm.subst, STerm.subst_subst ρ σ x, STerm.subst_subst ρ σ y,
        STerm.subst_subst ρ σ c]
  | .mulx _ x y => by simp only [STerm.subst, STerm.subst_subst ρ σ x, STerm.subst_subst ρ σ y]
  | .cout _ x y c => by
      simp only [STerm.subst, STerm.subst_subst ρ σ x, STerm.subst_subst ρ σ y,
        STerm.subst_subst ρ σ c]
  | .sel x y c => by
      simp only [STerm.subst, STerm.subst_subst ρ σ x, STerm.subst_subst ρ σ y,
        STerm.subst_subst ρ σ c]
  | .setcc _ x y => by simp only [STerm.subst, STerm.subst_subst ρ σ x, STerm.subst_subst ρ σ y]
  | .ref _ => rfl

/-- Two substitutions in a row are one substitution. -/
theorem SArr.subst_subst (ρ σ : Nat → STerm) :
    ∀ a : SArr, (a.subst ρ).subst σ = a.subst (fun k => (ρ k).subst σ)
  | .cell _ => rfl
  | .aset a _ _ i v => by
      simp only [SArr.subst, SArr.subst_subst ρ σ a, STerm.subst_subst ρ σ i,
        STerm.subst_subst ρ σ v]
  | .zero _ _ => rfl
end

/-! ### Static widths -/

/-- The width the facts `F` state of the start register `r`. -/
def factW (F : List (String × Nat)) (r : String) : Option Nat := (F.find? (·.1 == r)).map (·.2)

/-- The width of a word over a table whose entries have the widths `W` (`none` when not
    known) and whose start registers have the widths the facts `F` state, when its outermost
    constructors fix it. -/
def STerm.swC (W : Array (Option Nat)) (F : List (String × Nat)) : STerm → Option Nat
  | .immW w _ => some w
  | .immAt _ x => x.swC W F
  | .bin _ x _ => x.swC W F
  | .un _ x => x.swC W F
  | .shImm _ _ x => x.swC W F
  | .aget _ w _ _ => some w
  | .cin _ => some 1
  | .carryW .. => some 64
  | .carryF .. => some 1
  | .mulx .. => some 64
  | .cout .. => some 1
  | .sel x _ _ => x.swC W F
  | .setcc .. => some 1
  | .ref k => W.getD k none
  | .reg r => factW F r
  | .aluF .. => none

theorem STerm.swC_ev {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {σ : Nat → STerm} {W : Array (Option Nat)} {F : List (String × Nat)}
    (hW : ∀ k w, W.getD k none = some w → ((σ k).ev V A C O).1 = w)
    (hF : ∀ r w, factW F r = some w → (V r).1 = w) :
    ∀ (t : STerm) (w : Nat), t.swC W F = some w → ((t.subst σ).ev V A C O).1 = w
  | .immW _ _, w, h => by
      simp only [STerm.swC, Option.some.injEq] at h; simp [STerm.subst, STerm.ev, h]
  | .immAt _ x, w, h => by
      simp only [STerm.swC] at h; simp only [STerm.subst, STerm.ev]; exact STerm.swC_ev hW hF x w h
  | .bin _ x _, w, h => by
      simp only [STerm.swC] at h; simp only [STerm.subst, STerm.ev]; exact STerm.swC_ev hW hF x w h
  | .un _ x, w, h => by
      simp only [STerm.swC] at h; simp only [STerm.subst, STerm.ev]; exact STerm.swC_ev hW hF x w h
  | .shImm _ _ x, w, h => by
      simp only [STerm.swC] at h; simp only [STerm.subst, STerm.ev]; exact STerm.swC_ev hW hF x w h
  | .aget _ _ _ _, w, h => by
      simp only [STerm.swC, Option.some.injEq] at h; simp [STerm.subst, STerm.ev, h]
  | .cin _, w, h => by
      simp only [STerm.swC, Option.some.injEq] at h; simp [STerm.subst, STerm.ev, h]
  | .carryW .., w, h => by
      simp only [STerm.swC, Option.some.injEq] at h; simp [STerm.subst, STerm.ev, h]
  | .carryF .., w, h => by
      simp only [STerm.swC, Option.some.injEq] at h; simp [STerm.subst, STerm.ev, h]
  | .mulx .., w, h => by
      simp only [STerm.swC, Option.some.injEq] at h; simp [STerm.subst, STerm.ev, h]
  | .cout .., w, h => by
      simp only [STerm.swC, Option.some.injEq] at h; simp [STerm.subst, STerm.ev, h]
  | .sel x _ _, w, h => by
      simp only [STerm.swC] at h; simp only [STerm.subst, STerm.ev]; exact STerm.swC_ev hW hF x w h
  | .setcc .., w, h => by
      simp only [STerm.swC, Option.some.injEq] at h; simp [STerm.subst, STerm.ev, h]
  | .ref k, w, h => by simp only [STerm.swC] at h; exact hW k w h
  | .reg r, w, h => by simp only [STerm.swC] at h; exact hF r w h
  | .aluF .., w, h => by simp [STerm.swC] at h

/-! ### The normal form of one node -/

/-- The sources of a commutative node are in canonical order unless this holds: a reference
    comes before a word that is no reference, and of two references the lower index comes
    first. -/
def swapC : STerm → STerm → Bool
  | .ref a, .ref b => b < a
  | .ref _, _ => false
  | _, .ref _ => true
  | _, _ => false

/-- The canonical add-with-carry word of `x`, `y` and the carry-in `c`. -/
def addWC (x y c : STerm) : STerm :=
  if swapC x y then .carryW .adcx y x c else .carryW .adcx x y c

/-- The canonical carry-out of `x + y + c`, the zero bit when both sources are the zero
    word. -/
def addFC (x y c : STerm) : STerm :=
  if x == .immW 64 0 && y == .immW 64 0 then .immW 1 0
  else if swapC x y then .carryF .adcx false y x c else .carryF .adcx false x y c

/-- The node a word stands for: the key `K` of a reference, the word itself otherwise. -/
def viewC (K : Array STerm) : STerm → STerm
  | .ref j => K.getD j (.ref j)
  | t => t

/-- **The normal form of one node** over a table with keys `K` and widths `W`. The value
    form and the flag form of one carry step, and the words of `ADC`, `ADCX` and `ADOX`, have
    one normal form: a sum `x + y` at width `64` is `carryW .adcx x y 0`, and a sum whose first
    source is such a word `carryW .adcx a b 0` and whose second source is a bit `c` is
    `carryW .adcx a b c`; the carry-out `cout` of sources of width `64`, the carry flag of
    `ADD`, `ADC`, `ADCX` and the overflow flag of `ADOX` are `carryF .adcx false x y c`; the
    carry and overflow flags of `AND`, `OR`, `XOR` at width `64` are the zero bit. The
    differences and borrows are normalised alike to `carryW .sbb` and `carryF .sbb false`.
    The sources of an addition are in canonical order (`swapC`). -/
def STerm.normC (K : Array STerm) (W : Array (Option Nat)) (F : List (String × Nat))
    (n : STerm) : STerm :=
  match n with
  | .carryW .sbb _ _ _ => n
  | .carryW _ x y c => addWC x y c
  | .carryF .sbb _ _ _ _ => n
  | .carryF .adc true _ _ _ => n
  | .carryF _ _ x y c => addFC x y c
  | .cout false x y c => if x.swC W F == some 64 && y.swC W F == some 64 then addFC x y c else n
  | .cout true x y c =>
      if x.swC W F == some 64 && y.swC W F == some 64 then .carryF .sbb false x y c else n
  | .aluF .add false x y _ =>
      if x.swC W F == some 64 && y.swC W F == some 64 then addFC x y (.immW 1 0) else n
  | .aluF .sub false x y _ =>
      if x.swC W F == some 64 && y.swC W F == some 64 then .carryF .sbb false x y (.immW 1 0)
      else n
  | .aluF op _ x y _ =>
      if (op == .and || op == .or || op == .xor) && x.swC W F == some 64 && y.swC W F == some 64
      then .immW 1 0 else n
  | .bin m x y =>
      if m = "ADD" then
        if x.swC W F == some 64 && y.swC W F == some 64 then addWC x y (.immW 1 0)
        else if y.swC W F == some 1 then
          match viewC K x with
          | .carryW .adcx a b c0 => if c0 == .immW 1 0 then addWC a b y else n
          | _ => n
        else n
      else if m = "SUB" then
        if x.swC W F == some 64 && y.swC W F == some 64 then .carryW .sbb x y (.immW 1 0)
        else if y.swC W F == some 1 then
          match viewC K x with
          | .carryW .sbb a b c0 => if c0 == .immW 1 0 then .carryW .sbb a b y else n
          | _ => n
        else n
      else n
  | _ => n

section NormSound

variable {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool} {σ : Nat → STerm}

theorem viewC_ev {K : Array STerm}
    (hK : ∀ j, ((K.getD j (.ref j)).subst σ).ev V A C O = (σ j).ev V A C O) (t : STerm) :
    ((viewC K t).subst σ).ev V A C O = (t.subst σ).ev V A C O := by
  cases t with
  | ref j => exact hK j
  | _ => rfl

theorem addWC_ev (x y c : STerm) :
    ((addWC x y c).subst σ).ev V A C O = ((STerm.carryW .adcx x y c).subst σ).ev V A C O := by
  unfold addWC
  split
  · simp only [STerm.subst, STerm.ev, carryWord_adcx_comm]
  · rfl

theorem addFC_ev (x y c : STerm) :
    ((addFC x y c).subst σ).ev V A C O =
      ((STerm.carryF .adcx false x y c).subst σ).ev V A C O := by
  unfold addFC
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [STerm.subst, STerm.ev, castW_mk, carryBit_adcx_eq]
    split <;> rfl
  · split
    · simp only [STerm.subst, STerm.ev, carryBit_adcx_comm]
    · rfl

/-- A word of a known width `w`, as a pair. -/
theorem ev_of_wid {t : STerm} {w : Nat} (h : (t.ev V A C O).1 = w) :
    t.ev V A C O = ⟨w, castW (t.ev V A C O) w⟩ := by
  generalize t.ev V A C O = p at h ⊢
  obtain ⟨w', v⟩ := p
  obtain rfl : w' = w := h
  simp

theorem bitOf_setWidth1 (p : Σ w, BitVec w) : (p.2.setWidth 1).getLsbD 0 = bitOf p := by
  simp [bitOf]

/-- **The normal form of a node evaluates as the node**, over a table whose keys `K`
    evaluate as their entries and whose widths `W` are widths of their entries. -/
theorem STerm.normC_ev {K : Array STerm} {W : Array (Option Nat)} {F : List (String × Nat)}
    (hK : ∀ j, ((K.getD j (.ref j)).subst σ).ev V A C O = (σ j).ev V A C O)
    (hW : ∀ k w, W.getD k none = some w → ((σ k).ev V A C O).1 = w)
    (hF : ∀ r w, factW F r = some w → (V r).1 = w) (n : STerm) :
    ((n.normC K W F).subst σ).ev V A C O = (n.subst σ).ev V A C O := by
  have w64 : ∀ t : STerm, (t.swC W F == some 64) = true → ((t.subst σ).ev V A C O).1 = 64 :=
    fun t h => STerm.swC_ev hW hF t 64 (by simpa using h)
  have w1 : ∀ t : STerm, (t.swC W F == some 1) = true → ((t.subst σ).ev V A C O).1 = 1 :=
    fun t h => STerm.swC_ev hW hF t 1 (by simpa using h)
  cases n with
  | carryW op x y c =>
      cases op
      · simp only [STerm.normC]; rw [addWC_ev]; simp only [STerm.subst, STerm.ev, carryWord_adc]
      · rfl
      · simp only [STerm.normC]; rw [addWC_ev]
      · simp only [STerm.normC]; rw [addWC_ev]; rfl
  | carryF op ofl x y c =>
      cases op <;> cases ofl
      · simp only [STerm.normC]; rw [addFC_ev]; simp only [STerm.subst, STerm.ev, carryBit_adc]
      · rfl
      · rfl
      · rfl
      · simp only [STerm.normC]; rw [addFC_ev]
      · simp only [STerm.normC]; rw [addFC_ev]; rfl
      · simp only [STerm.normC]; rw [addFC_ev]; rfl
      · simp only [STerm.normC]; rw [addFC_ev]; rfl
  | cout sub x y c =>
      cases sub
      · simp only [STerm.normC]
        split
        · rename_i h
          simp only [Bool.and_eq_true] at h
          rw [addFC_ev]
          simp only [STerm.subst, STerm.ev, coutBit]
          rw [ev_of_wid (w64 x h.1), ev_of_wid (w64 y h.2)]
          simp only [castW_mk, extW, BitVec.setWidth_eq, carryOutBit_eq, bitOf_setWidth1,
            Bool.false_eq_true, ↓reduceIte]
        · rfl
      · simp only [STerm.normC]
        split
        · rename_i h
          simp only [Bool.and_eq_true] at h
          simp only [STerm.subst, STerm.ev, coutBit]
          rw [ev_of_wid (w64 x h.1), ev_of_wid (w64 y h.2)]
          simp only [castW_mk, extW, BitVec.setWidth_eq, borrowOutBit_eq, bitOf_setWidth1,
            ↓reduceIte]
        · rfl
  | aluF op ofl x y o =>
      have hl : ∀ {op : AluOp}, (op = .and ∨ op = .or ∨ op = .xor) → ∀ ofl : Bool,
          (x.swC W F == some 64 && y.swC W F == some 64) = true →
          ((STerm.immW 1 0).subst σ).ev V A C O =
            ((STerm.aluF op ofl x y o).subst σ).ev V A C O := by
        intro op hop ofl h
        simp only [Bool.and_eq_true] at h
        simp only [STerm.subst, STerm.ev, w64 x h.1, w64 y h.2, and_self, ↓reduceIte,
          aluBit_logic hop]
        rfl
      cases op <;> cases ofl <;> simp only [STerm.normC]
      · split
        · rename_i h
          simp only [Bool.and_eq_true] at h
          rw [addFC_ev]
          simp only [STerm.subst, STerm.ev, w64 x h.1, w64 y h.2, and_self, ↓reduceIte,
            aluBit_add]
          rfl
        · rfl
      · rfl
      · split
        · rename_i h
          simp only [Bool.and_eq_true] at h
          simp only [STerm.subst, STerm.ev, w64 x h.1, w64 y h.2, and_self, ↓reduceIte,
            aluBit_sub]
          rfl
        · rfl
      · rfl
      all_goals
        split
        · rename_i h
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, reduceCtorEq,
            false_or, or_false, true_and] at h
          exact hl (by simp) _ (by simpa using h)
        · rfl
  | bin m x y =>
      simp only [STerm.normC]
      by_cases hA : m = "ADD"
      · subst hA
        simp only [↓reduceIte]
        split
        · rename_i h
          simp only [Bool.and_eq_true] at h
          rw [addWC_ev]
          simp only [STerm.subst, STerm.ev]
          rw [ev_of_wid (w64 x h.1), ev_of_wid (w64 y h.2)]
          simp [extW, binW_add, bitOf]
        · split
          · rename_i h1
            split
            · rename_i a b c0 hv
              split
              · rename_i hc
                simp only [beq_iff_eq] at hc
                subst hc
                rw [addWC_ev]
                have hx := viewC_ev hK x
                rw [hv] at hx
                simp only [STerm.subst, STerm.ev] at hx ⊢
                rw [← hx, ev_of_wid (w1 y h1)]
                simp [extW, binW_add_carry, bitOf]
              · rfl
            · rfl
          · rfl
      · simp only [hA, ↓reduceIte]
        by_cases hS : m = "SUB"
        · subst hS
          simp only [↓reduceIte]
          split
          · rename_i h
            simp only [Bool.and_eq_true] at h
            simp only [STerm.subst, STerm.ev]
            rw [ev_of_wid (w64 x h.1), ev_of_wid (w64 y h.2)]
            simp [extW, binW_sub, bitOf]
          · split
            · rename_i h1
              split
              · rename_i a b c0 hv
                split
                · rename_i hc
                  simp only [beq_iff_eq] at hc
                  subst hc
                  have hx := viewC_ev hK x
                  rw [hv] at hx
                  simp only [STerm.subst, STerm.ev] at hx ⊢
                  rw [← hx, ev_of_wid (w1 y h1)]
                  simp [extW, binW_sub_borrow, bitOf]
                · rfl
              · rfl
            · rfl
        · simp only [hS, ↓reduceIte]
  | _ => rfl

end NormSound

/-! ### Canonical keys of a term table -/

/-- The canonical keys of the first entries of a term table: for each entry its canonical
    form (`rep`: a leaf, or a reference to the first entry with its key), its key (`key`: the
    normal form `normC` of its node over the canonical forms of its children) and the width
    its key fixes (`wid`), with an index from keys to entries (`idx`, a hint checked against
    `key`). -/
structure CanonT where
  /-- The canonical form of each entry. -/
  rep : Array STerm
  /-- The key of each entry. -/
  key : Array STerm
  /-- The width the key of each entry fixes. -/
  wid : Array (Option Nat)
  /-- The first entry of each key. -/
  idx : Std.HashMap STerm Nat

/-- The canonical keys of no entry. -/
def CanonT.empty : CanonT := ⟨#[], #[], #[], {}⟩

/-- The word `t` with each reference replaced by the canonical form of its entry. -/
def CanonT.form (Cn : CanonT) (t : STerm) : STerm := t.subst (fun j => Cn.rep.getD j (.ref j))

/-- A leaf word or a reference. -/
def STerm.isLeafC : STerm → Bool
  | .reg _ | .immW _ _ | .cin _ | .ref _ => true
  | _ => false

/-- The canonical keys with the entry of node `n` appended at the index `Cn.rep.size`. -/
def CanonT.push (F : List (String × Nat)) (Cn : CanonT) (n : STerm) : CanonT :=
  let r := (Cn.form n).normC Cn.key Cn.wid F
  let w := r.swC Cn.wid F
  if r.isLeafC then
    { Cn with rep := Cn.rep.push r, key := Cn.key.push (viewC Cn.key r), wid := Cn.wid.push w }
  else
    match Cn.idx[r]? with
    | some j =>
        if Cn.key[j]? == some r then
          { Cn with rep := Cn.rep.push (.ref j), key := Cn.key.push r, wid := Cn.wid.push w }
        else
          { rep := Cn.rep.push (.ref Cn.rep.size), key := Cn.key.push r, wid := Cn.wid.push w,
            idx := Cn.idx.insert r Cn.rep.size }
    | none =>
        { rep := Cn.rep.push (.ref Cn.rep.size), key := Cn.key.push r, wid := Cn.wid.push w,
          idx := Cn.idx.insert r Cn.rep.size }

/-- The canonical keys of the term table `E`, with the facts `F`. -/
def CanonT.build (F : List (String × Nat)) (E : Array TEnt) : CanonT :=
  E.foldl (fun Cn e => Cn.push F e.node) CanonT.empty

/-- Two words over the table `E` have one canonical form, with the facts `F`. -/
def canonEqT (F : List (String × Nat)) (E : Array TEnt) (t t' : STerm) : Bool :=
  (CanonT.build F E).form t == (CanonT.build F E).form t'

section CanonSound

variable {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool} {σ : Nat → STerm}

/-- The canonical keys describe the substitution `σ` at one evaluation: the canonical forms
    and the keys evaluate as the entries, and the widths are their widths. -/
def CanonT.OK (σ : Nat → STerm) (V : String → Σ w, BitVec w) (A : String → ArrCell)
    (C O : Bool) (Cn : CanonT) : Prop :=
  Cn.key.size = Cn.rep.size ∧ Cn.wid.size = Cn.rep.size ∧
    (∀ j, ((Cn.rep.getD j (.ref j)).subst σ).ev V A C O = (σ j).ev V A C O) ∧
    (∀ j, ((Cn.key.getD j (.ref j)).subst σ).ev V A C O = (σ j).ev V A C O) ∧
    (∀ j w, Cn.wid.getD j none = some w → ((σ j).ev V A C O).1 = w)

theorem CanonT.ok_empty : CanonT.empty.OK σ V A C O :=
  ⟨rfl, rfl, fun _ => by simp [CanonT.empty, STerm.subst], fun _ => by
    simp [CanonT.empty, STerm.subst], fun _ _ h => by simp [CanonT.empty] at h⟩

theorem CanonT.form_ev {Cn : CanonT} (h : Cn.OK σ V A C O) (t : STerm) :
    ((Cn.form t).subst σ).ev V A C O = (t.subst σ).ev V A C O := by
  unfold CanonT.form
  rw [STerm.subst_subst]
  exact STerm.ev_subst_congr h.2.2.1 t

theorem getD_push_eq {α : Type} (xs : Array α) (x d : α) (j : Nat) :
    (xs.push x).getD j d = if j = xs.size then x else xs.getD j d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> rfl

theorem CanonT.ok_push {F : List (String × Nat)} (hF : ∀ r w, factW F r = some w → (V r).1 = w)
    {Cn : CanonT} (h : Cn.OK σ V A C O) (n : STerm)
    (hn : (n.subst σ).ev V A C O = (σ Cn.rep.size).ev V A C O) :
    (Cn.push F n).OK σ V A C O ∧ (Cn.push F n).rep.size = Cn.rep.size + 1 := by
  obtain ⟨hk, hw, hr, hkey, hwid⟩ := h
  have hR : (((Cn.form n).normC Cn.key Cn.wid F).subst σ).ev V A C O =
      (σ Cn.rep.size).ev V A C O := by
    rw [STerm.normC_ev hkey hwid hF, CanonT.form_ev ⟨hk, hw, hr, hkey, hwid⟩, hn]
  have hW : ∀ w, ((Cn.form n).normC Cn.key Cn.wid F).swC Cn.wid F = some w →
      ((σ Cn.rep.size).ev V A C O).1 = w := fun w hw' => by
    rw [← hR]; exact STerm.swC_ev hwid hF _ w hw'
  -- the three arrays receive their new element at one index
  have mk : ∀ (x y : STerm) (z : Option Nat) (I : Std.HashMap STerm Nat),
      (x.subst σ).ev V A C O = (σ Cn.rep.size).ev V A C O →
      (y.subst σ).ev V A C O = (σ Cn.rep.size).ev V A C O →
      (∀ w, z = some w → ((σ Cn.rep.size).ev V A C O).1 = w) →
      (CanonT.mk (Cn.rep.push x) (Cn.key.push y) (Cn.wid.push z) I).OK σ V A C O ∧
        (CanonT.mk (Cn.rep.push x) (Cn.key.push y) (Cn.wid.push z) I).rep.size =
          Cn.rep.size + 1 := by
    intro x y z I ex ey ez
    refine ⟨⟨by simp [hk], by simp [hw], fun j => ?_, fun j => ?_, fun j w hj => ?_⟩,
      by simp⟩
    · simp only [getD_push_eq]
      split
      · subst_vars; exact ex
      · exact hr j
    · simp only [getD_push_eq, hk]
      split
      · subst_vars; exact ey
      · exact hkey j
    · simp only [getD_push_eq, hw] at hj
      by_cases hjk : j = Cn.rep.size
      · subst hjk
        simp only [↓reduceIte] at hj
        exact ez w hj
      · simp only [hjk, ↓reduceIte] at hj
        exact hwid j w hj
  unfold CanonT.push
  dsimp only
  generalize (Cn.form n).normC Cn.key Cn.wid F = r at hR hW ⊢
  split
  · exact mk _ _ _ _ hR (by rw [viewC_ev hkey, hR]) hW
  · split
    · rename_i j _
      split
      · rename_i hj
        have hkj : Cn.key.getD j (.ref j) = r := by
          simp only [beq_iff_eq] at hj
          simp [Array.getD_eq_getD_getElem?, hj]
        refine mk _ _ _ _ ?_ hR hW
        rw [← hR, ← hkj, hkey j]
        rfl
      · exact mk _ _ _ _ (by rw [STerm.subst]) hR hW
    · exact mk _ _ _ _ (by rw [STerm.subst]) hR hW

/-- **The canonical keys of a valid term table describe it.** -/
theorem CanonT.ok_build {F : List (String × Nat)}
    (hF : ∀ r w, factW F r = some w → (V r).1 = w) {E : Array TEnt} (hE : TblOK σ E) :
    (CanonT.build F E).OK σ V A C O := by
  unfold CanonT.build
  have := Array.foldl_induction (as := E)
    (fun i (Cn : CanonT) => Cn.OK σ V A C O ∧ Cn.rep.size = i) (init := CanonT.empty)
    ⟨CanonT.ok_empty, rfl⟩ (f := fun Cn e => Cn.push F e.node) (fun i Cn ⟨hok, hs⟩ => by
      obtain ⟨h1, h2⟩ := CanonT.ok_push hF hok E[i].node (by
        rw [hs, (hE i i.isLt).1]
        rfl)
      exact ⟨h1, by rw [h2, hs]⟩)
  exact this.1

/-- **Words with one canonical form evaluate alike.** -/
theorem canonEqT_ev {F : List (String × Nat)} {E : Array TEnt} (hE : TblOK σ E) {t t' : STerm}
    (h : canonEqT F E t t' = true) (V : String → Σ w, BitVec w) (A : String → ArrCell)
    (C O : Bool) (hF : ∀ r w, factW F r = some w → (V r).1 = w) :
    (t.subst σ).ev V A C O = (t'.subst σ).ev V A C O := by
  simp only [canonEqT, beq_iff_eq] at h
  rw [← CanonT.form_ev (CanonT.ok_build hF hE) t, h, CanonT.form_ev (CanonT.ok_build hF hE) t']

end CanonSound

/-! ### Facts and guards implied by widths -/

/-- The widths that the guards `gs` state of start registers. -/
def guardFacts (gs : List SG) : List (String × Nat) :=
  gs.filterMap fun g => match g with
    | .wid (.reg r) w => some (r, w)
    | _ => none

theorem guardFacts_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {σ : Nat → STerm} {gs : List SG} (h : AllG V A C O (gs.map (SG.subst σ))) :
    ∀ r w, factW (guardFacts gs) r = some w → (V r).1 = w := by
  intro r w hr
  simp only [factW, Option.map_eq_some_iff] at hr
  obtain ⟨⟨r', w'⟩, hf, rfl⟩ := hr
  have hmem := List.mem_of_find?_eq_some hf
  have hr' : r' = r := by simpa using List.find?_some hf
  subst hr'
  simp only [guardFacts, List.mem_filterMap] at hmem
  obtain ⟨g, hg, hgw⟩ := hmem
  rcases g with ⟨t, w0⟩ | _ | _ <;> try simp at hgw
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> simp at hgw
  obtain ⟨rfl, rfl⟩ := hgw
  have := h _ (List.mem_map.mpr ⟨_, hg, rfl⟩)
  simpa [SG.subst, STerm.subst, SG.holds, STerm.ev] using this

/-- A guard that the widths of the canonical keys `Cn` and the facts `F` decide to hold. -/
def SG.impT (Cn : CanonT) (F : List (String × Nat)) : SG → Bool
  | .wid t w => (Cn.form t).swC Cn.wid F == some w
  | .eqW x y =>
      match (Cn.form x).swC Cn.wid F, (Cn.form y).swC Cn.wid F with
      | some a, some b => a == b
      | _, _ => false
  | .shp _ _ _ => false

theorem SG.impT_holds {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {σ : Nat → STerm} {Cn : CanonT} {F : List (String × Nat)} (h : Cn.OK σ V A C O)
    (hF : ∀ r w, factW F r = some w → (V r).1 = w) {g : SG} (hg : g.impT Cn F = true) :
    (g.subst σ).holds V A C O := by
  have hw : ∀ (t : STerm) (w : Nat), (Cn.form t).swC Cn.wid F = some w →
      ((t.subst σ).ev V A C O).1 = w := fun t w ht => by
    rw [← CanonT.form_ev h t]; exact STerm.swC_ev h.2.2.2.2 hF _ w ht
  cases g with
  | wid t w =>
      simp only [SG.impT, beq_iff_eq] at hg
      exact hw t w hg
  | eqW x y =>
      simp only [SG.impT] at hg
      split at hg
      · rename_i a b ha hb
        simp only [beq_iff_eq] at hg
        subst hg
        simp only [SG.subst, SG.holds]
        rw [hw x a ha, hw y a hb]
      · cases hg
  | shp _ _ _ => simp [SG.impT] at hg

end Canon

/-! ## 15. The shared checker

`blockOkR` is `blockOk` over the term table: both bodies of a block pair run over one table
(`blockRuns`), so equal words are equal entries, and the registers and flags a value reads
come from the cached entries. `blockOkR_spec` shows that it implies `blockOk`. -/

/-- The start registers the flag `f` over the table `E` reads. -/
def SFlag.varsT (E : Array TEnt) : SFlag → List String
  | .init => []
  | .cmp x y => x.varsT E ++ y.varsT E

/-- The flag `f` over the table `E` reads a flag at the start. -/
def SFlag.readsInitT (E : Array TEnt) : SFlag → Bool
  | .init => true
  | .cmp x y => x.readsFT E || y.readsFT E

/-- The flag `f` reads only table entries below `n`. -/
def SFlag.refsLt (n : Nat) : SFlag → Bool
  | .init => true
  | .cmp x y => x.refsLt n && y.refsLt n

/-- The start registers the guard `g` over the table `E` reads. -/
def SG.varsT (E : Array TEnt) : SG → List String
  | .wid t _ => t.varsT E
  | .eqW x y => x.varsT E ++ y.varsT E
  | .shp a _ _ => a.varsT E

/-- The guard `g` over the table `E` reads a flag at the start. -/
def SG.readsFT (E : Array TEnt) : SG → Bool
  | .wid t _ => t.readsFT E
  | .eqW x y => x.readsFT E || y.readsFT E
  | .shp a _ _ => a.readsFT E

/-- The guard `g` reads only table entries below `n`. -/
def SG.refsLt (n : Nat) : SG → Bool
  | .wid t _ => t.refsLt n
  | .eqW x y => x.refsLt n && y.refsLt n
  | .shp a _ _ => a.refsLt n

/-- The start registers the branch condition `d` over the table `E` reads. -/
def SDec.varsT (E : Array TEnt) : SDec → List String
  | .flag _ z => z.varsT E
  | .nz t => t.varsT E
  | .const _ => []

/-- The branch condition `d` over the table `E` reads a flag at the start. -/
def SDec.readsInitT (E : Array TEnt) : SDec → Bool
  | .flag _ z => z.readsInitT E
  | .nz t => t.readsFT E
  | .const _ => false

/-- The branch condition `d` reads only table entries below `n`. -/
def SDec.refsLt (n : Nat) : SDec → Bool
  | .flag _ z => z.refsLt n
  | .nz t => t.refsLt n
  | .const _ => true

/-- The word `t` over the table `E` may be compared at a block with live set `n`. -/
def okInT (E : Array TEnt) (n : List String × Bool) (t : STerm) : Bool :=
  t.refsLt E.size && okIn n (t.varsT E) (t.readsFT E)

/-- The array `a` over the table `E` may be compared at a block with live set `n`. -/
def okInAT (E : Array TEnt) (n : List String × Bool) (a : SArr) : Bool :=
  a.refsLt E.size && okIn n (a.varsT E) (a.readsFT E)

/-- The flag `f` over the table `E` may be compared at a block with live set `n`. -/
def okInFT (E : Array TEnt) (n : List String × Bool) (f : SFlag) : Bool :=
  f.refsLt E.size && okIn n (f.varsT E) (f.readsInitT E)

/-- The guard `g` over the table `E` may be compared at a block with live set `n`. -/
def okInGT (E : Array TEnt) (n : List String × Bool) (g : SG) : Bool :=
  g.refsLt E.size && okIn n (g.varsT E) (g.readsFT E)

/-- The branch condition `d` over the table `E` may be compared at a block with live
    set `n`. -/
def okInDT (E : Array TEnt) (n : List String × Bool) (d : SDec) : Bool :=
  d.refsLt E.size && okIn n (d.varsT E) (d.readsInitT E)

theorem okIn_of {n : List String × Bool} {vs vs' : List String} {rf rf' : Bool}
    (hv : ∀ v ∈ vs, v ∈ vs') (hr : rf = true → rf' = true) (h : okIn n vs' rf' = true) :
    okIn n vs rf = true := by
  obtain ⟨h1, h2⟩ := okIn_spec h
  simp only [okIn, vIn, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨fun v hv' => h1 v (hv v hv'), ?_⟩
  cases rf
  · exact Or.inl rfl
  · exact Or.inr (h2 (hr rfl))

section Shared

variable {σ : Nat → STerm} {E : Array TEnt}

theorem okInT_spec (h : TblOK σ E) {n : List String × Bool} {t : STerm}
    (ht : okInT E n t = true) : okIn n (t.subst σ).vars (t.subst σ).readsF = true := by
  simp only [okInT, Bool.and_eq_true] at ht
  exact okIn_of (STerm.varsT_spec h t ht.1) (STerm.readsFT_spec h t ht.1) ht.2

theorem okInAT_spec (h : TblOK σ E) {n : List String × Bool} {a : SArr}
    (ha : okInAT E n a = true) : okIn n (a.subst σ).vars (a.subst σ).readsF = true := by
  simp only [okInAT, Bool.and_eq_true] at ha
  exact okIn_of (SArr.varsT_spec h a ha.1) (SArr.readsFT_spec h a ha.1) ha.2

theorem okInFT_spec (h : TblOK σ E) {n : List String × Bool} {f : SFlag}
    (hf : okInFT E n f = true) : okIn n (f.subst σ).vars (f.subst σ).readsInit = true := by
  simp only [okInFT, Bool.and_eq_true] at hf
  cases f with
  | init => exact hf.2
  | cmp x y =>
      simp only [SFlag.refsLt, Bool.and_eq_true] at hf
      refine okIn_of (vs' := SFlag.varsT E (.cmp x y)) (rf' := SFlag.readsInitT E (.cmp x y))
        (fun v hv => ?_) (fun hr => ?_) hf.2
      · simp only [SFlag.subst, SFlag.vars, List.mem_append] at hv
        simp only [SFlag.varsT, List.mem_append]
        exact hv.imp (STerm.varsT_spec h x hf.1.1 v) (STerm.varsT_spec h y hf.1.2 v)
      · simp only [SFlag.subst, SFlag.readsInit, Bool.or_eq_true] at hr
        simp only [SFlag.readsInitT, Bool.or_eq_true]
        exact hr.imp (STerm.readsFT_spec h x hf.1.1) (STerm.readsFT_spec h y hf.1.2)

theorem okInGT_spec (h : TblOK σ E) {n : List String × Bool} {g : SG}
    (hg : okInGT E n g = true) : okIn n (g.subst σ).vars (g.subst σ).readsF = true := by
  simp only [okInGT, Bool.and_eq_true] at hg
  cases g with
  | wid t w => exact okIn_of (STerm.varsT_spec h t hg.1) (STerm.readsFT_spec h t hg.1) hg.2
  | eqW x y =>
      simp only [SG.refsLt, Bool.and_eq_true] at hg
      refine okIn_of (vs' := SG.varsT E (.eqW x y)) (rf' := SG.readsFT E (.eqW x y))
        (fun v hv => ?_) (fun hr => ?_) hg.2
      · simp only [SG.subst, SG.vars, List.mem_append] at hv
        simp only [SG.varsT, List.mem_append]
        exact hv.imp (STerm.varsT_spec h x hg.1.1 v) (STerm.varsT_spec h y hg.1.2 v)
      · simp only [SG.subst, SG.readsF, Bool.or_eq_true] at hr
        simp only [SG.readsFT, Bool.or_eq_true]
        exact hr.imp (STerm.readsFT_spec h x hg.1.1) (STerm.readsFT_spec h y hg.1.2)
  | shp a w m => exact okIn_of (SArr.varsT_spec h a hg.1) (SArr.readsFT_spec h a hg.1) hg.2

theorem okInDT_spec (h : TblOK σ E) {n : List String × Bool} {d : SDec}
    (hd : okInDT E n d = true) : okIn n (d.subst σ).vars (d.subst σ).readsInit = true := by
  simp only [okInDT, Bool.and_eq_true] at hd
  cases d with
  | flag pol z =>
      have := okInFT_spec h (n := n) (f := z) (by simp only [okInFT, Bool.and_eq_true]; exact hd)
      simpa [SDec.subst, SDec.vars, SDec.readsInit] using this
  | nz t =>
      exact okIn_of (STerm.varsT_spec h t hd.1) (STerm.readsFT_spec h t hd.1) hd.2
  | const b => exact hd.2

end Shared

/-- The normal form of a guard over the table `E` (`SG.norm`). -/
def SG.normT (E : Array TEnt) : SG → List SG
  | .wid t w =>
      match t.wbkT E with
      | some v => if v = w then [] else [SG.falseG]
      | none => [.wid (t.wbT E) w]
  | .eqW x y =>
      match x.wbkT E, y.wbkT E with
      | some a, some b => if a = b then [] else [SG.falseG]
      | _, _ => [.eqW (x.wbT E) (y.wbT E)]
  | .shp a w n => [.shp a w n]

/-- The normal form of a list of guards over the table `E` (`normG`). -/
def normGT (E : Array TEnt) (gs : List SG) : List SG := gs.flatMap (SG.normT E)

theorem SG.normT_subst {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E) (g : SG)
    (hg : g.refsLt E.size = true) : (g.normT E).map (SG.subst σ) = (g.subst σ).norm := by
  cases g with
  | wid t w =>
      obtain ⟨w1, w2⟩ := STerm.wbT_spec h t hg
      simp only [SG.normT, SG.subst, SG.norm]
      rw [w2, w1]
      cases t.wbkT E with
      | some v => by_cases hv : v = w <;> simp [hv, SG.falseG, SG.subst, STerm.subst]
      | none => rfl
  | eqW x y =>
      simp only [SG.refsLt, Bool.and_eq_true] at hg
      obtain ⟨x1, x2⟩ := STerm.wbT_spec h x hg.1
      obtain ⟨y1, y2⟩ := STerm.wbT_spec h y hg.2
      simp only [SG.normT, SG.subst, SG.norm]
      rw [x2, y2, x1, y1]
      cases x.wbkT E with
      | none => cases y.wbkT E <;> rfl
      | some a =>
          cases y.wbkT E with
          | none => rfl
          | some b => by_cases hab : a = b <;> simp [hab, SG.falseG, SG.subst, STerm.subst]
  | shp a w n => rfl

theorem normGT_subst {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E) :
    ∀ gs : List SG, gs.all (SG.refsLt E.size) = true →
      (normGT E gs).map (SG.subst σ) = normG (gs.map (SG.subst σ))
  | [], _ => rfl
  | g :: gs, hb => by
      simp only [List.all_cons, Bool.and_eq_true] at hb
      have ih := normGT_subst h gs hb.2
      simp only [normGT, normG] at ih ⊢
      rw [List.flatMap_cons, List.map_append, ih, SG.normT_subst h g hb.1]
      rfl

theorem symDec_subst (σ : Nat → STerm) (ss : SSt) (c : LOperand) :
    symDec (ss.subst σ) c = (symDec ss c).subst σ := by
  unfold symDec
  split
  · rfl
  · split <;> simp [SDec.subst]

/-- The start registers that the guard `g` over the table `E` reads are read by guards of
    `gs`. -/
def guardVarsIn (E : Array TEnt) (gs : List SG) (g : SG) : Bool :=
  (g.varsT E).all fun v => gs.any fun g0 => (g0.varsT E).contains v

/-- The guard check of `blockOk` over the table `E`: every guard of the normal form of the
    rewritten block's guards `gs'` is one of the source block's, or the widths of the canonical
    keys of `E` under the facts of the source block's guards `gs` decide it (`SG.impT`) and
    the start registers it reads are read by guards of the source block (`guardVarsIn`). -/
def guardsT (E : Array TEnt) (n : List String × Bool) (gs gs' : List SG) : Bool :=
  (gs ++ gs').all (SG.refsLt E.size) &&
    (normGT E gs').all (fun g =>
      ((normGT E gs).contains g ||
        (guardVarsIn E (normGT E gs) g &&
          g.impT (CanonT.build (guardFacts (normGT E gs)) E) (guardFacts (normGT E gs)))) &&
      okInGT E n g)

theorem guardsT_spec {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E)
    {n : List String × Bool} {gs gs' : List SG} (hg : guardsT E n gs gs' = true) :
    (normG (gs'.map (SG.subst σ))).all (fun g =>
      ((normG (gs.map (SG.subst σ))).contains g || SG.impG (gs.map (SG.subst σ)) g) &&
        okIn n g.vars g.readsF) = true := by
  simp only [guardsT, Bool.and_eq_true, List.all_append] at hg
  obtain ⟨⟨hb, hb'⟩, hc⟩ := hg
  rw [← normGT_subst h gs' hb']
  simp only [List.all_eq_true, List.mem_map, Bool.and_eq_true, Bool.or_eq_true,
    List.contains_iff_mem] at hc ⊢
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨?_, okInGT_spec h (hc g hg).2⟩
  rcases (hc g hg).1 with hm | hi
  · left
    rw [← normGT_subst h gs hb]
    exact List.mem_map.mpr ⟨g, hm, rfl⟩
  · right
    refine SG.impG_of fun V A C O hA => ?_
    have hN : AllG V A C O ((normGT E gs).map (SG.subst σ)) := by
      rw [normGT_subst h gs hb]; exact allG_normG.mpr hA
    exact SG.impT_holds (CanonT.ok_build (guardFacts_sound hN) h) (guardFacts_sound hN) hi.2

/-- The substitution laws of a symbolic step `sym` and a symbolic branch condition `dec`: both
    commute with every substitution of table entries. The check over the term table implies
    the check from these laws. -/
structure SymSubst (sym : LinstrRM → SSt → SOut) (dec : SSt → LOperand → SDec) : Prop where
  /-- The symbolic step commutes with substitution. -/
  step_subst : ∀ (σ : Nat → STerm) (i : LinstrRM) (ss : SSt),
    sym i (ss.subst σ) = (sym i ss).subst σ
  /-- The symbolic branch condition commutes with substitution. -/
  dec_subst : ∀ (σ : Nat → STerm) (ss : SSt) (c : LOperand),
    dec (ss.subst σ) c = (dec ss c).subst σ

/-- The x86 symbolic step and branch condition commute with substitution. -/
theorem symSubst_x86 : SymSubst symStep symDec := ⟨symStep_subst, symDec_subst⟩

/-- The terminator check of `blockOk` over the table `E` (`termAgree`). -/
def termAgreeT (E : Array TEnt) (T : Term) (n : List String × Bool) (ss ss' : SSt) :
    Option LinstrRM → Option LinstrRM → optParam (SSt → LOperand → SDec) symDec → Bool
  | some (.Lgoto (a, _), _), some (.Lgoto (b, _), _), _ =>
      match T with
      | .goto _ => a == b
      | _ => false
  | some (.Lcond c _, _), some (.Lcond c' _, _), dec =>
      match T with
      | .cond _ _ => dec ss c == dec ss' c' && okInDT E n (dec ss c)
      | _ => false
  | _, _, _ =>
      match T with
      | .fall _ => true
      | _ => false

theorem termAgreeT_spec_at {dec : SSt → LOperand → SDec}
    (hd : ∀ (σ : Nat → STerm) (ss : SSt) (c : LOperand),
      dec (ss.subst σ) c = (dec ss c).subst σ)
    {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E) {T : Term}
    {n : List String × Bool} {ss ss' : SSt} {x y : Option LinstrRM}
    (ht : termAgreeT E T n ss ss' x y dec = true) :
    termAgree T n (ss.subst σ) (ss'.subst σ) x y dec = true := by
  unfold termAgreeT at ht
  unfold termAgree
  split at ht
  · exact ht
  · rename_i c _ _ c' _ _ dec'
    split at ht
    · simp only [Bool.and_eq_true, beq_iff_eq] at ht
      have hd' := okInDT_spec h ht.2
      simp only [okIn, Bool.and_eq_true] at hd'
      simp only [hd, ht.1, Bool.and_eq_true, beq_self_eq_true, true_and]
      rw [← ht.1]
      exact hd'
    · cases ht
  · exact ht

theorem termAgreeT_spec {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E) {T : Term}
    {n : List String × Bool} {ss ss' : SSt} {x y : Option LinstrRM}
    (ht : termAgreeT E T n ss ss' x y = true) :
    termAgree T n (ss.subst σ) (ss'.subst σ) x y = true :=
  termAgreeT_spec_at symDec_subst h ht

/-- `SArr.selfSt` over the table `E`: the word stored is the element read, or an entry of `E`
    whose node is the element read. -/
def SArr.selfStT (E : Array TEnt) (gs : List SG) (b : SArr) (w n : Nat) (i v : STerm) :
    Bool :=
  (v == .aget b w n i ||
      (match v with
        | .ref k =>
            match E[k]?.map TEnt.node with
            | some (.aget b0 w0 n0 i0) => w0 == w && n0 == n && i0 == i && b0 == b
            | _ => false
        | _ => false)) &&
    gs.contains (.shp b w n)

/-- The symbolic array `a` over the table `E` without its stores of the element read
    (`SArr.selfStT`, under the guards `gs`). -/
def SArr.nfT (E : Array TEnt) (gs : List SG) : SArr → SArr
  | .cell r => .cell r
  | .aset b w n i v =>
      if SArr.selfStT E gs b w n i v then SArr.nfT E gs b
      else .aset (SArr.nfT E gs b) w n i v
  | .zero w n => .zero w n

theorem SArr.selfStT_subst {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E)
    {gs : List SG} {b : SArr} {w n : Nat} {i v : STerm}
    (hs : SArr.selfStT E gs b w n i v = true) :
    SArr.selfSt (gs.map (SG.subst σ)) (b.subst σ) w n (i.subst σ) (v.subst σ) = true := by
  simp only [SArr.selfStT, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem] at hs
  obtain ⟨hv, hm⟩ := hs
  simp only [SArr.selfSt, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem]
  refine ⟨?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  rcases hv with rfl | hv
  · rfl
  · split at hv
    · rename_i k
      split at hv
      · rename_i b0 w0 n0 i0 he
        simp only [Bool.and_eq_true, beq_iff_eq] at hv
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hv
        obtain ⟨e, he'⟩ := Option.map_eq_some_iff.mp he
        have := (h.entry he'.1).1
        rw [STerm.subst, this, he'.2, STerm.subst]
      · cases hv
    · cases hv

/-- **Arrays with one normal form over the table are equal up to stores of the element
    read**, under every substitution that agrees with the table. -/
theorem SArr.nfT_same {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E) (gs gs' : List SG) :
    ∀ a a' : SArr, SArr.nfT E gs a = SArr.nfT E gs' a' →
      SArr.same (gs.map (SG.subst σ)) (gs'.map (SG.subst σ)) (a.subst σ) (a'.subst σ) = true
  | .cell r, .cell r', e => by
      simp only [SArr.nfT, SArr.cell.injEq] at e
      simp [SArr.subst, SArr.same, e]
  | .cell r, .aset b' w' n' i' v', e => by
      rw [SArr.nfT] at e
      rw [SArr.nfT] at e
      split at e
      · rename_i hs
        have ih := SArr.nfT_same h gs gs' (.cell r) b' (by rw [SArr.nfT]; exact e)
        rw [SArr.subst] at ih ⊢
        rw [SArr.subst, SArr.same, SArr.selfStT_subst h hs, ih]; rfl
      · cases e
  | .aset b w n i v, .cell r', e => by
      rw [SArr.nfT] at e
      rw [SArr.nfT] at e
      split at e
      · rename_i hs
        have ih := SArr.nfT_same h gs gs' b (.cell r') (by rw [SArr.nfT]; exact e)
        rw [SArr.subst] at ih ⊢
        rw [SArr.subst, SArr.same, SArr.selfStT_subst h hs, ih]; rfl
      · cases e
  | .aset b w n i v, .aset b' w' n' i' v', e => by
      rw [SArr.subst, SArr.subst, SArr.same]
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      by_cases hs : SArr.selfStT E gs b w n i v = true
      · have e1 : SArr.nfT E gs b = SArr.nfT E gs' (.aset b' w' n' i' v') := by
          rw [← e, SArr.nfT, ite_eq_left hs]
        have ih := SArr.nfT_same h gs gs' b _ e1
        rw [SArr.subst] at ih
        exact Or.inl (Or.inl ⟨SArr.selfStT_subst h hs, ih⟩)
      · by_cases hs' : SArr.selfStT E gs' b' w' n' i' v' = true
        · have e1 : SArr.nfT E gs (.aset b w n i v) = SArr.nfT E gs' b' := by
            rw [e, SArr.nfT, ite_eq_left hs']
          have ih := SArr.nfT_same h gs gs' _ b' e1
          rw [SArr.subst] at ih
          exact Or.inl (Or.inr ⟨SArr.selfStT_subst h hs', ih⟩)
        · rw [SArr.nfT, SArr.nfT, ite_eq_right hs, ite_eq_right hs'] at e
          simp only [SArr.aset.injEq] at e
          obtain ⟨eb, rfl, rfl, rfl, rfl⟩ := e
          exact Or.inr ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, SArr.nfT_same h gs gs' b b' eb⟩
  | .zero w n, .zero w' n', e => by grind only [SArr.nfT, SArr.subst, SArr.same]
  | .zero w n, .aset b' w' n' i' v', e => by
      rw [SArr.nfT] at e
      rw [SArr.nfT] at e
      split at e
      · rename_i hs
        have ih := SArr.nfT_same h gs gs' (.zero w n) b' (by rw [SArr.nfT]; exact e)
        rw [SArr.subst] at ih ⊢
        rw [SArr.subst, SArr.same, SArr.selfStT_subst h hs, ih]; rfl
      · cases e
  | .aset b w n i v, .zero w' n', e => by
      rw [SArr.nfT] at e
      rw [SArr.nfT] at e
      split at e
      · rename_i hs
        have ih := SArr.nfT_same h gs gs' b (.zero w' n') (by rw [SArr.nfT]; exact e)
        rw [SArr.subst] at ih ⊢
        rw [SArr.subst, SArr.same, SArr.selfStT_subst h hs, ih]; rfl
      · cases e
  | .cell _, .zero _ _, e => by simp [SArr.nfT] at e
  | .zero _ _, .cell _, e => by simp [SArr.nfT] at e
termination_by a a' => sizeOf a + sizeOf a'

/-- The array check of `exitAgree` over the table `E` (`arrAgree`): the two arrays are one
    symbolic array, or they have one normal form `SArr.nfT`. -/
def arrAgreeT (E : Array TEnt) (n : List String × Bool) (gs gs' : List SG) (a a' : SArr) :
    Bool :=
  (a == a' && okInAT E n a) ||
    (SArr.nfT E gs a == SArr.nfT E gs' a' && okInAT E n a')

theorem arrAgreeT_spec {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E)
    {n : List String × Bool} {gs gs' : List SG} {a a' : SArr}
    (ha : arrAgreeT E n gs gs' a a' = true) :
    arrAgree n (gs.map (SG.subst σ)) (gs'.map (SG.subst σ)) (a.subst σ) (a'.subst σ) =
      true := by
  simp only [arrAgreeT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at ha
  simp only [arrAgree, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases ha with ⟨e, o⟩ | ⟨e, o⟩
  · exact Or.inl ⟨by rw [e], okInAT_spec h o⟩
  · exact Or.inr ⟨SArr.nfT_same h gs gs' a a' e, okInAT_spec h o⟩

/-- One symbolic array that passes `okInAT` passes the array check. -/
theorem arrAgreeT_of_eq {E : Array TEnt} {n : List String × Bool} {gs gs' : List SG}
    {a a' : SArr} (e : a = a') (o : okInAT E n a = true) :
    arrAgreeT E n gs gs' a a' = true := by
  simp only [arrAgreeT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact Or.inl ⟨e, o⟩

/-- The register agreement of `exitAgree` over the table `E` (`regAgree`): the two words are
    one word, or they have one canonical form under the facts of the source block's guards `gs`
    and `t'` may be compared at the block; and `t` may be compared at the block. -/
def regAgreeT (E : Array TEnt) (n : List String × Bool) (gs : List SG) (t t' : STerm) : Bool :=
  (t == t' || (gs.all (SG.refsLt E.size) && canonEqT (guardFacts (normGT E gs)) E t t' &&
    okInT E n t')) && okInT E n t

theorem regAgreeT_of_eq {E : Array TEnt} {n : List String × Bool} {gs : List SG}
    {t t' : STerm} (e : t = t') (o : okInT E n t = true) : regAgreeT E n gs t t' = true := by
  subst e
  simp [regAgreeT, o]

theorem regAgreeT_mono {E : Array TEnt} {n n' : List String × Bool} {gs : List SG}
    (hm : ∀ t, okInT E n t = true → okInT E n' t = true) {t t' : STerm}
    (h : regAgreeT E n gs t t' = true) : regAgreeT E n' gs t t' = true := by
  simp only [regAgreeT, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨h1 | ⟨⟨h2, h3⟩, h4⟩, h5⟩ := h
  · exact ⟨Or.inl h1, hm _ h5⟩
  · exact ⟨Or.inr ⟨⟨h2, h3⟩, hm _ h4⟩, hm _ h5⟩

theorem regAgreeT_spec {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E)
    {n : List String × Bool} {gs : List SG} {t t' : STerm}
    (ha : regAgreeT E n gs t t' = true) :
    regAgree n (gs.map (SG.subst σ)) (t.subst σ) (t'.subst σ) = true := by
  simp only [regAgreeT, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ha
  simp only [regAgree, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  obtain ⟨h1 | ⟨⟨hb, hc⟩, ho'⟩, ho⟩ := ha
  · exact ⟨Or.inl (by rw [h1]), okInT_spec h ho⟩
  · refine ⟨Or.inr ⟨STerm.semEqG_of fun V A C O hA => ?_, okInT_spec h ho'⟩,
      okInT_spec h ho⟩
    have hN : AllG V A C O ((normGT E gs).map (SG.subst σ)) := by
      rw [normGT_subst h gs hb]; exact allG_normG.mpr hA
    exact canonEqT_ev h hc V A C O (guardFacts_sound hN)

/-- The exit check of `blockOk` over the table `E` (`exitAgree`). -/
def exitAgreeT (E : Array TEnt) (outs : List String) (L : Nat → List String × Bool)
    (n : List String × Bool) (T : Term) (ss ss' : SSt) (gs gs' : List SG) : Bool :=
  T.succs.all (fun j =>
      (L j).1.all (fun r => regAgreeT E n gs (ss.regs r) (ss'.regs r)) &&
        (!(L j).2 || (ss.zf == ss'.zf && okInFT E n ss.zf &&
          ss.cf == ss'.cf && okInT E n ss.cf &&
          ss.of == ss'.of && okInT E n ss.of))) &&
    (!T.halts || outs.all (fun r => regAgreeT E n gs (ss.regs r) (ss'.regs r))) &&
    (ss.awr ++ ss'.awr).all (fun q => arrAgreeT E n gs gs' (ss.arrs q) (ss'.arrs q))

theorem exitAgreeT_spec {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E)
    {outs : List String} {L : Nat → List String × Bool} {n : List String × Bool} {T : Term}
    {ss ss' : SSt} {gs gs' : List SG} (he : exitAgreeT E outs L n T ss ss' gs gs' = true) :
    exitAgree outs L n T (ss.subst σ) (ss'.subst σ) (gs.map (SG.subst σ))
      (gs'.map (SG.subst σ)) = true := by
  simp only [exitAgreeT, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at he
  obtain ⟨⟨hs, hh⟩, ha⟩ := he
  simp only [exitAgree, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true']
  refine ⟨⟨fun j hj => ⟨fun r hr => ?_, ?_⟩, ?_⟩, fun q hq => ?_⟩
  · rw [SSt.subst_regs_apply, SSt.subst_regs_apply]
    exact regAgreeT_spec h ((hs j hj).1 r hr)
  · rcases (hs j hj).2 with h0 | ⟨⟨⟨⟨⟨z1, z2⟩, c1⟩, c2⟩, o1⟩, o2⟩
    · exact Or.inl h0
    · exact Or.inr ⟨⟨⟨⟨⟨by simp only [SSt.subst, z1], okInFT_spec h z2⟩,
        by simp only [SSt.subst, c1]⟩, okInT_spec h c2⟩, by simp only [SSt.subst, o1]⟩,
        okInT_spec h o2⟩
  · rcases hh with h0 | ho
    · exact Or.inl h0
    · refine Or.inr fun r hr => ?_
      rw [SSt.subst_regs_apply, SSt.subst_regs_apply]
      exact regAgreeT_spec h (ho r hr)
  · have hq' : q ∈ ss.awr ++ ss'.awr := hq
    exact arrAgreeT_spec h (ha q hq')

/-- The shared runs of block `b` of `B` and block `b'` of `B'` with terminator `T`: the
    final table and the two descriptions over it. -/
def blockRuns (B B' : List LinstrRM) (b b' : Block) (T : Term)
    (sym : LinstrRM → SSt → SOut := symStep) : Tbl × SOut × SOut :=
  let p := tRun (bodyAt B b T) SSt.start Tbl.empty sym
  let q := tRun (bodyAt B' b' T) SSt.start p.1 sym
  (q.1, p.2, q.2)

/-- The check of block `k` from its shared runs `R` (`blockOk`). -/
def blockOkR (outs : List String) (L : Nat → List String × Bool) (k : Nat) (T : Term)
    (R : Tbl × SOut × SOut) (B B' : List LinstrRM) (b b' : Block)
    (dec : SSt → LOperand → SDec := symDec) : Bool :=
  match T with
  | .ret => true
  | _ =>
      match R.2.1 with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          match R.2.2 with
          | .ok ss' gs' =>
              guardsT R.1.ents (L k) gs gs' &&
                termAgreeT R.1.ents T (L k) ss ss' B[b.stop - 1]? B'[b'.stop - 1]? dec &&
                exitAgreeT R.1.ents outs L (L k) T ss ss' gs gs'
          | _ => false

/-- **The shared check implies the check**, for every symbolic step and branch condition
    that commute with substitution. -/
theorem blockOkR_spec_at {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hS : SymSubst sym dec) {outs : List String} {L : Nat → List String × Bool} {k : Nat}
    {T : Term} {B B' : List LinstrRM} {b b' : Block}
    (h : blockOkR outs L k T (blockRuns B B' b b' T sym) B B' b b' dec = true) :
    blockOk outs L k T B B' b b' sym dec = true := by
  have hv : TValid (blockRuns B B' b b' T sym).1.ents :=
    tRun_valid_at sym _ _ _ (tRun_valid_at sym _ _ _ tValid_empty)
  obtain ⟨⟨σ, hσ⟩, -⟩ := hv
  have e1 : symRun (bodyAt B b T) SSt.start sym = (blockRuns B B' b b' T sym).2.1.subst σ := by
    rw [← SSt.subst_start σ, ← tRun_subst_at hS.step_subst hσ _ _ _ (tRun_ext_at sym _ _ _)]
    rfl
  have e2 : symRun (bodyAt B' b' T) SSt.start sym =
      (blockRuns B B' b b' T sym).2.2.subst σ := by
    rw [← SSt.subst_start σ, ← tRun_subst_at hS.step_subst hσ _ _ _ (TExt.refl _)]
    rfl
  unfold blockOkR at h
  unfold blockOk
  split
  · rfl
  · rename_i hT
    have h' : (match (blockRuns B B' b b' T sym).2.1 with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          match (blockRuns B B' b b' T sym).2.2 with
          | .ok ss' gs' =>
              guardsT (blockRuns B B' b b' T sym).1.ents (L k) gs gs' &&
                termAgreeT (blockRuns B B' b b' T sym).1.ents T (L k) ss ss' B[b.stop - 1]?
                  B'[b'.stop - 1]? dec &&
                exitAgreeT (blockRuns B B' b b' T sym).1.ents outs L (L k) T ss ss' gs gs'
          | _ => false) = true := by
      split at h
      · exact absurd rfl hT
      · exact h
    rw [e1, e2]
    revert h'
    generalize blockRuns B B' b b' T sym = R at hσ
    obtain ⟨Tb, o, o'⟩ := R
    intro h'
    cases o with
    | fail => rfl
    | unk => cases h'
    | ok ss gs =>
        cases o' with
        | ok ss' gs' =>
            simp only [Bool.and_eq_true] at h'
            obtain ⟨⟨hg, hta⟩, hex⟩ := h'
            simp only [SOut.subst, Bool.and_eq_true]
            exact ⟨⟨guardsT_spec hσ hg, termAgreeT_spec_at hS.dec_subst hσ hta⟩,
              exitAgreeT_spec hσ hex⟩
        | fail => cases h'
        | unk => cases h'

/-- **The shared check implies the check.** -/
theorem blockOkR_spec {outs : List String} {L : Nat → List String × Bool} {k : Nat}
    {T : Term} {B B' : List LinstrRM} {b b' : Block}
    (h : blockOkR outs L k T (blockRuns B B' b b' T) B B' b b' = true) :
    blockOk outs L k T B B' b b' = true :=
  blockOkR_spec_at symSubst_x86 h

/-! ## 16. Live sets -/

/-- The shared runs of the block pairs of `G` and `G'`. -/
def runsOf (B B' : List LinstrRM) (G G' : CFG) (sym : LinstrRM → SSt → SOut := symStep) :
    Array (Tbl × SOut × SOut) :=
  (Array.range G.blocks.size).map fun k =>
    blockRuns B B' (G.blk k) (G'.blk k) (G.blk k).term sym

/-- The checker for the live sets `L` over the shared runs `R` of the block pairs of `G` and
    `G'` (`ownedCheckWith`). -/
def ownedCheckWithR (outs : List String) (L : Nat → List String × Bool)
    (B B' : List LinstrRM) (G G' : CFG) (R : Array (Tbl × SOut × SOut))
    (dec : SSt → LOperand → SDec := symDec) : Bool :=
  !B.isEmpty && !B'.isEmpty && G.blocks.size == G'.blocks.size &&
    (List.range G.blocks.size).all (fun k =>
      (G.blk k).term == (G'.blk k).term &&
        match R[k]? with
        | some r => blockOkR outs L k (G.blk k).term r B B' (G.blk k) (G'.blk k) dec
        | none => false)

/-- The check over the shared runs implies the check for the live sets, for every symbolic
    step and branch condition that commute with substitution. -/
theorem ownedCheckWithR_spec_at {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hS : SymSubst sym dec) {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} {G G' : CFG} (hG : cfgOf (B.map Prod.fst) = some G)
    (hG' : cfgOf (B'.map Prod.fst) = some G')
    (h : ownedCheckWithR outs L B B' G G' (runsOf B B' G G' sym) dec = true) :
    ownedCheckWith outs L B B' sym dec = true := by
  unfold ownedCheckWith
  rw [hG, hG']
  simp only [ownedCheckWithR, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h ⊢
  obtain ⟨hne, hall⟩ := h
  refine ⟨hne, fun k hk => ?_⟩
  obtain ⟨ht, hb⟩ := hall k hk
  refine ⟨ht, ?_⟩
  have hR : (runsOf B B' G G' sym)[k]? =
      some (blockRuns B B' (G.blk k) (G'.blk k) (G.blk k).term sym) := by
    simp [runsOf, hk]
  rw [hR] at hb
  exact blockOkR_spec_at hS hb

theorem ownedCheckWithR_spec {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} {G G' : CFG} (hG : cfgOf (B.map Prod.fst) = some G)
    (hG' : cfgOf (B'.map Prod.fst) = some G')
    (h : ownedCheckWithR outs L B B' G G' (runsOf B B' G G') = true) :
    ownedCheckWith outs L B B' = true :=
  ownedCheckWithR_spec_at symSubst_x86 hG hG' h

/-- The start registers and flags block `k` needs live for the checks of `blockOkR` to pass,
    from its shared runs `R`, given the live sets `L` of its successors. The result is a
    candidate only: `ownedCheckWith` checks the live sets it is given. -/
def blockNeed (outs : List String) (L : Nat → List String × Bool) (T : Term)
    (R : Tbl × SOut × SOut) (B : List LinstrRM) (b : Block)
    (dec : SSt → LOperand → SDec := symDec) : List String × Bool :=
  match T with
  | .ret => ([], false)
  | _ =>
      let E := R.1.ents
      match R.2.1, R.2.2 with
      | .ok ss _, .ok ss' gs' =>
          let d : Option SDec :=
            match T, B[b.stop - 1]? with
            | .cond _ _, some (.Lcond c _, _) => some (dec ss c)
            | _, _ => none
          ((normGT E gs').flatMap (SG.varsT E) ++ (d.map (SDec.varsT E)).getD [] ++
              T.succs.flatMap (fun j => (L j).1.flatMap (fun r => (ss.regs r).varsT E) ++
                (if (L j).2 then ss.zf.varsT E ++ ss.cf.varsT E ++ ss.of.varsT E else [])) ++
              (if T.halts then outs.flatMap (fun r => (ss.regs r).varsT E) else []) ++
              (ss.awr ++ ss'.awr).flatMap (fun q => (ss.arrs q).varsT E),
            (d.map (SDec.readsInitT E)).getD false || (normGT E gs').any (SG.readsFT E) ||
              T.succs.any (fun j => (L j).1.any (fun r => (ss.regs r).readsFT E) ||
                ((L j).2 && (ss.zf.readsInitT E || ss.cf.readsFT E || ss.of.readsFT E))) ||
              (T.halts && outs.any (fun r => (ss.regs r).readsFT E)) ||
              (ss.awr ++ ss'.awr).any (fun q => (ss.arrs q).readsFT E))
      | _, _ => ([], false)

/-- `n` extended by the names and flag of `m`. -/
def joinLive (n m : List String × Bool) : List String × Bool :=
  (m.1.foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) n.1, n.2 || m.2)

/-- One round of the live-set iteration over the blocks of `G`, from their shared runs
    `R`. -/
def liveRound (outs : List String) (B : List LinstrRM) (G : CFG)
    (R : Array (Tbl × SOut × SOut)) (L : Array (List String × Bool))
    (dec : SSt → LOperand → SDec := symDec) :
    Array (List String × Bool) :=
  (Array.range G.blocks.size).map fun k =>
    joinLive (L.getD k ([], false))
      (match R[k]? with
        | some r =>
            blockNeed outs (fun j => L.getD j ([], false)) (G.blk k).term r B (G.blk k) dec
        | none => ([], false))

/-- The live-set iteration from the empty sets, stopped at a fixpoint or after `n`
    rounds. -/
def liveIter (outs : List String) (B : List LinstrRM) (G : CFG)
    (R : Array (Tbl × SOut × SOut)) :
    Nat → Array (List String × Bool) → optParam (SSt → LOperand → SDec) symDec →
      Array (List String × Bool)
  | 0, L, _ => L
  | n + 1, L, dec =>
      let L' := liveRound outs B G R L dec
      if L'.map (fun p => (p.1.length, p.2)) == L.map (fun p => (p.1.length, p.2)) then L
      else liveIter outs B G R n L' dec

/-- **The checker.** Each block pair runs once over a shared term table (`runsOf`); the live
    sets are computed by `liveIter` and the runs checked by `ownedCheckWithR`. The symbolic
    step `sym` and the symbolic branch condition `dec` default to the x86 ones, `symStep`
    and `symDec`. -/
def ownedCheckM (outs : List String) (B B' : List LinstrRM)
    (sym : LinstrRM → SSt → SOut := symStep) (dec : SSt → LOperand → SDec := symDec) : Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      let R := runsOf B B' G G' sym
      let L := liveIter outs B G R (4 * G.blocks.size + 64)
        (Array.replicate G.blocks.size ([], false)) dec
      ownedCheckWithR outs (fun k => L.getD k ([], false)) B B' G G' R dec
  | _, _ => false

/-- A pair `ownedCheckM` accepts under `sym` and `dec` is accepted by `ownedCheckWith` for
    some live sets, when `sym` and `dec` commute with substitution. -/
theorem ownedCheckM_with_at {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hS : SymSubst sym dec) {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckM outs B B' sym dec = true) :
    ∃ L, ownedCheckWith outs L B B' sym dec = true := by
  unfold ownedCheckM at h
  cases hG : cfgOf (B.map Prod.fst) with
  | none => simp [hG] at h
  | some G =>
      cases hG' : cfgOf (B'.map Prod.fst) with
      | none => simp [hG, hG'] at h
      | some G' =>
          rw [hG, hG'] at h
          exact ⟨_, ownedCheckWithR_spec_at hS hG hG' h⟩

theorem ownedCheckM_with {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckM outs B B' = true) : ∃ L, ownedCheckWith outs L B B' = true :=
  ownedCheckM_with_at symSubst_x86 h

/-- **Soundness of the checker over an instruction set.** If the symbolic step `sym` and
    the symbolic branch condition `dec` satisfy the laws `SymLaws I sym dec` against the
    instruction set `I` and commute with substitution (`SymSubst sym dec`), and
    `ownedCheckM outs B B' sym dec` accepts, every halting run of `I` on the singleton program
    over `B` from a state at pc `0` of that function is matched by a halting run on the
    singleton program over `B'` from the same state, and the end states agree on the
    registers `outs`, on the arrays and on the word memory. -/
theorem ownedCheckM_sound_at {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec) (hS : SymSubst sym dec)
    {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckM outs B B' sym dec = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', I.lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' := by
  obtain ⟨L, hL'⟩ := ownedCheckM_with_at hS h
  exact ownedCheckWith_sound_at hL hL' fn s t hfn hpc fuel hrun

/-- **Soundness of the checker.** If `ownedCheckM outs B B'` accepts, every halting
    `lsemFuelMemF` run of the singleton program over `B` from a state at pc `0` of that
    function is matched by a halting run of the singleton program over `B'` from the same
    state, and the end states agree on the registers `outs`, on the arrays and on the word
    memory. -/
theorem ownedCheckM_sound {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckM outs B B' = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' := by
  obtain ⟨L, hL⟩ := ownedCheckM_with h
  exact ownedCheckWith_sound hL fn s t hfn hpc fuel hrun

/-! ## 17. Programs -/

/-- A body typed instruction by instruction with the memory tag `tag`. -/
def typeBody (tag : LinstrR → MemTag) (c : Lcmd) : List LinstrRM :=
  c.map fun i => (i.li_i, tag i.li_i)

/-- A typed body without its trailing `Lret`: `lsemFuelMemF` takes no step at `Lret`, so a
    halting run of a body leaves it by falling off its end. -/
def dropRet (c : List LinstrRM) : List LinstrRM :=
  match c.getLast? with
  | some (.Lret, _) => c.dropLast
  | _ => c

/-- The memory cells that the body `c` writes at the argument pointers `args` or at the
    output-store base `reloadScratch2`: the destination registers `mem.<a>.<off>`,
    `a ∈ reloadScratch2 :: args`, of its operations, without repetition. The array ABI keeps
    such a cell as a register of that name. The ABI export stores its outputs through
    `reloadScratch2`, reloaded with the output pointer before each store
    (`physBodyWithStores`), so its output cells are `mem.R14.<off>`. -/
def memOuts (args : List String) (c : Lcmd) : List String :=
  (c.flatMap fun i =>
    match i.li_i with
    | .Lopn ds _ _ =>
        ds.filterMap fun
          | .reg d =>
              if (reloadScratch2 :: args).any (fun a => ("mem." ++ a ++ ".").isPrefixOf d) then
                some d
              else none
          | _ => none
    | _ => []).eraseDups

/-- The observed registers of a function: its result registers and the memory cells at its
    argument pointers or its output-store base that its body writes (`memOuts`). -/
def resOuts (f : Lfundef) : List String := f.lfd_res ++ memOuts f.lfd_arg f.lfd_body

/-- **Every result register is observed.** -/
theorem mem_resOuts_of_res {f : Lfundef} {r : String} (h : r ∈ f.lfd_res) : r ∈ resOuts f :=
  List.mem_append_left _ h

/-- **Every stored output cell is observed.** A cell `mem.<a>.<off>` that an operation of the
    body writes, at an argument pointer `a` or at the output-store base `reloadScratch2`, is
    among the observed registers `resOuts f`. -/
theorem mem_resOuts_of_cell {f : Lfundef} {i : Linstr} {ds : List LOperand} {opn : String}
    {ss : List LOperand} {d a : String} (hi : i ∈ f.lfd_body) (hl : i.li_i = .Lopn ds opn ss)
    (hd : LOperand.reg d ∈ ds) (ha : a ∈ reloadScratch2 :: f.lfd_arg)
    (hp : ("mem." ++ a ++ ".").isPrefixOf d = true) : d ∈ resOuts f := by
  have hany : (reloadScratch2 :: f.lfd_arg).any (fun a => ("mem." ++ a ++ ".").isPrefixOf d)
      = true := List.any_eq_true.mpr ⟨a, ha, hp⟩
  unfold resOuts memOuts
  refine List.mem_append_right _ ?_
  rw [List.mem_eraseDups]
  refine List.mem_flatMap.mpr ⟨i, hi, ?_⟩
  rw [hl]
  exact List.mem_filterMap.mpr ⟨.reg d, hd, by simp only [hany, ite_true]⟩

/-- An operation writes an array: an indexed store, an immediate store or a zeroing. The
    checker's observation `Obs` compares the arrays. -/
def writesArrB : LinstrR → Bool
  | .Lopn _ opn _ =>
      opn.startsWith "STOREIDX" || opn.startsWith "STOREIMM" || opn.startsWith "ZEROARR"
  | _ => false

/-- **The function has an output the checker compares**: a result register or a written
    output cell (`resOuts`), or an array store. A function without one computes nothing the
    checker reads, so `ownedCheckTy` refuses it rather than accept a comparison of no
    output. -/
def hasOutB (f : Lfundef) : Bool :=
  !(resOuts f).isEmpty || f.lfd_body.any (fun i => writesArrB i.li_i)

theorem Obs.of_append {xs ys : List String} {t t' : LstateMF} (h : Obs (xs ++ ys) t t') :
    Obs xs t t' :=
  ⟨fun r hr => h.1 r (List.mem_append_left ys hr), h.2⟩

/-- **Every block of the body runs symbolically**: the symbolic run under `sym` of each block
    of `B` before its terminator is not `.fail`. `ownedCheckM` accepts a block whose run fails
    from every state without a comparison, since no halting run passes through it; a body
    with such a block (an operation the flag machine does not step) gives an acceptance that
    compares nothing on the runs through that block. -/
def blocksRunB (B : List LinstrRM) (sym : LinstrRM → SSt → SOut := symStep) : Bool :=
  match cfgOf (B.map Prod.fst) with
  | some G => (List.range G.blocks.size).all fun k =>
      match symRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start sym with
      | .fail => false
      | _ => true
  | none => false

/-- The checker on the first functions of two programs, for a typing `ty` of function
    bodies: the functions have the same name, the source function has an output the check
    compares (`hasOutB`) and every block of its typed body runs symbolically (`blocksRunB`),
    the rewritten body satisfies the printer's two-address
    precondition `TwoAddrLegalize.bodyTiedOk`, and `ownedCheckM` accepts the two typed
    bodies with the function's result registers and the memory cells its body writes at its
    argument pointers or its output-store base (`resOuts`) as the observed registers. -/
def ownedCheckTy (ty : Lcmd → List LinstrRM) (P P' : Lprog) : Bool :=
  match P.lp_funcs.head?, P'.lp_funcs.head? with
  | some (n, f), some (n', f') =>
      n == n' && hasOutB f && blocksRunB (ty f.lfd_body) && TwoAddrLegalize.bodyTiedOk f'.lfd_body &&
        ownedCheckM (resOuts f) (ty f.lfd_body) (ty f'.lfd_body)
  | _, _ => false

/-- The checker with every instruction at the register tag and the trailing `Lret` dropped. -/
def ownedCheck (P P' : Lprog) : Bool :=
  ownedCheckTy (fun c => dropRet (typeBody (fun _ => .reg none) c)) P P'

/-- **Soundness of the program checker, with the memory results.** If `ownedCheckTy ty P P'`
    accepts, the first functions of `P` and `P'` have one name, the source function has an
    output the check compares (`hasOutB`) and its typed body has no block whose symbolic run
    fails (`blocksRunB`), the rewritten body satisfies `bodyTiedOk`, and
    every halting `lsemFuelMemF` run of the typed source body from pc `0` is matched by a
    halting run of the typed rewritten body from the same state, with end states that agree
    on the result registers, on the memory cells the source body writes at its argument
    pointers or its output-store base (every stored output cell, `mem_resOuts_of_cell`), on
    the arrays and on the word memory. -/
theorem ownedCheckTy_sound_mem {ty : Lcmd → List LinstrRM} {P P' : Lprog}
    (h : ownedCheckTy ty P P' = true) :
    ∃ n f f', P.lp_funcs.head? = some (n, f) ∧ P'.lp_funcs.head? = some (n, f') ∧
      hasOutB f = true ∧ blocksRunB (ty f.lfd_body) = true ∧
      TwoAddrLegalize.bodyTiedOk f'.lfd_body = true ∧
      ∀ (fn : String) (s t : LstateMF), s.prog.lfn = fn → s.prog.base.reg.lpc = 0 →
        ∀ fuel, lsemFuelMemF (singletonProgM fn (ty f.lfd_body)) fuel s = some t →
        ∃ fuel' t', lsemFuelMemF (singletonProgM fn (ty f'.lfd_body)) fuel' s = some t' ∧
          Obs (resOuts f) t t' := by
  unfold ownedCheckTy at h
  split at h
  · rename_i n f n' f' h1 h2
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hn, hout⟩, hrunB⟩, htied⟩, hchk⟩ := h
    subst hn
    exact ⟨n, f, f', h1, h2, hout, hrunB, htied, fun fn s t hfn hpc fuel hrun =>
      ownedCheckM_sound hchk fn s t hfn hpc fuel hrun⟩
  · cases h

/-- **Soundness of the program checker.** If `ownedCheckTy ty P P'` accepts, the first
    functions of `P` and `P'` have one name, the rewritten body satisfies `bodyTiedOk`, and
    every halting `lsemFuelMemF` run of the typed source body from pc `0` is matched by a
    halting run of the typed rewritten body from the same state, with end states that agree
    on the result registers, the arrays and the word memory. -/
theorem ownedCheckTy_sound {ty : Lcmd → List LinstrRM} {P P' : Lprog}
    (h : ownedCheckTy ty P P' = true) :
    ∃ n f f', P.lp_funcs.head? = some (n, f) ∧ P'.lp_funcs.head? = some (n, f') ∧
      TwoAddrLegalize.bodyTiedOk f'.lfd_body = true ∧
      ∀ (fn : String) (s t : LstateMF), s.prog.lfn = fn → s.prog.base.reg.lpc = 0 →
        ∀ fuel, lsemFuelMemF (singletonProgM fn (ty f.lfd_body)) fuel s = some t →
        ∃ fuel' t', lsemFuelMemF (singletonProgM fn (ty f'.lfd_body)) fuel' s = some t' ∧
          Obs f.lfd_res t t' := by
  obtain ⟨n, f, f', h1, h2, -, -, htied, hsim⟩ := ownedCheckTy_sound_mem h
  refine ⟨n, f, f', h1, h2, htied, fun fn s t hfn hpc fuel hrun => ?_⟩
  obtain ⟨fuel', t', hrun', hobs⟩ := hsim fn s t hfn hpc fuel hrun
  exact ⟨fuel', t', hrun', hobs.of_append⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
