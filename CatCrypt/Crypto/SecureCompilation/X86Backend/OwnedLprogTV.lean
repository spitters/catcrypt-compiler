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
public import Std.Data.HashMap.Basic

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
immediate shifts) with the carry and overflow flags `withALUFlags` writes, the carry
family `ADC`, `SBB`, `ADCX`, `ADOX` of `carryStep`, and the two-source `MOV` and the
widening multiplies `MULX`, `MULXMEM` of `wideStep` (`symWide`: the low word the masked
low `MUL` term `mulLoT`, the term of the front's masked low product, and the high word
`STerm.mulx`), and the high word `MULXHI` of `lsemStepMC` (the term `bin "MULXHI"`, `binW`);
the carry arms of `lsemStepMC`, `SAR`, `CMOV`, the
casts and the compile-time-offset memory moves are `unk`. `symRun` composes the steps of a
list.

## The check

The two control-flow graphs (`AllocCheck.LcmdCFG.cfgOf`) must have the same number of
blocks and the same terminators. Each block pair is run symbolically from one symbolic
start state; the pair is accepted when the source block always fails or ends in `Lret`
(no halting run passes through it), or when every guard of the normal form (`normG`) of the
rewritten block's guards is one of the source block, two jumps name the same function, two
branch conditions have the same symbolic value, and at each exit the final symbolic states
agree on the registers live at the successor (on `outs` at an exit that leaves the body), on
the zero, carry and overflow flags when the flags are live, and on every array written,
with every start register these values read live at the block, and the flags live at the
block when a value reads a start flag. The live sets are computed by a fixpoint iteration
(`liveIter`) and checked, not trusted.

## Shared terms

The two bodies of a block pair run over one hash-consed term table (`Tbl`, `tRun`), so the
symbolic words of a block take space linear in its length and equal words are compared by
index. A word over the table stands for its instance under a substitution of its entries
(`STerm.subst`); the symbolic step commutes with substitution (`symStep_subst`), so the run
over the table is the symbolic run up to that substitution (`tRun_subst`), and the check
over the table (`blockOkR`) implies `blockOk` (`blockOkR_spec`).

## Main definitions

* `STerm`, `SArr`, `SFlag`, `SG`, `SSt`, `Holds`: symbolic values, states and the states
  they describe.
* `symN`, `symSh`, `symMC`, `symCast`, `symMem`, `aluFl`, `symCarry`, `symWide`, `symStep`,
  `symRun`:
  the symbolic step layer by layer, and runs.
* `SDec`, `symDec`: the symbolic value of a branch condition.
* `blockOk`, `ownedCheckWith`, `ownedCheckM`: the checker.
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

deriving instance Hashable for AluOp, CarryOp

/-- The two-source operation `m` at width `w`: the high word of the product (`mulHiW`) for
    `MULXHI`, the operation of `applyOpnN` otherwise, and `a` when `applyOpnN` has no
    operation `m`. -/
def binW (w : Nat) (m : String) (a b : BitVec w) : BitVec w :=
  if m = "MULXHI" then mulHiW a b else (applyOpnN w m [a, b]).getD a

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
  /-- Entry `k` of a term table (`TEnt`); a substitution (`STerm.subst`) gives it its term,
      and `STerm.ev` gives it the word of width `0`. -/
  | ref (k : Nat)

/-- A symbolic array cell over the registers and arrays at the start of a block. -/
inductive SArr where
  /-- The cell of a name at the start. -/
  | cell (r : String)
  /-- The array `a` read at shape `(w, n)` with element `i` set to `v`. -/
  | aset (a : SArr) (w n : Nat) (i v : STerm)
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
  | .ref _ => ⟨0, 0#0⟩

/-- The value of a symbolic array, for the start registers `V`, arrays `A` and flags `C`,
    `O`. -/
def SArr.ev : SArr → ArrCell
  | .cell r => A r
  | .aset a w n i v => ⟨w, n, stackSet (castA a.ev w n) (castW i.ev 64).toNat (castW v.ev w)⟩
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
  | t => t

/-- The width of a symbolic word that its outermost constructor fixes. -/
def STerm.wknown : STerm → Option Nat
  | .immW w _ => some w
  | .aget _ w _ _ => some w
  | .cin _ => some 1
  | .carryW .. => some 64
  | .carryF .. => some 1
  | .mulx .. => some 64
  | _ => none

theorem STerm.wbase_ev (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) :
    ∀ t : STerm, (t.wbase.ev V A C O).1 = (t.ev V A C O).1
  | .immAt _ x => by rw [STerm.wbase, STerm.wbase_ev V A C O x, STerm.ev]
  | .bin _ x _ => by rw [STerm.wbase, STerm.wbase_ev V A C O x, STerm.ev]
  | .un _ x => by rw [STerm.wbase, STerm.wbase_ev V A C O x, STerm.ev]
  | .shImm _ _ x => by rw [STerm.wbase, STerm.wbase_ev V A C O x, STerm.ev]
  | .reg _ => rfl
  | .immW _ _ => rfl
  | .aget _ _ _ _ => rfl
  | .cin _ => rfl
  | .aluF _ _ _ _ _ => rfl
  | .carryW _ _ _ _ => rfl
  | .carryF _ _ _ _ _ => rfl
  | .mulx _ _ _ => rfl
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

/-- A symbolic state: a symbolic word per register, a symbolic array per name, the
    symbolic zero flag, the registers and names written, and the symbolic carry and
    overflow flags as words of width `1`. -/
structure SSt where
  /-- The symbolic word of each register. -/
  regs : String → STerm
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

/-- The symbolic state at the start of a block. -/
def SSt.start : SSt := ⟨STerm.reg, SArr.cell, .init, [], [], .cin false, .cin true⟩

/-- `ss` with register `d` set to `t`. -/
def SSt.setR (ss : SSt) (d : String) (t : STerm) : SSt :=
  { ss with regs := fun r => if r = d then t else ss.regs r, wr := d :: ss.wr }

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
  simp only [SSt.setR, List.mem_cons, not_or] at hr ⊢
  rw [if_neg hr.1]
  exact h.1 r hr.2

theorem SSt.Good.setA {ss : SSt} (h : ss.Good) (d : String) (a : SArr) :
    (ss.setA d a).Good := by
  refine ⟨h.1, fun r hr => ?_⟩
  simp only [SSt.setA, List.mem_cons, not_or] at hr ⊢
  rw [if_neg hr.1]
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
def shOk (m : String) : Bool := m == "SAR" || m == "SHL" || m == "SHR"

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
  rcases h with (h | h) | h <;> subst h <;> simp [applyImmShiftN, applyOpnN]

theorem applyImmShiftN_some {w : Nat} {m : String} (h : shOk m = true) (k : Nat) (a : BitVec w) :
    (applyImmShiftN w m k a).isSome := by
  simp only [shOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | h <;> subst h <;> simp [applyImmShiftN, applyOpnN]

theorem applyImmShiftN_none {w : Nat} {m : String} (h : shOk m = false) (k : Nat)
    (a : BitVec w) : applyImmShiftN w m k a = none := by
  simp only [shOk, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  simp [applyImmShiftN, h.1.1, h.1.2, h.2]

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

/-- The symbolic description of `lsemStepN`. A shift `SHL`/`SHR` by an immediate operand is
    described by the immediate-shift term `shImm`, the term of the count-in-name form
    `SHL:k`/`SHR:k`, so both spellings of one shift have one term. Another two-source
    operation with an immediate `n` below `2 ^ w`, for the width `w` of its mnemonic's tag, is
    described with the second source `immW w n`, the term of a move of `n` into a register, so
    an operation on a register that holds a moved constant and the operation on the immediate
    have one term. A shift by the count `0` in either form is described as the copy of its
    source, the term of a register `MOV`. A commutative operation `opn d, [a, d]` with `a ≠ d`
    is described with its sources exchanged (`commSwap`), so it has the term of
    `opn d, [d, a]`. -/
def symN (x : LinstrR) (R : String → STerm) : ROut :=
  match x with
  | .Lopn [.reg _] opn [_, _, _] => if stripWidthTag opn = "CMOV" then .unk else .fail
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
                if stripWidthTag opn = "SHL" ∨ stripWidthTag opn = "SHR" then
                  if n = 0 then .set dst (R ra) []
                  else .set dst (.shImm (stripWidthTag opn) n (R ra)) []
                else if n < 2 ^ widthFromTag opn then
                  .set dst (.bin (stripWidthTag opn) (R ra) (.immW (widthFromTag opn) n)) []
                else .set dst (.bin (stripWidthTag opn) (R ra) (.immAt n (R ra))) []
            | _ => .fail
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
              if k = 0 then .set dst (R a) [] else .set dst (.shImm m k (R a)) []
            else .fail
        | none => .fail
  | .Lopn _ _ _ => .fail
  | .Lalign => .nop
  | .Llabel _ _ => .nop
  | _ => .fail

theorem readReg_reg (r : LstateN) (a : String) : readReg r (.reg a) = some (r.lvm a) := rfl

theorem stepN_bin_reg (r : LstateN) (dst opn ra rb : String) :
    lsemStepN (.Lopn [.reg dst] opn [.reg ra, .reg rb]) r =
      if (r.lvm rb).1 = (r.lvm ra).1 then
        (applyOpnN (r.lvm ra).1 (stripWidthTag opn) [(r.lvm ra).2, castW (r.lvm rb) (r.lvm ra).1]).map
          (fun v => (r.setReg dst v).nextPc)
      else none := by
  simp only [lsemStepN, readReg_reg, evalOperandN, getW_eq]
  split_ifs
  · simp only []
    cases applyOpnN _ _ _ <;> rfl
  · rfl

theorem stepN_bin_imm (r : LstateN) (dst opn ra : String) (n : Nat) :
    lsemStepN (.Lopn [.reg dst] opn [.reg ra, .imm n]) r =
      (applyOpnN (r.lvm ra).1 (stripWidthTag opn) [(r.lvm ra).2, BitVec.ofNat _ n]).map
        (fun v => (r.setReg dst v).nextPc) := by
  simp only [lsemStepN, readReg_reg, evalOperandN]
  cases applyOpnN _ _ _ <;> rfl

@[simp] theorem castW_mk {w : Nat} (v : BitVec w) : castW ⟨w, v⟩ w = v := by
  simp [castW]

theorem symN_sound (x : LinstrR) (R : String → STerm) : RSound (lsemStepN x) R (symN x R) := by
  intro V A C O r hr
  unfold symN
  split
  · split_ifs with h
    · trivial
    · simp [ROut.Desc, lsemStepN, h]
  · rename_i dst opn a b
    split
    · rename_i ra
      by_cases hb : binOk (stripWidthTag opn) = true
      · rw [if_pos hb]
        split
        · rename_i rb
          have key : ROut.Desc (lsemStepN (.Lopn [.reg dst] opn [.reg ra, .reg rb])) V A C O r
              (.set dst (.bin (stripWidthTag opn) (R ra) (R rb)) [.eqW (R ra) (R rb)]) := by
            simp only [ROut.Desc]
            rw [stepN_bin_reg, hr ra, hr rb]
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
          rw [stepN_bin_imm, hr ra]
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (applyOpnN_bin_some hb
            ((R ra).ev V A C O).2 (BitVec.ofNat ((R ra).ev V A C O).1 n))
          split_ifs with hs hz
          · subst hz
            have h0 : ∀ {w : Nat} (x : BitVec w),
                applyOpnN w (stripWidthTag opn) [x, BitVec.ofNat w 0] = some x := by
              intro w x
              rcases hs with hs | hs <;> simp [hs, applyOpnN]
            simp [AllG, h0]
          · have he : ∀ {w : Nat} (x : BitVec w), applyImmShiftN w (stripWidthTag opn) n x =
                applyOpnN w (stripWidthTag opn) [x, BitVec.ofNat w n] := by
              intro w x
              unfold applyImmShiftN
              rcases hs with hs | hs <;> simp [hs]
            simp [AllG, STerm.ev, he, hv]
          · rename_i hlt
            simp [AllG, STerm.ev, binW_of_binOk hb, extW_ofNat hlt, hv]
          · simp [AllG, STerm.ev, binW_of_binOk hb, extW_of_eq, hv]
        · rename_i hb1 hb2
          cases b with
          | reg rb => exact absurd rfl (hb1 rb)
          | imm n => exact absurd rfl (hb2 n)
          | arr _ _ => simp [ROut.Desc, lsemStepN, readReg, evalOperandN]
          | arrIdx _ _ _ => simp [ROut.Desc, lsemStepN, readReg, evalOperandN]
      · rw [if_neg hb]
        simp only [ROut.Desc]
        have hn : ∀ {w : Nat} (x y : BitVec w), applyOpnN w (stripWidthTag opn) [x, y] = none :=
          fun x y => applyOpnN_bin_none (Bool.eq_false_iff.mpr hb) x y
        cases b with
        | reg rb => rw [stepN_bin_reg, hn]; simp
        | imm n => rw [stepN_bin_imm, hn]; simp
        | _ => simp [lsemStepN, evalOperandN, readReg]
    · rename_i ha
      cases a with
      | reg ra => exact absurd rfl (ha ra)
      | _ => simp [ROut.Desc, lsemStepN, readReg]
  · split_ifs with h
    · simp [ROut.Desc, lsemStepN, h, AllG, STerm.ev]
    · simp [ROut.Desc, lsemStepN, h]
  · rename_i dst opn a
    split_ifs with h1 h2
    · simp [ROut.Desc, lsemStepN, h1, readReg, hr a, AllG, STerm.ev, applyOpnN]
    · simp [ROut.Desc, lsemStepN, h2, readReg, hr a, AllG, applyOpnN]
    · split
      · rename_i m k hm
        split_ifs with hs hz
        · subst hz
          simp [ROut.Desc, lsemStepN, h1, h2, hm, readReg, hr a, applyImmShiftN_zero hs, AllG]
        · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
            (applyImmShiftN_some hs k ((R a).ev V A C O).2)
          simp [ROut.Desc, lsemStepN, h1, h2, hm, readReg, hr a, hv, AllG, STerm.ev]
        · simp [ROut.Desc, lsemStepN, h1, h2, hm, readReg,
            applyImmShiftN_none (Bool.eq_false_iff.mpr hs)]
      · rename_i hm
        simp [ROut.Desc, lsemStepN, h1, h2, hm]
  · rename_i hA hB hC hD
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
    all_goals first | rfl | (rename_i heq; cases heq)
  · rfl
  · rfl
  · rename_i hA hB hC hD hE hF hG
    simp only [ROut.Desc]
    unfold lsemStepN
    split
    · exact (hA _ _ _ _ _ rfl).elim
    · exact (hB _ _ _ _ rfl).elim
    · exact (hC _ _ _ rfl).elim
    · exact (hD _ _ _ rfl).elim
    · exact (hE _ _ _ rfl).elim
    · exact (hF rfl).elim
    · exact (hG _ _ rfl).elim
    all_goals rfl

/-- The symbolic description of `lsemStepSh`: the structured `SAR` is outside the
    fragment. -/
def symSh (x : LinstrR) (R : String → STerm) : ROut :=
  match sarStruct? x with
  | some _ => .unk
  | none => symN x R

theorem symSh_sound (x : LinstrR) (R : String → STerm) : RSound (lsemStepSh x) R (symSh x R) := by
  intro V A C O r hr
  unfold symSh
  split
  · trivial
  · rename_i h
    have := symN_sound x R V A C O r hr
    simpa only [ROut.Desc, lsemStepSh_of_not_sar x r h] using this

/-- The symbolic description of `lsemStepMC`: the high word `MULXHI d, a, b` of a product is
    the term `bin "MULXHI"` under the guard that `a` and `b` have one width; the carry arms are
    outside the fragment. -/
def symMC (x : LinstrR) (R : String → STerm) : ROut :=
  match mulhiStruct? x with
  | some (d, a, b) => .set d (.bin "MULXHI" (R a) (R b)) [.eqW (R a) (R b)]
  | none =>
      match adcxStruct? x, adcxhiStruct? x, sbbStruct? x, sbbhiStruct? x with
      | none, none, none, none => symSh x R
      | _, _, _, _ => .unk

theorem symMC_sound (x : LinstrR) (R : String → STerm) : RSound (lsemStepMC x) R (symMC x R) := by
  intro V A C O r hr
  unfold symMC
  split
  · rename_i d a b h
    simp only [ROut.Desc, lsemStepMC, h, readReg_reg, hr a, getW_eq, hr b, AllG,
      List.mem_singleton, forall_eq, SG.holds, STerm.ev, binW, if_true]
    split_ifs with hw
    · simp [extW_of_eq hw, hw.symm]
    · simp [Ne.symm hw]
  · rename_i h1
    split
    · rename_i h2 h3 h4 h5
      have := symSh_sound x R V A C O r hr
      simpa only [ROut.Desc, lsemStepMC_of_delegate x r h1 h2 h3 h4 h5] using this
    · trivial

/-- The symbolic description of `lsemStepCast`: an untagged immediate move with a descriptor
    `w'` sets its destination to the immediate at width `w'`; a cast with a descriptor is
    outside the fragment. -/
def symCast (i : LinstrRT) (R : String → STerm) : ROut :=
  match castStruct? i.1 with
  | none =>
      match movImmStruct? i.1, i.2 with
      | some (d, n), some w' => .set d (.immW w' n) []
      | _, _ => symMC i.1 R
  | some _ =>
      match i.2 with
      | none => symMC i.1 R
      | some _ => .unk

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
  | some _ =>
    cases hd : i.2 with
    | none =>
      have := symMC_sound i.1 R V A C O r hr
      simpa only [ROut.Desc, lsemStepCast_of_delegate i r (Or.inr hd)] using this
    | some _ => trivial

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
  simp only [SSt.setR, LstateN.lvm_nextPc, LstateN.lvm_setReg]
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
             · simp only [c1, c2, if_true, Option.map_some, Option.some.injEq] at ht
               subst ht
               refine ⟨allG_append.mpr ⟨g1.mpr c1, g2.mpr c2⟩,
                 ⟨fun q => (hreg _ q).trans ?_, hs.2.1, hs.2.2.1, ?_, ?_⟩, rfl, rfl, rfl⟩
               all_goals first
                 | (by_cases hq : q = d <;>
                     simp [hq, SSt.setR, STerm.ev, carryWord, hs.2.2.2.1, hs.2.2.2.2])
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
        · simp only [c1, if_true, Option.map_some, Option.some.injEq] at ht
          subst ht
          refine ⟨g1.mpr c1, ⟨fun q => ?_, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩,
            rfl, rfl, rfl⟩
          simp only [SSt.setR, LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.lvm_nextPc,
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
            · simp only [c0, c1, if_true, Option.map_some, Option.some.injEq] at ht
              subst ht
              refine ⟨allG_append.mpr ⟨g0.mpr c0, g1.mpr c1⟩,
                ⟨fun q => ?_, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩, rfl, rfl, rfl⟩
              simp only [SSt.setR, LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.lvm_nextPc,
                LstateN.lvm_setReg]
              by_cases hq : q = hi
              · simp [hq, STerm.ev]
              · by_cases hl : q = lo
                · subst hl
                  simp only [hq, if_false, if_true]
                  rw [mulLoT_ev c0 c1]
                · simp only [hq, hl, if_false]
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
            · simp only [c1, c2, if_true, Option.some.injEq] at ht
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
      simp only [SSt.setR, LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.lvm_nextPc,
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
    simp only [hmx, if_false]
    dsimp only [symN]
    simp only [hb, hs1, hs2, Bool.false_eq_true, ↓reduceIte]
  have hM : symMem (.Lopn [.reg d] opn [.reg x, .reg d], τ) ss =
      symMem (.Lopn [.reg d] opn [.reg d, .reg x], τ) ss := by
    cases τ <;> simp only [symMem, loadStruct?, storeStruct?, hC]
  have hA : ∀ ofl, aluFlT (.Lopn [.reg d] opn [.reg x, .reg d], τ) ss ofl =
      aluFlT (.Lopn [.reg d] opn [.reg d, .reg x], τ) ss ofl := by
    intro ofl
    simp only [aluFlT, aluFlagOp?, aluSwap, hs1, hs2, hsub, if_false]
    split_ifs <;> simp [symOp64]
  simp only [symStep, cmpArgs?, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?, hcmp, hadc,
    hsbb, hadcx, hadox, hmov, if_false, hM]
  cases symMem (.Lopn [.reg d] opn [.reg d, .reg x], τ) ss <;> simp only [aluFl, hA]

/-! ## 6. Straight-line runs -/

/-- The flag-machine steps of a list of instructions, in order. -/
def runL (P : LprogM) : List LinstrRM → LstateMF → Option LstateMF
  | [], s => some s
  | i :: is, s => (evalInstrPMemF P i s).bind (runL P is)

/-- The symbolic run of a list of instructions: the final symbolic state with the guards
    of every step, `fail` when a step always fails, `unk` when a step is outside the
    fragment. -/
def symRun : List LinstrRM → SSt → SOut
  | [], ss => .ok ss []
  | i :: is, ss =>
      match symStep i ss with
      | .ok ss1 g1 =>
          match symRun is ss1 with
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

/-- **The symbolic run describes the run exactly.** From every state `ss` describes, the
    steps of `is` succeed exactly when the guards of `symRun is ss` hold, and then end in
    a state its final symbolic state describes; a run `symRun` reports as failing fails. -/
theorem symRun_sound (P : LprogM) :
    ∀ (is : List LinstrRM) (ss : SSt) (V : String → Σ w, BitVec w) (A : String → ArrCell)
      (C O : Bool) (Z : Bool) (s : LstateMF), Holds V A C O Z ss s →
      (symRun is ss).DescN is.length (runL P is s) V A C O Z s
  | [], ss, V, A, C, O, Z, s, hs => by
      refine ⟨fun t ht => ?_, fun _ => rfl⟩
      cases ht
      exact ⟨allG_nil V A C O, hs, rfl, rfl, rfl⟩
  | i :: is, ss, V, A, C, O, Z, s, hs => by
      have hstep := symStep_sound P i ss V A C O Z s hs
      simp only [symRun, runL]
      cases h1 : symStep i ss with
      | ok ss1 g1 =>
          rw [h1] at hstep
          obtain ⟨hs1, hs2⟩ := hstep
          cases h2 : symRun is ss1 with
          | ok ss2 g2 =>
              simp only [h2, SOut.DescN]
              refine ⟨fun t ht => ?_, fun hg => ?_⟩
              · obtain ⟨s1, e1, e2⟩ := Option.bind_eq_some_iff.mp ht
                obtain ⟨hg1, hH1, hF1⟩ := hs1 s1 e1
                have ih := symRun_sound P is ss1 V A C O Z s1 hH1
                rw [h2] at ih
                obtain ⟨hg2, hH2, hF2⟩ := ih.1 t e2
                refine ⟨allG_append.mpr ⟨hg1, hg2⟩, hH2, ?_, ?_, ?_⟩
                · rw [hF2.1, hF1.1]
                · rw [hF2.2.1, hF1.2.1, List.length_cons]; omega
                · rw [hF2.2.2, hF1.2.2]
              · obtain ⟨hg1, hg2⟩ := allG_append.mp hg
                obtain ⟨s1, e1⟩ := Option.isSome_iff_exists.mp (hs2 hg1)
                have ih := symRun_sound P is ss1 V A C O Z s1 (hs1 s1 e1).2.1
                rw [h2] at ih
                rw [e1, Option.bind_some]
                exact ih.2 hg2
          | fail =>
              simp only [h2, SOut.DescN]
              cases e1 : evalInstrPMemF P i s with
              | none => rfl
              | some s1 =>
                  have ih := symRun_sound P is ss1 V A C O Z s1 (hs1 s1 e1).2.1
                  rw [h2] at ih
                  exact ih
          | unk => simp only [h2, SOut.DescN]
      | fail =>
          rw [h1] at hstep
          simp only [SOut.DescN]
          simp only [SOut.Desc] at hstep
          rw [hstep, Option.bind_none]
      | unk => simp only [SOut.DescN]

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

theorem symRun_good : ∀ (is : List LinstrRM) {ss : SSt}, ss.Good → ∀ {ss' : SSt} {gs : List SG},
    symRun is ss = .ok ss' gs → ss'.Good
  | [], ss, hg, ss', gs, h => by
      simp only [symRun, SOut.ok.injEq] at h; rw [← h.1]; exact hg
  | i :: is, ss, hg, ss', gs, h => by
      cases h1 : symStep i ss with
      | ok ss1 g1 =>
          cases h2 : symRun is ss1 with
          | ok ss2 g2 =>
              simp only [symRun, h1, h2, SOut.ok.injEq] at h
              rw [← h.1]
              exact symRun_good is (symStep_good i hg h1) h2
          | fail => simp [symRun, h1, h2] at h
          | unk => simp [symRun, h1, h2] at h
      | fail => simp [symRun, h1] at h
      | unk => simp [symRun, h1] at h

/-- A label declaration. -/
def isLbl (i : LinstrRM) : Bool :=
  match i.1 with
  | .Llabel _ _ => true
  | _ => false

theorem symStep_label {i : LinstrRM} (h : isLbl i = true) (ss : SSt) :
    symStep i ss = .ok ss [] := by
  obtain ⟨x, tag⟩ := i
  cases x <;> simp_all [isLbl, symStep, cmpArgs?, movRegArgs?, flagCondCC?]

theorem symRun_label {i : LinstrRM} (h : isLbl i = true) (is : List LinstrRM) (ss : SSt) :
    symRun (i :: is) ss = symRun is ss := by
  simp only [symRun, symStep_label h]
  cases symRun is ss <;> simp

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
  | .ref _ => []

/-- The start registers a symbolic array reads. -/
def SArr.vars : SArr → List String
  | .cell _ => []
  | .aset a _ _ i v => a.vars ++ i.vars ++ v.vars
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
  | .ref _ => false

/-- The symbolic array reads the carry or the overflow flag at the start. -/
def SArr.readsF : SArr → Bool
  | .cell _ => false
  | .aset a _ _ i v => a.readsF || i.readsF || v.readsF
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

/-- A halting run from the start of a stretch `xs` of non-terminators of the body runs
    `xs` and then the rest. -/
theorem fuel_runL :
    ∀ (xs rest : List LinstrRM) (s t : LstateMF) (fuel : Nat), s.prog.lfn = fn →
      B.drop s.prog.base.reg.lpc = xs ++ rest → (∀ x ∈ xs, isTermR x.1 = false) →
      lsemFuelMemF (singletonProgM fn B) fuel s = some t →
      ∃ u f, fuel = xs.length + f ∧ runL (singletonProgM fn B) xs s = some u ∧
        lsemFuelMemF (singletonProgM fn B) f u = some t
  | [], _, s, t, fuel, _, _, _, h => ⟨s, fuel, by simp, rfl, h⟩
  | x :: xs, rest, s, t, fuel, hfn, hB, hx, h => by
      have hget : B[s.prog.base.reg.lpc]? = some x := by
        rw [← List.head?_drop, hB]; rfl
      cases fuel with
      | zero =>
          simp [lsemFuelMemF, findInstrMem_single hfn, hget] at h
      | succ f =>
          simp only [lsemFuelMemF, findInstrMem_single hfn, hget] at h
          cases he : evalInstrPMemF (singletonProgM fn B) x s with
          | none => rw [he] at h; cases h
          | some s1 =>
              rw [he] at h
              obtain ⟨h1, h2⟩ := step_plain (hx x (by simp)) he
              have hB1 : B.drop s1.prog.base.reg.lpc = xs ++ rest := by
                rw [h2, ← List.drop_drop, hB]; rfl
              obtain ⟨u, f', hf, hu, hrun⟩ := fuel_runL xs rest s1 t f (h1.trans hfn) hB1
                (fun y hy => hx y (by simp [hy])) h
              refine ⟨u, f', by simp [hf]; omega, ?_, hrun⟩
              simp [runL, he, hu]

/-- A run of a stretch `xs` of non-terminators of the body is the first `xs.length` steps
    of every run from its start. -/
theorem runL_fuel :
    ∀ (xs rest : List LinstrRM) (s u : LstateMF), s.prog.lfn = fn →
      B.drop s.prog.base.reg.lpc = xs ++ rest → (∀ x ∈ xs, isTermR x.1 = false) →
      runL (singletonProgM fn B) xs s = some u → ∀ f,
      lsemFuelMemF (singletonProgM fn B) (xs.length + f) s =
        lsemFuelMemF (singletonProgM fn B) f u
  | [], _, s, u, _, _, _, h, f => by simp only [runL, Option.some.injEq] at h; subst h; simp
  | x :: xs, rest, s, u, hfn, hB, hx, h, f => by
      have hget : B[s.prog.base.reg.lpc]? = some x := by
        rw [← List.head?_drop, hB]; rfl
      simp only [runL] at h
      cases he : evalInstrPMemF (singletonProgM fn B) x s with
      | none => rw [he] at h; cases h
      | some s1 =>
          rw [he, Option.bind_some] at h
          obtain ⟨h1, h2⟩ := step_plain (hx x (by simp)) he
          have hB1 : B.drop s1.prog.base.reg.lpc = xs ++ rest := by
            rw [h2, ← List.drop_drop, hB]; rfl
          rw [List.length_cons, show xs.length + 1 + f = (xs.length + f) + 1 by omega]
          simp only [lsemFuelMemF, findInstrMem_single hfn, hget, he]
          exact runL_fuel xs rest s1 u (h1.trans hfn) hB1 (fun y hy => hx y (by simp [hy])) h f

end Run

/-! ## 9. Terminators -/

/-- The polarity of a condition-code operand: `Z` jumps on a set zero flag, `NZ` on a
    clear one; any other operand is read as a register. -/
def ccPol : LOperand → Option Bool
  | .reg "Z" => some true
  | .reg "NZ" => some false
  | _ => none

theorem flagCondCC?_cond (c : LOperand) (l : LLabel) (tag : MemTag) :
    flagCondCC? (.Lcond c l, tag) = (ccPol c).map (fun p => (p, l)) := by
  unfold flagCondCC? ccPol
  split <;> simp_all

/-- The branch a conditional takes from state `s`. -/
def decC (s : LstateMF) (c : LOperand) : Bool :=
  match ccPol c with
  | some pol => s.zf == pol
  | none => condNZ s.prog.base c

theorem evalInstrPMemF_cond (P : LprogM) (c : LOperand) (l : LLabel) (tag : MemTag)
    (s : LstateMF) :
    evalInstrPMemF P (.Lcond c l, tag) s =
      if decC s c = true then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
      else some { s with prog := { s.prog with base := s.prog.base.nextPc } } := by
  unfold decC
  cases hcc : ccPol c with
  | some pol =>
      unfold evalInstrPMemF
      simp only [cmpArgs?, movRegArgs?, flagCondCC?_cond, hcc]
      simp [beq_iff_eq]
  | none =>
      have hf : flagCondCC? (LinstrR.Lcond c l, tag) = none := by
        rw [flagCondCC?_cond, hcc]; rfl
      rw [evalInstrPMemF_delegate P _ s rfl rfl hf rfl rfl rfl]
      simp only [evalInstrPMemL]
      split <;> simp

theorem evalInstrPMemF_goto (P : LprogM) (x : String) (l : LLabel) (tag : MemTag)
    (s : LstateMF) :
    evalInstrPMemF P (.Lgoto (x, l), tag) s =
      if x = P.lfn then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
      else none := by
  rw [evalInstrPMemF_delegate P _ s rfl rfl rfl rfl rfl rfl]
  simp only [evalInstrPMemL]
  split <;> simp

theorem evalInstrPMemF_ret (P : LprogM) (tag : MemTag) (s : LstateMF) :
    evalInstrPMemF P (.Lret, tag) s = none := by
  rw [evalInstrPMemF_delegate P _ s rfl rfl rfl rfl rfl rfl]
  simp [evalInstrPMemL, lsemStepMem_ret]

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

/-- The two terminator instructions agree: two jumps name the same function, and two
    branches have the same symbolic condition, which reads only live names. -/
def termAgree (T : Term) (n : List String × Bool) (ss ss' : SSt) :
    Option LinstrRM → Option LinstrRM → Bool
  | some (.Lgoto (a, _), _), some (.Lgoto (b, _), _) =>
      match T with
      | .goto _ => a == b
      | _ => false
  | some (.Lcond c _, _), some (.Lcond c' _, _) =>
      match T with
      | .cond _ _ =>
          symDec ss c == symDec ss' c' && vIn n (symDec ss c).vars &&
            (!(symDec ss c).readsInit || n.2)
      | _ => false
  | _, _ =>
      match T with
      | .fall _ => true
      | _ => false

/-- The two final symbolic states agree at every exit of a block with live set `n` and
    terminator `T`: on the registers live at each successor and, when the flags are live
    there, on the zero, carry and overflow flags; on `outs` when the block may leave the
    body; and on every array written. Every value compared passes `okIn n`. -/
def exitAgree (outs : List String) (L : Nat → List String × Bool) (n : List String × Bool)
    (T : Term) (ss ss' : SSt) : Bool :=
  T.succs.all (fun j =>
      (L j).1.all (fun r =>
          ss.regs r == ss'.regs r && okIn n (ss.regs r).vars (ss.regs r).readsF) &&
        (!(L j).2 || (ss.zf == ss'.zf && okIn n ss.zf.vars ss.zf.readsInit &&
          ss.cf == ss'.cf && okIn n ss.cf.vars ss.cf.readsF &&
          ss.of == ss'.of && okIn n ss.of.vars ss.of.readsF))) &&
    (!T.halts ||
      outs.all (fun r => ss.regs r == ss'.regs r && okIn n (ss.regs r).vars (ss.regs r).readsF)) &&
    (ss.awr ++ ss'.awr).all (fun q =>
      ss.arrs q == ss'.arrs q && okIn n (ss.arrs q).vars (ss.arrs q).readsF)

/-- The check of block `k` of the source body `B` (block `b`) against block `k` of the
    rewritten body `B'` (block `b'`), both with terminator `T`, for the live sets `L`. -/
def blockOk (outs : List String) (L : Nat → List String × Bool) (k : Nat) (T : Term)
    (B B' : List LinstrRM) (b b' : Block) : Bool :=
  match T with
  | .ret => true
  | _ =>
      match symRun (bodyAt B b T) SSt.start with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          match symRun (bodyAt B' b' T) SSt.start with
          | .ok ss' gs' =>
              (normG gs').all (fun g => (normG gs).contains g && okIn (L k) g.vars g.readsF) &&
                termAgree T (L k) ss ss' B[b.stop - 1]? B'[b'.stop - 1]? &&
                exitAgree outs L (L k) T ss ss'
          | _ => false

/-- The checker for the live sets `L`: the two bodies are non-empty, their graphs have the
    same number of blocks and the same terminators, and every block pair passes
    `blockOk`. -/
def ownedCheckWith (outs : List String) (L : Nat → List String × Bool)
    (B B' : List LinstrRM) : Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      !B.isEmpty && !B'.isEmpty && G.blocks.size == G'.blocks.size &&
        (List.range G.blocks.size).all (fun k =>
          (G.blk k).term == (G'.blk k).term &&
            blockOk outs L k (G.blk k).term B B' (G.blk k) (G'.blk k))
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
    {n : List String × Bool} {T : Term} {ss ss' : SSt} (h : exitAgree outs L n T ss ss' = true) :
    (∀ j ∈ T.succs,
      (∀ r ∈ (L j).1, ss.regs r = ss'.regs r ∧
        okIn n (ss.regs r).vars (ss.regs r).readsF = true) ∧
      ((L j).2 = true → ss.zf = ss'.zf ∧ okIn n ss.zf.vars ss.zf.readsInit = true ∧
        ss.cf = ss'.cf ∧ okIn n ss.cf.vars ss.cf.readsF = true ∧
        ss.of = ss'.of ∧ okIn n ss.of.vars ss.of.readsF = true)) ∧
    (T.halts = true → ∀ r ∈ outs, ss.regs r = ss'.regs r ∧
      okIn n (ss.regs r).vars (ss.regs r).readsF = true) ∧
    (∀ q ∈ ss.awr ++ ss'.awr, ss.arrs q = ss'.arrs q ∧
      okIn n (ss.arrs q).vars (ss.arrs q).readsF = true) := by
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
    (hex : exitAgree outs L n T ss ss' = true) :
    (∀ j ∈ T.succs, Rel (L j) u u') ∧ (T.halts = true → Obs outs u u') := by
  obtain ⟨hs, hh, ha⟩ := exitAgree_spec hex
  have hterm : ∀ t : STerm, okIn n t.vars t.readsF = true → t.ev V' A C' O' = t.ev V A C O :=
    fun t ht => STerm.ev_congr A t (fun r hr => hV r ((okIn_spec ht).1 r hr))
      (fun e => (hZ ((okIn_spec ht).2 e)).2)
  have harr : u'.prog.base.larr = u.prog.base.larr := by
    funext q
    rw [hH'.2.1 q, hH.2.1 q]
    by_cases hq : q ∈ ss.awr ++ ss'.awr
    · obtain ⟨e, v⟩ := ha q hq
      rw [← e]
      exact SArr.ev_congr A _ (fun r hr => hV r ((okIn_spec v).1 r hr))
        (fun e => (hZ ((okIn_spec v).2 e)).2)
    · simp only [List.mem_append, not_or] at hq
      rw [hg.2 q hq.1, hg'.2 q hq.2]
      rfl
  have hreg : ∀ r, ss.regs r = ss'.regs r →
      okIn n (ss.regs r).vars (ss.regs r).readsF = true →
      u'.prog.base.reg.lvm r = u.prog.base.reg.lvm r := by
    intro r e v
    rw [hH'.1 r, hH.1 r, ← e]
    exact hterm _ v
  refine ⟨fun j hj => ⟨hlfn, harr, hmem, fun r hr => ?_, fun hl => ?_⟩, fun hT => ?_⟩
  · obtain ⟨e, v⟩ := (hs j hj).1 r hr
    exact hreg r e v
  · obtain ⟨e, z, ec, zc, eo, zo⟩ := (hs j hj).2 hl
    refine ⟨?_, ?_, ?_⟩
    · rw [hH'.2.2.1, hH.2.2.1, ← e]
      exact SFlag.ev_congr A _ (fun r hr => hV r ((okIn_spec z).1 r hr))
        (fun hr => hZ ((okIn_spec z).2 hr))
    · rw [hH'.2.2.2.1, hH.2.2.2.1, ← ec, hterm _ zc]
    · rw [hH'.2.2.2.2, hH.2.2.2.2, ← eo, hterm _ zo]
  · refine ⟨fun r hr => ?_, harr, hmem⟩
    obtain ⟨e, v⟩ := hh hT r hr
    exact hreg r e v

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

theorem runL_frame {fn : String} {B : List LinstrRM} :
    ∀ (xs : List LinstrRM) (s u : LstateMF), (∀ x ∈ xs, isTermR x.1 = false) →
      runL (singletonProgM fn B) xs s = some u →
      u.prog.lfn = s.prog.lfn ∧ u.prog.base.reg.lpc = s.prog.base.reg.lpc + xs.length
  | [], s, u, _, h => by simp only [runL, Option.some.injEq] at h; subst h; simp
  | x :: xs, s, u, hx, h => by
      simp only [runL] at h
      cases he : evalInstrPMemF (singletonProgM fn B) x s with
      | none => rw [he] at h; cases h
      | some s1 =>
          rw [he, Option.bind_some] at h
          obtain ⟨h1, h2⟩ := step_plain (hx x (by simp)) he
          obtain ⟨h3, h4⟩ := runL_frame xs s1 u (fun y hy => hx y (by simp [hy])) h
          refine ⟨h3.trans h1, ?_⟩
          rw [h4, h2, List.length_cons]
          omega

theorem run_inv {P : LprogM} {f : Nat} {s t : LstateMF} {i : LinstrRM}
    (h : lsemFuelMemF P f s = some t) (hi : findInstrMem P s.prog = some i) :
    ∃ f1 s1, f = f1 + 1 ∧ evalInstrPMemF P i s = some s1 ∧ lsemFuelMemF P f1 s1 = some t := by
  cases f with
  | zero => simp [lsemFuelMemF, hi] at h
  | succ f1 =>
      simp only [lsemFuelMemF, hi] at h
      cases he : evalInstrPMemF P i s with
      | none => rw [he] at h; cases h
      | some s1 => rw [he] at h; exact ⟨f1, s1, rfl, rfl, h⟩

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

theorem symRun_entry {B : List LinstrRM} {b : Block} {T : Term} {p : Nat}
    (hp : EntryAt B b p) (hle : p ≤ bstopOf T b) :
    symRun ((B.drop p).take (bstopOf T b - p)) SSt.start = symRun (bodyAt B b T) SSt.start := by
  rcases hp with rfl | ⟨rfl, x, hx, hl⟩
  · rfl
  · unfold bodyAt
    rw [take_cons B (by omega) hx, symRun_label hl]

theorem blockOk_spec {outs : List String} {L : Nat → List String × Bool} {k : Nat} {T : Term}
    {B B' : List LinstrRM} {b b' : Block} (h : blockOk outs L k T B B' b b' = true)
    (hT : T ≠ .ret) :
    symRun (bodyAt B b T) SSt.start = .fail ∨
      ∃ ss gs ss' gs', symRun (bodyAt B b T) SSt.start = .ok ss gs ∧
        symRun (bodyAt B' b' T) SSt.start = .ok ss' gs' ∧
        (∀ g ∈ normG gs', g ∈ normG gs ∧ (∀ v ∈ g.vars, v ∈ (L k).1) ∧
          (g.readsF = true → (L k).2 = true)) ∧
        termAgree T (L k) ss ss' B[b.stop - 1]? B'[b'.stop - 1]? = true ∧
        exitAgree outs L (L k) T ss ss' = true := by
  have h2 : (match symRun (bodyAt B b T) SSt.start with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          match symRun (bodyAt B' b' T) SSt.start with
          | .ok ss' gs' =>
              (normG gs').all (fun g => (normG gs).contains g && okIn (L k) g.vars g.readsF) &&
                termAgree T (L k) ss ss' B[b.stop - 1]? B'[b'.stop - 1]? &&
                exitAgree outs L (L k) T ss ss'
          | _ => false) = true := by
    cases T with
    | ret => exact absurd rfl hT
    | _ => exact h
  cases hs : symRun (bodyAt B b T) SSt.start with
  | fail => exact Or.inl rfl
  | unk => rw [hs] at h2; cases h2
  | ok ss gs =>
      rw [hs] at h2
      cases ht : symRun (bodyAt B' b' T) SSt.start with
      | ok ss' gs' =>
          rw [ht] at h2
          simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h2
          obtain ⟨⟨hg, hta⟩, hex⟩ := h2
          exact Or.inr ⟨ss, gs, ss', gs', rfl, rfl,
            fun g hg' => ⟨(hg g hg').1, okIn_spec (hg g hg').2⟩, hta, hex⟩
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
    (G G' : CFG) : Prop where
  hG : cfgOf (B.map Prod.fst) = some G
  hG' : cfgOf (B'.map Prod.fst) = some G'
  size : G'.blocks.size = G.blocks.size
  blk : ∀ k < G.blocks.size, (G'.blk k).term = (G.blk k).term ∧
    blockOk outs L k (G.blk k).term B B' (G.blk k) (G'.blk k) = true

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

/-- The simulation up to the measure `N`: a halting source run from a block entry is
    matched by a halting run of the rewritten body. -/
def SimAt (outs : List String) (L : Nat → List String × Bool) (B B' : List LinstrRM)
    (G G' : CFG) (fn : String) (N : Nat) : Prop :=
  ∀ (fuel k : Nat) (s s' t : LstateMF),
    fuel * (G.blocks.size + 1) + (G.blocks.size - k) < N → k < G.blocks.size →
    Pair B B' (G.blk k) (G'.blk k) s.prog.base.reg.lpc s'.prog.base.reg.lpc →
    Rel (L k) s s' → s.prog.lfn = fn →
    lsemFuelMemF (singletonProgM fn B) fuel s = some t →
    ∃ f' t', lsemFuelMemF (singletonProgM fn B') f' s' = some t' ∧ Obs outs t t'

theorem halt_at_end {fn : String} {B : List LinstrRM} {w : LstateMF} (hfn : w.prog.lfn = fn)
    (hw : w.prog.base.reg.lpc = B.length) (f : Nat) :
    lsemFuelMemF (singletonProgM fn B) f w = some w := by
  apply lsemFuelMemF_halt
  rw [findInstrMem_single hfn, hw]
  simp

/-- Control that falls out of block `k` continues in the next block, or leaves both
    bodies. -/
theorem fall_cont {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G') {N k : Nat}
    (ih : SimAt outs L B B' G G' fn N) (hk : k < G.blocks.size) {nx : Option Nat}
    (hn : G.next k = nx) (hn' : G'.next k = nx) {w w' t : LstateMF} {f0 : Nat}
    (hw : w.prog.base.reg.lpc = (G.blk k).stop) (hw' : w'.prog.base.reg.lpc = (G'.blk k).stop)
    (hfn : w.prog.lfn = fn) (hfn' : w'.prog.lfn = fn)
    (hrun : lsemFuelMemF (singletonProgM fn B) f0 w = some t)
    (hmeas : f0 * (G.blocks.size + 1) + (G.blocks.size - (k + 1)) < N)
    (hrel : ∀ j, nx = some j → Rel (L j) w w') (hobs : nx = none → Obs outs w w') :
    ∃ f' t', lsemFuelMemF (singletonProgM fn B') f' w' = some t' ∧ Obs outs t t' := by
  have hk' : k < G'.blocks.size := hc.size ▸ hk
  cases nx with
  | none =>
      have e1 := (stop_next hc.hG hk).1 hn
      have e2 := (stop_next hc.hG' hk').1 hn'
      rw [halt_at_end hfn (hw.trans e1)] at hrun
      cases hrun
      exact ⟨0, w', halt_at_end hfn' (hw'.trans e2) 0, hobs rfl⟩
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
theorem jump_cont {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} {N tg : Nat} (ih : SimAt outs L B B' G G' fn N)
    (htg : tg < G.blocks.size) {l l' : LLabel}
    (hl : findLabel l (B.map Prod.fst) = some (G.blk tg).start)
    (hl' : findLabel l' (B'.map Prod.fst) = some (G'.blk tg).start) {w w' t : LstateMF}
    {f1 : Nat} (hw : w.prog.base.reg.lpc = (G.blk tg).start + 1)
    (hw' : w'.prog.base.reg.lpc = (G'.blk tg).start + 1) (hfn : w.prog.lfn = fn)
    (hrun : lsemFuelMemF (singletonProgM fn B) f1 w = some t)
    (hmeas : f1 * (G.blocks.size + 1) + (G.blocks.size - tg) < N) (hrel : Rel (L tg) w w') :
    ∃ f' t', lsemFuelMemF (singletonProgM fn B') f' w' = some t' ∧ Obs outs t t' :=
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

theorem sim_step {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G') {N : Nat}
    (ih : SimAt outs L B B' G G' fn N) : SimAt outs L B B' G G' fn (N + 1) := by
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
    fuel_runL _ _ s t fuel hfn (drop_split B hle) hplain hrun
  obtain ⟨hul, hup⟩ := runL_frame _ s u hplain hu
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
      run_inv hru (by rw [findInstrMem_single hul', hupc2, hz])
    obtain ⟨zi, zt⟩ := z
    simp only at hzr
    subst hzr
    rw [evalInstrPMemF_ret] at he
    cases he
  -- the symbolic runs of the two block bodies
  have hD := symRun_sound (singletonProgM fn B) ((B.drop s.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) SSt.start _ _ _ _ _ s
    (holds_start s)
  rw [symRun_entry hE hle] at hD
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
  have hD' := symRun_sound (singletonProgM fn B') ((B'.drop s'.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)) SSt.start _ _ _ _ _ s' hH0'
  rw [symRun_entry hE' hle', hS'] at hD'
  have hAllN := allG_normG.mpr hAll
  have hAll' : AllG s'.prog.base.reg.lvm s.prog.base.larr s'.prog.base.cf s'.prog.base.of gs' :=
    allG_normG.mp fun g hg =>
      (SG.holds_congr _ g (fun r hr => (hV r ((hgs g hg).2.1 r hr)).symm)
        (fun e => by
          obtain ⟨-, hc, ho⟩ := hrel.2.2.2.2 ((hgs g hg).2.2 e)
          exact ⟨hc.symm, ho.symm⟩)).mp
      (hAllN g (hgs g hg).1)
  obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp (hD'.2 hAll')
  obtain ⟨-, hH', hFr'⟩ := hD'.1 u' hu'
  have hplain' := body_plain hc.hG' hk' hs1'
  rw [hTk] at hplain' hbstop'
  have hrun' := runL_fuel _ _ s' u' hfn' (drop_split B' hle') hplain' hu'
  simp only [List.length_take, List.length_drop] at hrun'
  have hupc' : u'.prog.base.reg.lpc = bstopOf (G.blk k).term (G'.blk k) := by
    rw [hFr'.2.1]; simp only [List.length_take, List.length_drop]; omega
  have hul'' : u'.prog.lfn = fn := hFr'.1.trans hfn'
  obtain ⟨hsucc, hhalt⟩ := exit_rel hH hH' hV (fun hz => hrel.2.2.2.2 hz)
    (symRun_good _ SSt.good_start hS) (symRun_good _ SSt.good_start hS')
    (by rw [hul'', hul']) (by rw [hFr'.2.2, hrel.2.2.1, hFr.2.2]) hex
  have hfle : f ≤ fuel := by omega
  obtain ⟨m', hm'⟩ : ∃ m', ∀ f0, lsemFuelMemF (singletonProgM fn B') (m' + f0) s' =
      lsemFuelMemF (singletonProgM fn B') f0 u' := ⟨_, hrun'⟩
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
      run_inv hru (by rw [findInstrMem_single hul', hw, hz])
    rw [evalInstrPMemF_goto] at he
    by_cases hx : x = (singletonProgM fn B).lfn
    · rw [if_pos hx, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      have he' : evalInstrPMemF (singletonProgM fn B') (.Lgoto (x, l'), zt') u' =
          some { u' with prog := { u'.prog with
            base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } } := by
        rw [evalInstrPMemF_goto, if_pos (by simpa [singletonProgM, hul'', hul'] using hx),
          evalJumpMem_single hl']
        rfl
      obtain ⟨f'', t', hr, hobs⟩ := jump_cont (w' := { u' with prog := { u'.prog with
          base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } }) ih htg hl hl' rfl rfl
        (by exact hul') hr1
        (measure_lt hN (show f1 + 1 ≤ fuel by omega)) (hsucc tg (by simp [hT, Term.succs]))
      refine ⟨m' + (f'' + 1), t', ?_, hobs⟩
      rw [hm', lsemFuelMemF_step _ _ _ _ _ (by rw [findInstrMem_single hul'', hw', hz']) he']
      exact hr
    · rw [if_neg hx] at he
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
    have hdec : decC u' c' = decC u c := by
      rw [decC_eq hH' c', decC_eq hH c, ← hdeq]
      exact SDec.ev_congr _ _ (fun r hr => hV r (vIn_spec hdv r hr))
        (fun hz => hrel.2.2.2.2 (by
          rcases hdz with h | h
          · rw [hz] at h; cases h
          · exact h))
    have hw : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [hupc, hT]; rfl
    have hw' : u'.prog.base.reg.lpc = (G'.blk k).stop - 1 := by rw [hupc', hT]; rfl
    obtain ⟨f1, u1, hf1, he, hr1⟩ :=
      run_inv hru (by rw [findInstrMem_single hul', hw, hz])
    rw [evalInstrPMemF_cond] at he
    have hstop : 0 < (G.blk k).stop := by have := F.lt; omega
    have hstop' : 0 < (G'.blk k).stop := by have := F'.lt; omega
    by_cases hd : decC u c = true
    · rw [if_pos hd, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      have he' : evalInstrPMemF (singletonProgM fn B') (.Lcond c' l', zt') u' =
          some { u' with prog := { u'.prog with
            base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } } := by
        rw [evalInstrPMemF_cond, if_pos (hdec.trans hd), evalJumpMem_single hl']
        rfl
      obtain ⟨f'', t', hr, hobs⟩ := jump_cont (w' := { u' with prog := { u'.prog with
          base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } }) ih htg hl hl' rfl rfl
        (by exact hul') hr1
        (measure_lt hN (show f1 + 1 ≤ fuel by omega)) (hsucc tg (by simp [hT, Term.succs]))
      refine ⟨m' + (f'' + 1), t', ?_, hobs⟩
      rw [hm', lsemFuelMemF_step _ _ _ _ _ (by rw [findInstrMem_single hul'', hw', hz']) he']
      exact hr
    · rw [if_neg hd] at he
      simp only [Option.some.injEq] at he
      have he' : evalInstrPMemF (singletonProgM fn B') (.Lcond c' l', zt') u' =
          some { u' with prog := { u'.prog with base := u'.prog.base.nextPc } } := by
        rw [evalInstrPMemF_cond, if_neg (by rw [hdec]; exact hd)]
      obtain ⟨f'', t', hr, hobs⟩ := fall_cont (w := u1)
        (w' := { u' with prog := { u'.prog with base := u'.prog.base.nextPc } })
        hc ih hk hnx.symm hnx'.symm
        (by rw [← he]; show u.prog.base.reg.lpc + 1 = _; omega)
        (by show u'.prog.base.reg.lpc + 1 = _; omega)
        (by rw [← he]; exact hul') hul'' hr1 (measure_le hN (show f1 ≤ fuel by omega) hk)
        (fun j hj => by rw [← he]; exact hsucc j (by simp [hT, Term.succs, hj]))
        (fun hn => by rw [← he]; exact hhalt (by simp [hT, hn, Term.halts]))
      refine ⟨m' + (f'' + 1), t', ?_, hobs⟩
      rw [hm', lsemFuelMemF_step _ _ _ _ _ (by rw [findInstrMem_single hul'', hw', hz']) he']
      exact hr
  · exact absurd hT hret

theorem simAt_all {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G') :
    ∀ N, SimAt outs L B B' G G' fn N
  | 0 => fun _ _ _ _ _ hN => absurd hN (Nat.not_lt_zero _)
  | N + 1 => sim_step hc (simAt_all hc N)

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
  unfold ownedCheckWith at h
  split at h
  · rename_i G G' hG hG'
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq,
      List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨hne, hne'⟩, hsz⟩, hblk⟩ := h
    have hc : Checked outs L B B' G G' :=
      ⟨hG, hG', hsz.symm, fun k hk => ⟨(hblk k hk).1.symm, (hblk k hk).2⟩⟩
    have hwl : B.map Prod.fst ≠ [] := by simpa using hne
    have hwl' : B'.map Prod.fst ≠ [] := by simpa using hne'
    obtain ⟨h0, hs0⟩ := cfgOf_start_zero hG hwl
    obtain ⟨-, hs0'⟩ := cfgOf_start_zero hG' hwl'
    exact simAt_all hc _ fuel 0 s s t (Nat.lt_succ_self _) h0
      (Or.inl ⟨hpc.trans hs0.symm, hpc.trans hs0'.symm⟩)
      ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩ hfn hrun
  · cases h

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
  | .ref k => σ k

/-- The symbolic array `a` with each table entry `ref k` replaced by `σ k`. -/
def SArr.subst (σ : Nat → STerm) : SArr → SArr
  | .cell r => .cell r
  | .aset a w n i v => .aset (a.subst σ) w n (i.subst σ) (v.subst σ)
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

/-- The symbolic state `ss` under the substitution `σ`. -/
def SSt.subst (σ : Nat → STerm) (ss : SSt) : SSt :=
  ⟨fun r => (ss.regs r).subst σ, fun r => (ss.arrs r).subst σ, ss.zf.subst σ, ss.wr, ss.awr,
    ss.cf.subst σ, ss.of.subst σ⟩

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
  simp only [SSt.subst, SSt.setR, SSt.mk.injEq, and_true]
  funext r
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
    · exact symSh_subst σ x R
    · rfl

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
        SG.subst, STerm.subst]
      rfl
    · rw [← liftR_subst, ← symCast_subst]; rfl
  · split
    · simp only [SOut.subst, SSt.subst_setA, List.map_cons, List.map_nil,
        SG.subst, SArr.subst]
      rfl
    · rw [← liftR_subst, ← symCast_subst]; rfl
  · rfl
  · rfl
  · rw [← liftR_subst, ← symCast_subst]; rfl

theorem aluFlT_subst (σ : Nat → STerm) (i : LinstrRM) (ss : SSt) (ofl : Bool) :
    aluFlT i (ss.subst σ) ofl = (aluFlT i ss ofl).subst σ := by
  unfold aluFlT
  split
  · rw [show (ss.subst σ).regs = fun r => (ss.regs r).subst σ from rfl, symOp64_subst,
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
  rw [show (ss.subst σ).regs = fun r => (ss.regs r).subst σ from rfl, symOp64_subst,
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
  rw [show (ss.subst σ).regs = fun r => (ss.regs r).subst σ from rfl]
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
  · rw [show (ss.subst σ).regs = fun r => (ss.regs r).subst σ from rfl, symOp64_subst,
      symOp64_subst]
    cases symOp64 ss.regs _ <;> cases symOp64 ss.regs _ <;> simp [SOut.subst, List.map_append]
    rfl
  · split
    · simp only [SOut.subst, SSt.subst_setR, List.map_nil]; rfl
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

/-- **The symbolic run commutes with substitution.** -/
theorem symRun_subst (σ : Nat → STerm) :
    ∀ (is : List LinstrRM) (ss : SSt), symRun is (ss.subst σ) = (symRun is ss).subst σ
  | [], _ => rfl
  | i :: is, ss => by
      simp only [symRun, symStep_subst]
      cases symStep i ss with
      | ok ss1 g1 =>
          simp only [SOut.subst, symRun_subst σ is ss1]
          cases symRun is ss1 <;> simp
      | fail => rfl
      | unk => rfl

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
  | .ref k => decide (k < n)

/-- The array `a` reads only table entries below `n`. -/
def SArr.refsLt (n : Nat) : SArr → Bool
  | .cell _ => true
  | .aset a _ _ i v => a.refsLt n && i.refsLt n && v.refsLt n
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
  | .ref k => (E[k]?.map TEnt.vars).getD []

/-- The start registers the array `a` over the table `E` reads. -/
def SArr.varsT (E : Array TEnt) : SArr → List String
  | .cell _ => []
  | .aset a _ _ i v => a.varsT E ++ i.varsT E ++ v.varsT E
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
  | .ref k => (E[k]?.map TEnt.rf).getD true

/-- The array `a` over the table `E` reads the carry or the overflow flag at the start. -/
def SArr.readsFT (E : Array TEnt) : SArr → Bool
  | .cell _ => false
  | .aset a _ _ i v => a.readsFT E || i.readsFT E || v.readsFT E
end

/-- The width base of the word `t` over the table `E`. -/
def STerm.wbT (E : Array TEnt) : STerm → STerm
  | .immAt _ x => x.wbT E
  | .bin _ x _ => x.wbT E
  | .un _ x => x.wbT E
  | .shImm _ _ x => x.wbT E
  | .ref k => (E[k]?.map TEnt.wb).getD (.ref k)
  | .reg r => .reg r
  | .immW w n => .immW w n
  | .aget a w n i => .aget a w n i
  | .cin ofl => .cin ofl
  | .aluF op ofl x y o => .aluF op ofl x y o
  | .carryW op x y c => .carryW op x y c
  | .carryF op ofl x y c => .carryF op ofl x y c
  | .mulx hi x y => .mulx hi x y

/-- The width the width base of the word `t` over the table `E` fixes. -/
def STerm.wbkT (E : Array TEnt) : STerm → Option Nat
  | .immAt _ x => x.wbkT E
  | .bin _ x _ => x.wbkT E
  | .un _ x => x.wbkT E
  | .shImm _ _ x => x.wbkT E
  | .ref k => (E[k]?.map TEnt.wbk).getD none
  | .reg _ => none
  | .immW w _ => some w
  | .aget _ w _ _ => some w
  | .cin _ => some 1
  | .aluF .. => none
  | .carryW .. => some 64
  | .carryF .. => some 1
  | .mulx .. => some 64

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
    simp only [σ', if_neg (Nat.ne_of_lt hk)]
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
    rw [if_pos hn] at hx
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
      p.1.internRegs { ss with regs := fun r => if r = d then p.2 else ss.regs r } ds

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
      simp only [SSt.subst, SSt.mk.injEq, and_true]
      funext r
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

/-- The symbolic run of a list of instructions over the table `T`: after each step the
    registers it writes and the carry and overflow flags are interned. The result is the
    final table and the description `symRun` gives, with words over the table. -/
def tRun : List LinstrRM → SSt → Tbl → Tbl × SOut
  | [], ss, T => (T, .ok ss [])
  | i :: is, ss, T =>
      match symStep i ss with
      | .ok ss1 g1 =>
          let p := T.internSt ss1 (ss1.wr.take (ss1.wr.length - ss.wr.length))
          let r := tRun is p.2 p.1
          match r.2 with
          | .ok ss2 g2 => (r.1, .ok ss2 (g1 ++ g2))
          | .fail => (r.1, .fail)
          | .unk => (r.1, .unk)
      | .fail => (T, .fail)
      | .unk => (T, .unk)

theorem tRun_ext : ∀ (is : List LinstrRM) (ss : SSt) (T : Tbl), TExt T.ents (tRun is ss T).1.ents
  | [], _, T => TExt.refl T.ents
  | i :: is, ss, T => by
      simp only [tRun]
      split
      · rename_i ss1 _ _
        have := (Tbl.internSt_ext T ss1 (ss1.wr.take (ss1.wr.length - ss.wr.length))).trans
          (tRun_ext is (T.internSt ss1 (ss1.wr.take (ss1.wr.length - ss.wr.length))).2 _)
        split <;> exact this
      · exact TExt.refl _
      · exact TExt.refl _

theorem tRun_valid : ∀ (is : List LinstrRM) (ss : SSt) (T : Tbl), TValid T.ents →
    TValid (tRun is ss T).1.ents
  | [], _, _, hv => hv
  | i :: is, ss, T, hv => by
      simp only [tRun]
      split
      · rename_i ss1 _ _
        have := tRun_valid is (T.internSt ss1 (ss1.wr.take (ss1.wr.length - ss.wr.length))).2 _
          (Tbl.internSt_valid hv ss1 (ss1.wr.take (ss1.wr.length - ss.wr.length)))
        split <;> exact this
      · exact hv
      · exact hv

/-- **The shared run describes the symbolic run.** For every substitution that agrees with a
    table extending the final table of `tRun`, its description is the description `symRun`
    gives from the substituted start. -/
theorem tRun_subst {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E) :
    ∀ (is : List LinstrRM) (ss : SSt) (T : Tbl), TExt (tRun is ss T).1.ents E →
      (tRun is ss T).2.subst σ = symRun is (ss.subst σ)
  | [], _, _, _ => rfl
  | i :: is, ss, T, hx => by
      simp only [symRun, symStep_subst]
      simp only [tRun] at hx ⊢
      cases hs : symStep i ss with
      | ok ss1 g1 =>
          simp only [hs] at hx ⊢
          generalize hp : T.internSt ss1 (ss1.wr.take (ss1.wr.length - ss.wr.length)) = p at hx ⊢
          have hx' : TExt (tRun is p.2 p.1).1.ents E := by split at hx <;> exact hx
          have ih := tRun_subst h is _ _ hx'
          have e2 := Tbl.internSt_subst h T ss1 (ss1.wr.take (ss1.wr.length - ss.wr.length))
            (by rw [hp]; exact (tRun_ext is _ _).trans hx')
          rw [hp] at e2
          rw [e2] at ih
          simp only [SOut.subst]
          rw [← ih]
          generalize tRun is p.2 p.1 = r
          obtain ⟨T', o⟩ := r
          cases o <;> simp [SOut.subst]
      | fail => rfl
      | unk => rfl

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
  · split <;> rfl

/-- The guard check of `blockOk` over the table `E`. -/
def guardsT (E : Array TEnt) (n : List String × Bool) (gs gs' : List SG) : Bool :=
  (gs ++ gs').all (SG.refsLt E.size) &&
    (normGT E gs').all (fun g => (normGT E gs).contains g && okInGT E n g)

theorem guardsT_spec {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E)
    {n : List String × Bool} {gs gs' : List SG} (hg : guardsT E n gs gs' = true) :
    (normG (gs'.map (SG.subst σ))).all (fun g =>
      (normG (gs.map (SG.subst σ))).contains g && okIn n g.vars g.readsF) = true := by
  simp only [guardsT, Bool.and_eq_true, List.all_append] at hg
  obtain ⟨⟨hb, hb'⟩, hc⟩ := hg
  rw [← normGT_subst h gs hb, ← normGT_subst h gs' hb']
  simp only [List.all_eq_true, List.mem_map, Bool.and_eq_true, List.contains_iff_mem] at hc ⊢
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨⟨g, (hc g hg).1, rfl⟩, okInGT_spec h (hc g hg).2⟩

/-- The terminator check of `blockOk` over the table `E` (`termAgree`). -/
def termAgreeT (E : Array TEnt) (T : Term) (n : List String × Bool) (ss ss' : SSt) :
    Option LinstrRM → Option LinstrRM → Bool
  | some (.Lgoto (a, _), _), some (.Lgoto (b, _), _) =>
      match T with
      | .goto _ => a == b
      | _ => false
  | some (.Lcond c _, _), some (.Lcond c' _, _) =>
      match T with
      | .cond _ _ => symDec ss c == symDec ss' c' && okInDT E n (symDec ss c)
      | _ => false
  | _, _ =>
      match T with
      | .fall _ => true
      | _ => false

theorem termAgreeT_spec {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E) {T : Term}
    {n : List String × Bool} {ss ss' : SSt} {x y : Option LinstrRM}
    (ht : termAgreeT E T n ss ss' x y = true) :
    termAgree T n (ss.subst σ) (ss'.subst σ) x y = true := by
  unfold termAgreeT at ht
  unfold termAgree
  split at ht
  · exact ht
  · rename_i c _ _ c' _ _
    split at ht
    · simp only [Bool.and_eq_true, beq_iff_eq] at ht
      have hd := okInDT_spec h ht.2
      simp only [okIn, Bool.and_eq_true] at hd
      simp only [symDec_subst, ht.1, Bool.and_eq_true, beq_self_eq_true, true_and]
      rw [← ht.1]
      exact hd
    · cases ht
  · exact ht

/-- The exit check of `blockOk` over the table `E` (`exitAgree`). -/
def exitAgreeT (E : Array TEnt) (outs : List String) (L : Nat → List String × Bool)
    (n : List String × Bool) (T : Term) (ss ss' : SSt) : Bool :=
  T.succs.all (fun j =>
      (L j).1.all (fun r => ss.regs r == ss'.regs r && okInT E n (ss.regs r)) &&
        (!(L j).2 || (ss.zf == ss'.zf && okInFT E n ss.zf &&
          ss.cf == ss'.cf && okInT E n ss.cf &&
          ss.of == ss'.of && okInT E n ss.of))) &&
    (!T.halts || outs.all (fun r => ss.regs r == ss'.regs r && okInT E n (ss.regs r))) &&
    (ss.awr ++ ss'.awr).all (fun q => ss.arrs q == ss'.arrs q && okInAT E n (ss.arrs q))

theorem exitAgreeT_spec {σ : Nat → STerm} {E : Array TEnt} (h : TblOK σ E)
    {outs : List String} {L : Nat → List String × Bool} {n : List String × Bool} {T : Term}
    {ss ss' : SSt} (he : exitAgreeT E outs L n T ss ss' = true) :
    exitAgree outs L n T (ss.subst σ) (ss'.subst σ) = true := by
  simp only [exitAgreeT, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at he
  obtain ⟨⟨hs, hh⟩, ha⟩ := he
  simp only [exitAgree, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true']
  refine ⟨⟨fun j hj => ⟨fun r hr => ?_, ?_⟩, ?_⟩, fun q hq => ?_⟩
  · obtain ⟨e, o⟩ := (hs j hj).1 r hr
    exact ⟨by simp only [SSt.subst, e], okInT_spec h o⟩
  · rcases (hs j hj).2 with h0 | ⟨⟨⟨⟨⟨z1, z2⟩, c1⟩, c2⟩, o1⟩, o2⟩
    · exact Or.inl h0
    · exact Or.inr ⟨⟨⟨⟨⟨by simp only [SSt.subst, z1], okInFT_spec h z2⟩,
        by simp only [SSt.subst, c1]⟩, okInT_spec h c2⟩, by simp only [SSt.subst, o1]⟩,
        okInT_spec h o2⟩
  · rcases hh with h0 | ho
    · exact Or.inl h0
    · exact Or.inr fun r hr => ⟨by simp only [SSt.subst, (ho r hr).1], okInT_spec h (ho r hr).2⟩
  · have hq' : q ∈ ss.awr ++ ss'.awr := hq
    exact ⟨by simp only [SSt.subst, (ha q hq').1], okInAT_spec h (ha q hq').2⟩

/-- The shared runs of block `b` of `B` and block `b'` of `B'` with terminator `T`: the
    final table and the two descriptions over it. -/
def blockRuns (B B' : List LinstrRM) (b b' : Block) (T : Term) : Tbl × SOut × SOut :=
  let p := tRun (bodyAt B b T) SSt.start Tbl.empty
  let q := tRun (bodyAt B' b' T) SSt.start p.1
  (q.1, p.2, q.2)

/-- The check of block `k` from its shared runs `R` (`blockOk`). -/
def blockOkR (outs : List String) (L : Nat → List String × Bool) (k : Nat) (T : Term)
    (R : Tbl × SOut × SOut) (B B' : List LinstrRM) (b b' : Block) : Bool :=
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
                termAgreeT R.1.ents T (L k) ss ss' B[b.stop - 1]? B'[b'.stop - 1]? &&
                exitAgreeT R.1.ents outs L (L k) T ss ss'
          | _ => false

/-- **The shared check implies the check.** -/
theorem blockOkR_spec {outs : List String} {L : Nat → List String × Bool} {k : Nat}
    {T : Term} {B B' : List LinstrRM} {b b' : Block}
    (h : blockOkR outs L k T (blockRuns B B' b b' T) B B' b b' = true) :
    blockOk outs L k T B B' b b' = true := by
  have hv : TValid (blockRuns B B' b b' T).1.ents :=
    tRun_valid _ _ _ (tRun_valid _ _ _ tValid_empty)
  obtain ⟨⟨σ, hσ⟩, -⟩ := hv
  have e1 : symRun (bodyAt B b T) SSt.start = (blockRuns B B' b b' T).2.1.subst σ := by
    rw [← SSt.subst_start σ, ← tRun_subst hσ _ _ _ (tRun_ext _ _ _)]
    rfl
  have e2 : symRun (bodyAt B' b' T) SSt.start = (blockRuns B B' b b' T).2.2.subst σ := by
    rw [← SSt.subst_start σ, ← tRun_subst hσ _ _ _ (TExt.refl _)]
    rfl
  unfold blockOkR at h
  unfold blockOk
  split
  · rfl
  · rename_i hT
    have h' : (match (blockRuns B B' b b' T).2.1 with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          match (blockRuns B B' b b' T).2.2 with
          | .ok ss' gs' =>
              guardsT (blockRuns B B' b b' T).1.ents (L k) gs gs' &&
                termAgreeT (blockRuns B B' b b' T).1.ents T (L k) ss ss' B[b.stop - 1]?
                  B'[b'.stop - 1]? &&
                exitAgreeT (blockRuns B B' b b' T).1.ents outs L (L k) T ss ss'
          | _ => false) = true := by
      split at h
      · exact absurd rfl hT
      · exact h
    rw [e1, e2]
    revert h'
    generalize blockRuns B B' b b' T = R at hσ
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
            exact ⟨⟨guardsT_spec hσ hg, termAgreeT_spec hσ hta⟩, exitAgreeT_spec hσ hex⟩
        | fail => cases h'
        | unk => cases h'

/-! ## 16. Live sets -/

/-- The shared runs of the block pairs of `G` and `G'`. -/
def runsOf (B B' : List LinstrRM) (G G' : CFG) : Array (Tbl × SOut × SOut) :=
  (Array.range G.blocks.size).map fun k => blockRuns B B' (G.blk k) (G'.blk k) (G.blk k).term

/-- The checker for the live sets `L` over the shared runs `R` of the block pairs of `G` and
    `G'` (`ownedCheckWith`). -/
def ownedCheckWithR (outs : List String) (L : Nat → List String × Bool)
    (B B' : List LinstrRM) (G G' : CFG) (R : Array (Tbl × SOut × SOut)) : Bool :=
  !B.isEmpty && !B'.isEmpty && G.blocks.size == G'.blocks.size &&
    (List.range G.blocks.size).all (fun k =>
      (G.blk k).term == (G'.blk k).term &&
        match R[k]? with
        | some r => blockOkR outs L k (G.blk k).term r B B' (G.blk k) (G'.blk k)
        | none => false)

theorem ownedCheckWithR_spec {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} {G G' : CFG} (hG : cfgOf (B.map Prod.fst) = some G)
    (hG' : cfgOf (B'.map Prod.fst) = some G')
    (h : ownedCheckWithR outs L B B' G G' (runsOf B B' G G') = true) :
    ownedCheckWith outs L B B' = true := by
  unfold ownedCheckWith
  rw [hG, hG']
  simp only [ownedCheckWithR, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h ⊢
  obtain ⟨hne, hall⟩ := h
  refine ⟨hne, fun k hk => ?_⟩
  obtain ⟨ht, hb⟩ := hall k hk
  refine ⟨ht, ?_⟩
  have hR : (runsOf B B' G G')[k]? =
      some (blockRuns B B' (G.blk k) (G'.blk k) (G.blk k).term) := by
    simp [runsOf, hk]
  rw [hR] at hb
  exact blockOkR_spec hb

/-- The start registers and flags block `k` needs live for the checks of `blockOkR` to pass,
    from its shared runs `R`, given the live sets `L` of its successors. The result is a
    candidate only: `ownedCheckWith` checks the live sets it is given. -/
def blockNeed (outs : List String) (L : Nat → List String × Bool) (T : Term)
    (R : Tbl × SOut × SOut) (B : List LinstrRM) (b : Block) : List String × Bool :=
  match T with
  | .ret => ([], false)
  | _ =>
      let E := R.1.ents
      match R.2.1, R.2.2 with
      | .ok ss _, .ok ss' gs' =>
          let dec : Option SDec :=
            match T, B[b.stop - 1]? with
            | .cond _ _, some (.Lcond c _, _) => some (symDec ss c)
            | _, _ => none
          ((normGT E gs').flatMap (SG.varsT E) ++ (dec.map (SDec.varsT E)).getD [] ++
              T.succs.flatMap (fun j => (L j).1.flatMap (fun r => (ss.regs r).varsT E) ++
                (if (L j).2 then ss.zf.varsT E ++ ss.cf.varsT E ++ ss.of.varsT E else [])) ++
              (if T.halts then outs.flatMap (fun r => (ss.regs r).varsT E) else []) ++
              (ss.awr ++ ss'.awr).flatMap (fun q => (ss.arrs q).varsT E),
            (dec.map (SDec.readsInitT E)).getD false || (normGT E gs').any (SG.readsFT E) ||
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
    (R : Array (Tbl × SOut × SOut)) (L : Array (List String × Bool)) :
    Array (List String × Bool) :=
  (Array.range G.blocks.size).map fun k =>
    joinLive (L.getD k ([], false))
      (match R[k]? with
        | some r => blockNeed outs (fun j => L.getD j ([], false)) (G.blk k).term r B (G.blk k)
        | none => ([], false))

/-- The live-set iteration from the empty sets, stopped at a fixpoint or after `n`
    rounds. -/
def liveIter (outs : List String) (B : List LinstrRM) (G : CFG)
    (R : Array (Tbl × SOut × SOut)) :
    Nat → Array (List String × Bool) → Array (List String × Bool)
  | 0, L => L
  | n + 1, L =>
      let L' := liveRound outs B G R L
      if L'.map (fun p => (p.1.length, p.2)) == L.map (fun p => (p.1.length, p.2)) then L
      else liveIter outs B G R n L'

/-- **The checker.** Each block pair runs once over a shared term table (`runsOf`); the live
    sets are computed by `liveIter` and the runs checked by `ownedCheckWithR`. -/
def ownedCheckM (outs : List String) (B B' : List LinstrRM) : Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      let R := runsOf B B' G G'
      let L := liveIter outs B G R (4 * G.blocks.size + 64)
        (Array.replicate G.blocks.size ([], false))
      ownedCheckWithR outs (fun k => L.getD k ([], false)) B B' G G' R
  | _, _ => false

theorem ownedCheckM_with {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckM outs B B' = true) : ∃ L, ownedCheckWith outs L B B' = true := by
  unfold ownedCheckM at h
  cases hG : cfgOf (B.map Prod.fst) with
  | none => simp [hG] at h
  | some G =>
      cases hG' : cfgOf (B'.map Prod.fst) with
      | none => simp [hG, hG'] at h
      | some G' =>
          rw [hG, hG'] at h
          exact ⟨_, ownedCheckWithR_spec hG hG' h⟩

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

/-- The memory cells at the argument pointers `args` that the body `c` writes: the
    destination registers `mem.<a>.<off>`, `a ∈ args`, of its operations, without
    repetition. The array ABI keeps such a cell as a register of that name. -/
def memOuts (args : List String) (c : Lcmd) : List String :=
  (c.flatMap fun i =>
    match i.li_i with
    | .Lopn ds _ _ =>
        ds.filterMap fun
          | .reg d => if args.any (fun a => ("mem." ++ a ++ ".").isPrefixOf d) then some d else none
          | _ => none
    | _ => []).eraseDups

/-- The observed registers of a function: its result registers and the memory cells at its
    argument pointers that its body writes (`memOuts`). -/
def resOuts (f : Lfundef) : List String := f.lfd_res ++ memOuts f.lfd_arg f.lfd_body

theorem Obs.of_append {xs ys : List String} {t t' : LstateMF} (h : Obs (xs ++ ys) t t') :
    Obs xs t t' :=
  ⟨fun r hr => h.1 r (List.mem_append_left ys hr), h.2⟩

/-- The checker on the first functions of two programs, for a typing `ty` of function
    bodies: the functions have the same name, the rewritten body satisfies the printer's
    two-address precondition `TwoAddrLegalize.bodyTiedOk`, and `ownedCheckM` accepts the
    two typed bodies with the function's result registers and the memory cells its body
    writes at its argument pointers (`resOuts`) as the observed registers. -/
def ownedCheckTy (ty : Lcmd → List LinstrRM) (P P' : Lprog) : Bool :=
  match P.lp_funcs.head?, P'.lp_funcs.head? with
  | some (n, f), some (n', f') =>
      n == n' && TwoAddrLegalize.bodyTiedOk f'.lfd_body &&
        ownedCheckM (resOuts f) (ty f.lfd_body) (ty f'.lfd_body)
  | _, _ => false

/-- The checker with every instruction at the register tag and the trailing `Lret` dropped. -/
def ownedCheck (P P' : Lprog) : Bool :=
  ownedCheckTy (fun c => dropRet (typeBody (fun _ => .reg none) c)) P P'

/-- **Soundness of the program checker, with the memory results.** If `ownedCheckTy ty P P'`
    accepts, the first functions of `P` and `P'` have one name, the rewritten body satisfies
    `bodyTiedOk`, and every halting `lsemFuelMemF` run of the typed source body from pc `0`
    is matched by a halting run of the typed rewritten body from the same state, with end
    states that agree on the result registers, on the memory cells the source body writes at
    its argument pointers, on the arrays and on the word memory. -/
theorem ownedCheckTy_sound_mem {ty : Lcmd → List LinstrRM} {P P' : Lprog}
    (h : ownedCheckTy ty P P' = true) :
    ∃ n f f', P.lp_funcs.head? = some (n, f) ∧ P'.lp_funcs.head? = some (n, f') ∧
      TwoAddrLegalize.bodyTiedOk f'.lfd_body = true ∧
      ∀ (fn : String) (s t : LstateMF), s.prog.lfn = fn → s.prog.base.reg.lpc = 0 →
        ∀ fuel, lsemFuelMemF (singletonProgM fn (ty f.lfd_body)) fuel s = some t →
        ∃ fuel' t', lsemFuelMemF (singletonProgM fn (ty f'.lfd_body)) fuel' s = some t' ∧
          Obs (resOuts f) t t' := by
  unfold ownedCheckTy at h
  split at h
  · rename_i n f n' f' h1 h2
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hn, htied⟩, hchk⟩ := h
    subst hn
    exact ⟨n, f, f', h1, h2, htied, fun fn s t hfn hpc fuel hrun =>
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
  obtain ⟨n, f, f', h1, h2, htied, hsim⟩ := ownedCheckTy_sound_mem h
  refine ⟨n, f, f', h1, h2, htied, fun fn s t hfn hpc fuel hrun => ?_⟩
  obtain ⟨fuel', t', hrun', hobs⟩ := hsim fn s t hfn hpc fuel hrun
  exact ⟨fuel', t', hrun', hobs.of_append⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
