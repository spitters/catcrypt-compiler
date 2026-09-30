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
immediate shifts) with the carry and overflow flags `withALUFlags` writes, and the carry
family `ADC`, `SBB`, `ADCX`, `ADOX` of `carryStep`; the multiply arms, `SAR`, `CMOV`, the
casts and the compile-time-offset memory moves are `unk`. `symRun` composes the steps of a
list.

## The check

The two control-flow graphs (`AllocCheck.LcmdCFG.cfgOf`) must have the same number of
blocks and the same terminators. Each block pair is run symbolically from one symbolic
start state; the pair is accepted when the source block always fails or ends in `Lret`
(no halting run passes through it), or when every guard of the rewritten block is a guard
of the source block, two jumps name the same function, two branch conditions have the
same symbolic value, and at each exit the final symbolic states agree on the registers live
at the successor (on `outs` at an exit that leaves the body), on the zero, carry and
overflow flags when the flags are live, and on every array written, with every start
register these values read live at the block, and the flags live at the block when a value
reads a start flag. The live sets are computed by a fixpoint iteration (`liveIter`) and
checked, not trusted.

## Main definitions

* `STerm`, `SArr`, `SFlag`, `SG`, `SSt`, `Holds`: symbolic values, states and the states
  they describe.
* `symN`, `symSh`, `symMC`, `symCast`, `symMem`, `aluFl`, `symCarry`, `symStep`, `symRun`:
  the symbolic step layer by layer, and runs.
* `SDec`, `symDec`: the symbolic value of a branch condition.
* `blockOk`, `ownedCheckWith`, `ownedCheckM`: the checker.
* `typeBody`, `dropRet`, `ownedCheckTy`, `ownedCheck`: the checker on the first functions of
  two programs, with the two-address gate `TwoAddrLegalize.bodyTiedOk`.
* `Rel`, `Obs`: the agreement of two states at a block entry and at the end.

## Main results

* `symN_sound`, `symSh_sound`, `symMC_sound`, `symCast_sound`, `symMem_sound`,
  `aluFlT_sound`, `symCarry_sound`, `symStep_sound`: each layer of the step is described
  exactly.
* `symRun_sound`: the symbolic run describes the run of a list exactly.
* `fuel_runL`, `runL_fuel`: a run through straight-line instructions of a body.
* `decC_eq`: the symbolic branch condition describes the branch taken.
* `ownedCheckWith_sound`, `ownedCheckM_sound`, `ownedCheckTy_sound`: soundness of the
  checker.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (stackGet stackSet)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (lsemStepSh sarStruct? lsemStepSh_of_not_sar)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
  (lsemStepMC mulhiStruct? adcxStruct? adcxhiStruct? sbbStruct? sbbhiStruct?
   lsemStepMC_of_delegate)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
  (LinstrRT lsemStepCast castStruct? lsemStepCast_of_delegate)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminImmShiftMnem (immShiftMnem?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (x86_ADC x86_SBB x86_ADCX)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
  (lsemStepMem_of_carryArgs lsemStepMem_flags)

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
  /-- The two-source operation `m` of `applyOpnN` at the width of `x`. -/
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

/-- A symbolic array cell over the registers and arrays at the start of a block. -/
inductive SArr where
  /-- The cell of a name at the start. -/
  | cell (r : String)
  /-- The array `a` read at shape `(w, n)` with element `i` set to `v`. -/
  | aset (a : SArr) (w n : Nat) (i v : STerm)
end

deriving instance DecidableEq for STerm, SArr

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
  | .bin m x y => ⟨(x.ev).1, (applyOpnN (x.ev).1 m [(x.ev).2, castW y.ev (x.ev).1]).getD (x.ev).2⟩
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

theorem applyImmShiftN_some {w : Nat} {m : String} (h : shOk m = true) (k : Nat) (a : BitVec w) :
    (applyImmShiftN w m k a).isSome := by
  simp only [shOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | h <;> subst h <;> simp [applyImmShiftN, applyOpnN]

theorem applyImmShiftN_none {w : Nat} {m : String} (h : shOk m = false) (k : Nat)
    (a : BitVec w) : applyImmShiftN w m k a = none := by
  simp only [shOk, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  simp [applyImmShiftN, h.1.1, h.1.2, h.2]

/-- The symbolic description of `lsemStepN`. -/
def symN (x : LinstrR) (R : String → STerm) : ROut :=
  match x with
  | .Lopn [.reg _] opn [_, _, _] => if stripWidthTag opn = "CMOV" then .unk else .fail
  | .Lopn [.reg dst] opn [a, b] =>
      match a with
      | .reg ra =>
          if binOk (stripWidthTag opn) then
            match b with
            | .reg rb => .set dst (.bin (stripWidthTag opn) (R ra) (R rb)) [.eqW (R ra) (R rb)]
            | .imm n => .set dst (.bin (stripWidthTag opn) (R ra) (.immAt n (R ra))) []
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
        | some (m, k) => if shOk m then .set dst (.shImm m k (R a)) [] else .fail
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
      split_ifs with hb
      · split
        · rename_i rb
          simp only [ROut.Desc]
          rw [stepN_bin_reg, hr ra, hr rb]
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (applyOpnN_bin_some hb
            ((R ra).ev V A C O).2 (castW ((R rb).ev V A C O) ((R ra).ev V A C O).1))
          simp only [AllG, List.mem_singleton, forall_eq, SG.holds, STerm.ev, hv]
          split_ifs with hw
          · simp [hw]
          · simp [Ne.symm hw]
        · rename_i n
          simp only [ROut.Desc]
          rw [stepN_bin_imm, hr ra]
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (applyOpnN_bin_some hb
            ((R ra).ev V A C O).2 (BitVec.ofNat ((R ra).ev V A C O).1 n))
          simp [AllG, STerm.ev, hv]
        · rename_i hb1 hb2
          cases b with
          | reg rb => exact absurd rfl (hb1 rb)
          | imm n => exact absurd rfl (hb2 n)
          | arr _ _ => simp [ROut.Desc, lsemStepN, readReg, evalOperandN]
          | arrIdx _ _ _ => simp [ROut.Desc, lsemStepN, readReg, evalOperandN]
      · simp only [ROut.Desc]
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
        split_ifs with hs
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

/-- The symbolic description of `lsemStepMC`: the multiply and carry arms are outside the
    fragment. -/
def symMC (x : LinstrR) (R : String → STerm) : ROut :=
  match mulhiStruct? x, adcxStruct? x, adcxhiStruct? x, sbbStruct? x, sbbhiStruct? x with
  | none, none, none, none, none => symSh x R
  | _, _, _, _, _ => .unk

theorem symMC_sound (x : LinstrR) (R : String → STerm) : RSound (lsemStepMC x) R (symMC x R) := by
  intro V A C O r hr
  unfold symMC
  split
  · rename_i h1 h2 h3 h4 h5
    have := symSh_sound x R V A C O r hr
    simpa only [ROut.Desc, lsemStepMC_of_delegate x r h1 h2 h3 h4 h5] using this
  · trivial

/-- The symbolic description of `lsemStepCast`: a cast with a descriptor is outside the
    fragment. -/
def symCast (i : LinstrRT) (R : String → STerm) : ROut :=
  match castStruct? i.1 with
  | none => symMC i.1 R
  | some _ =>
      match i.2 with
      | none => symMC i.1 R
      | some _ => .unk

theorem symCast_sound (i : LinstrRT) (R : String → STerm) :
    RSound (lsemStepCast i) R (symCast i R) := by
  intro V A C O r hr
  unfold symCast
  split
  · rename_i h
    have := symMC_sound i.1 R V A C O r hr
    simpa only [ROut.Desc, lsemStepCast_of_delegate i r (Or.inl h)] using this
  · split
    · rename_i h
      have := symMC_sound i.1 R V A C O r hr
      simpa only [ROut.Desc, lsemStepCast_of_delegate i r (Or.inr h)] using this
    · trivial

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

/-- The symbolic carry flag (`ofl = false`) or overflow flag (`ofl = true`) after the memref
    step of `i` from `ss`: for a recognised arithmetic or logical operation whose sources are
    read at width `64`, the flag it writes (`STerm.aluF`); otherwise the flag of `ss`. -/
def aluFlT (i : LinstrRM) (ss : SSt) (ofl : Bool) : STerm :=
  match aluFlagOp? i with
  | some (op, a, b) =>
      match symOp64 ss.regs a, symOp64 ss.regs b with
      | some (ta, _), some (tb, _) => .aluF op ofl ta tb (if ofl then ss.of else ss.cf)
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

/-- The symbolic description of one instruction of `evalInstrPMemF`: the flag `CMP`, the
    register-copy `MOV`, a label, the carry family, and the memref step with the flags of
    `withALUFlags`; a branch and a jump are outside the fragment. -/
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
        simp only [h1, h2, e1, e2, STerm.ev]
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
            have he : evalInstrPMemF P i s =
                ((lsemStepMem i s.prog.base).map (withALUFlags i s.prog.base)).map
                  (fun b => { s with prog := { s.prog with base := b } }) := by
              simp only [evalInstrPMemF, hc, hm, hf, hL]
              cases lsemStepMem i s.prog.base <;> simp [hk]
            rw [he]
            exact descM_liftF i (symMem_zf i ss) hs
              (symMem_sound i ss V A C O s.prog.base ⟨hs.1, hs.2.1⟩)
              (fun b hb => lsemStepMem_flags hb)

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
      rw [evalInstrPMemF_delegate P _ s rfl rfl hf rfl rfl]
      simp only [evalInstrPMemL]
      split <;> simp

theorem evalInstrPMemF_goto (P : LprogM) (x : String) (l : LLabel) (tag : MemTag)
    (s : LstateMF) :
    evalInstrPMemF P (.Lgoto (x, l), tag) s =
      if x = P.lfn then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
      else none := by
  rw [evalInstrPMemF_delegate P _ s rfl rfl rfl rfl rfl]
  simp only [evalInstrPMemL]
  split <;> simp

theorem evalInstrPMemF_ret (P : LprogM) (tag : MemTag) (s : LstateMF) :
    evalInstrPMemF P (.Lret, tag) s = none := by
  rw [evalInstrPMemF_delegate P _ s rfl rfl rfl rfl rfl]
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
              gs'.all (fun g => gs.contains g && okIn (L k) g.vars g.readsF) &&
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
        (∀ g ∈ gs', g ∈ gs ∧ (∀ v ∈ g.vars, v ∈ (L k).1) ∧
          (g.readsF = true → (L k).2 = true)) ∧
        termAgree T (L k) ss ss' B[b.stop - 1]? B'[b'.stop - 1]? = true ∧
        exitAgree outs L (L k) T ss ss' = true := by
  have h2 : (match symRun (bodyAt B b T) SSt.start with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          match symRun (bodyAt B' b' T) SSt.start with
          | .ok ss' gs' =>
              gs'.all (fun g => gs.contains g && okIn (L k) g.vars g.readsF) &&
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
  have hAll' : AllG s'.prog.base.reg.lvm s.prog.base.larr s'.prog.base.cf s'.prog.base.of gs' :=
    fun g hg =>
      (SG.holds_congr _ g (fun r hr => (hV r ((hgs g hg).2.1 r hr)).symm)
        (fun e => by
          obtain ⟨-, hc, ho⟩ := hrel.2.2.2.2 ((hgs g hg).2.2 e)
          exact ⟨hc.symm, ho.symm⟩)).mp
      (hAll g (hgs g hg).1)
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

/-! ## 13. Live sets -/

/-- The start registers and flags block `k` needs live for the checks of `blockOk` to pass,
    given the live sets `L` of its successors. The result is a candidate only:
    `ownedCheckWith` checks the live sets it is given. -/
def blockNeed (outs : List String) (L : Nat → List String × Bool) (T : Term)
    (B B' : List LinstrRM) (b b' : Block) : List String × Bool :=
  match T with
  | .ret => ([], false)
  | _ =>
      match symRun (bodyAt B b T) SSt.start, symRun (bodyAt B' b' T) SSt.start with
      | .ok ss _, .ok ss' gs' =>
          let dec : Option SDec :=
            match T, B[b.stop - 1]? with
            | .cond _ _, some (.Lcond c _, _) => some (symDec ss c)
            | _, _ => none
          (gs'.flatMap SG.vars ++ (dec.map SDec.vars).getD [] ++
              T.succs.flatMap (fun j => (L j).1.flatMap (fun r => (ss.regs r).vars) ++
                (if (L j).2 then ss.zf.vars ++ ss.cf.vars ++ ss.of.vars else [])) ++
              (if T.halts then outs.flatMap (fun r => (ss.regs r).vars) else []) ++
              (ss.awr ++ ss'.awr).flatMap (fun q => (ss.arrs q).vars),
            (dec.map SDec.readsInit).getD false || gs'.any SG.readsF ||
              T.succs.any (fun j => (L j).1.any (fun r => (ss.regs r).readsF) ||
                ((L j).2 && (ss.zf.readsInit || ss.cf.readsF || ss.of.readsF))) ||
              (T.halts && outs.any (fun r => (ss.regs r).readsF)) ||
              (ss.awr ++ ss'.awr).any (fun q => (ss.arrs q).readsF))
      | _, _ => ([], false)

/-- `n` extended by the names and flag of `m`. -/
def joinLive (n m : List String × Bool) : List String × Bool :=
  (m.1.foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) n.1, n.2 || m.2)

/-- One round of the live-set iteration over the blocks of `G` and `G'`. -/
def liveRound (outs : List String) (B B' : List LinstrRM) (G G' : CFG)
    (L : Array (List String × Bool)) : Array (List String × Bool) :=
  (Array.range G.blocks.size).map fun k =>
    joinLive (L.getD k ([], false))
      (blockNeed outs (fun j => L.getD j ([], false)) (G.blk k).term B B' (G.blk k) (G'.blk k))

/-- The live-set iteration from the empty sets, stopped at a fixpoint or after `n`
    rounds. -/
def liveIter (outs : List String) (B B' : List LinstrRM) (G G' : CFG) :
    Nat → Array (List String × Bool) → Array (List String × Bool)
  | 0, L => L
  | n + 1, L =>
      let L' := liveRound outs B B' G G' L
      if L'.map (fun p => (p.1.length, p.2)) == L.map (fun p => (p.1.length, p.2)) then L
      else liveIter outs B B' G G' n L'

/-- **The checker.** The live sets are computed by `liveIter` and checked by
    `ownedCheckWith`. -/
def ownedCheckM (outs : List String) (B B' : List LinstrRM) : Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      let L := liveIter outs B B' G G' (4 * G.blocks.size + 64)
        (Array.replicate G.blocks.size ([], false))
      ownedCheckWith outs (fun k => L.getD k ([], false)) B B'
  | _, _ => false

theorem ownedCheckM_with {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckM outs B B' = true) : ∃ L, ownedCheckWith outs L B B' = true := by
  unfold ownedCheckM at h
  split at h
  · exact ⟨_, h⟩
  · cases h

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

/-! ## 14. Programs -/

/-- A body typed instruction by instruction with the memory tag `tag`. -/
def typeBody (tag : LinstrR → MemTag) (c : Lcmd) : List LinstrRM :=
  c.map fun i => (i.li_i, tag i.li_i)

/-- A typed body without its trailing `Lret`: `lsemFuelMemF` takes no step at `Lret`, so a
    halting run of a body leaves it by falling off its end. -/
def dropRet (c : List LinstrRM) : List LinstrRM :=
  match c.getLast? with
  | some (.Lret, _) => c.dropLast
  | _ => c

/-- The checker on the first functions of two programs, for a typing `ty` of function
    bodies: the functions have the same name, the rewritten body satisfies the printer's
    two-address precondition `TwoAddrLegalize.bodyTiedOk`, and `ownedCheckM` accepts the
    two typed bodies with the function's result registers as the observed registers. -/
def ownedCheckTy (ty : Lcmd → List LinstrRM) (P P' : Lprog) : Bool :=
  match P.lp_funcs.head?, P'.lp_funcs.head? with
  | some (n, f), some (n', f') =>
      n == n' && TwoAddrLegalize.bodyTiedOk f'.lfd_body &&
        ownedCheckM f.lfd_res (ty f.lfd_body) (ty f'.lfd_body)
  | _, _ => false

/-- The checker with every instruction at the register tag and the trailing `Lret` dropped. -/
def ownedCheck (P P' : Lprog) : Bool :=
  ownedCheckTy (fun c => dropRet (typeBody (fun _ => .reg none) c)) P P'

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
  unfold ownedCheckTy at h
  split at h
  · rename_i n f n' f' h1 h2
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hn, htied⟩, hchk⟩ := h
    subst hn
    exact ⟨n, f, f', h1, h2, htied, fun fn s t hfn hpc fuel hrun =>
      ownedCheckM_sound hchk fn s t hfn hpc fuel hrun⟩
  · cases h

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
