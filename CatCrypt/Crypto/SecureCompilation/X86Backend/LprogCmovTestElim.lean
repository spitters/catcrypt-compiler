/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate

/-!
# Shared condition tests for runs of conditional moves on Lprog bodies

An opt-in `Lprog → Lprog` pass over the owned-RA linear body
(`JasminLprogExport.Lcmd`). `JasminOp.select 64` exports to
`Lopn [d] CMOV:64 [c, t, f]` (`d := c ≠ 0 ? t : f`), which
`LprogAsmPrinter.renderLopn` prints as

    mov f, d ; test c, c ; cmovne t, d

(the `mov` is dropped when `f = d`; when `d = t` the pair is
`test c, c ; cmove f, d`). A run of such selects on one condition register
re-tests the condition at every select. The pass rewrites each eligible `CMOV`
into the printer's two-address forms `Lopn [c] TEST:64 [c, c]` (`testq`),
`Lopn [d] MOV:64 [f]` (`movq`) and `Lopn [d] CMOVNE:64 [d, t]` /
`Lopn [d] CMOVE:64 [d, f]` (`cmovneq` / `cmoveq`), and emits the `TEST` only
when the zero flag does not already hold the test of `c`.

## The rewrite

A `CMOV:64` is eligible when its destination `d`, condition `c` and the two
data operands `t`, `f` are pool registers (`LcmdCopyPropagate.isPhysGP`) and
`d ≠ c`. The sweep carries the register whose zero test the flag holds:

* at an eligible `CMOV`, it emits `TEST c, c` unless the carried register is
  `c`, then `CMOVE d, f` when `d = t`, and otherwise `MOV d, f` (omitted when
  `d = f`) followed by `CMOVNE d, t`; the carried register becomes `c`;
* at a flag-silent instruction (`isFlagSilent`: the move, load, store and
  `lea` opcodes) with one register destination other than the carried
  register, the carried register is kept;
* at every other instruction (a flag writer, a label, control flow, or a write
  of the carried register) the carried register is dropped.

The pass is meant to run last, on the body the printer receives: the emitted
`TEST` names `c` as its nominal destination, as `CmovSelectEmit.test64L` does.

## Semantics

`JasminLsem.lsemStraight` has no flags, and `applyOpn` has no `TEST` or
`CMOVcc` arm. The preservation theorem is stated over `fsem`, the extension of
`lsemStep` by a zero flag `zf : Option Bool` held outside the register file
(`none` when the flag is not known), in the manner of
`JasminLsemMemFlagGuard.LstateMF`:

* `CMOV:64 [c, t, f]` writes `c ≠ 0 ? t : f` and sets `zf := (c = 0)`, the
  effect of its printed text;
* `TEST:64 [a, b]` sets `zf := (a &&& b = 0)` and writes no register;
* `CMP:64 [a, b]` sets `zf := (a = b)` and writes no register;
* `CMOVNE:64 [d, s]` / `CMOVE:64 [d, s]` read `zf`, and are stuck when it is
  unknown;
* every other instruction is `lsemStep`; a flag-silent opcode keeps `zf`, any
  other instruction sets it to unknown.

`lsemStep` reads the condition's low bit (`selectW (BitVec.setWidth 1 c)`), the
printed text tests the whole register. The two agree when the condition holds
`0` or `1`, the value a `reg 1` condition carries (`fstep_cmov_lsem`).

## Main results

* `cmovTestElimBody`, `cmovTestElimFundef`, `cmovTestElimLprog`: the pass.
* `fstep`, `fsem`, `fview`: the flag-extended step, its fold, and the observed
  state (register map, memory, zero flag; the program counter excluded).
* `fstep_st_of_plain`, `fstep_cmov_lsem`: `fstep` is `lsemStep` on every
  instruction other than `CMOV:64`, `TEST:64`, `CMP:64`, `CMOVNE:64`, `CMOVE:64`, and on
  a `CMOV:64` whose condition holds `0` or `1`.
* `cmovTestElimBody_fview`, `cmovTestElimFundef_fview`: the pass preserves the
  observed state of `fsem` on every body and every start state.
* `cmpFuseBody`, `cmpFuseFundef`: the fusion of a materialised comparison
  `SETE:64`/`SETNE:64` with the selects on its result into one `CMP:64` and
  two-address conditional moves (§8); `fstep` gives `CMP:64 [a, b]` the effect
  `zf := (a = b)`.
* `selectW_setWidth_cmpBit`: on the `0`/`1` word of a comparison result the
  low-bit read of `lsemStep` and the whole-word test of the printed text select
  the same operand.
* `cmpFuseBody_sound`, `cmpFuseFundef_sound`: the fused body and the original
  are both stuck under `fsem` or finish with equal memory and equal live-out
  registers.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCmovTestElim

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (selectW JasminCmp cmpBit)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (isPhysGP lsemStep_reg_nonmem physGPs instrUses fullDefsOf operandReads LiveAgree
   evalOperand_liveAgree lsemStep_liveAgree contains_instrUses_of_src lsemStep_isSome_indep)

/-! ## 1. Mnemonics and instruction shapes -/

/-- The 64-bit conditional move `JasminOp.select 64` exports to
    (`withWidthTag 64 "CMOV"`). -/
def cmovMn : String := "CMOV:64"

/-- The 64-bit flag-only `test`. -/
def testMn : String := "TEST:64"

/-- The 64-bit two-address `cmovne`. -/
def cmovneMn : String := "CMOVNE:64"

/-- The 64-bit two-address `cmove`. -/
def cmoveMn : String := "CMOVE:64"

/-- The 64-bit register move. -/
def movMn : String := "MOV:64"

/-- `Lopn [d] CMOV:64 [c, t, f]`: the destination and the condition, true and
    false operands. -/
def cmovArgs? : LinstrR → Option (String × LOperand × LOperand × LOperand)
  | .Lopn [.reg d] opn [c, t, f] => if opn = cmovMn then some (d, c, t, f) else none
  | _ => none

/-- `Lopn [_] TEST:64 [a, b]`: the two tested operands. -/
def testArgs? : LinstrR → Option (LOperand × LOperand)
  | .Lopn [.reg _] opn [a, b] => if opn = testMn then some (a, b) else none
  | _ => none

/-- The 64-bit flag-only `cmp`. -/
def cmpMn : String := "CMP:64"

/-- `Lopn [_] CMP:64 [a, b]`: the two compared operands. -/
def cmpArgs? : LinstrR → Option (LOperand × LOperand)
  | .Lopn [.reg _] opn [a, b] => if opn = cmpMn then some (a, b) else none
  | _ => none

/-- `Lopn [d] CMOVNE:64 [a, b]` (sense `true`) or `Lopn [d] CMOVE:64 [a, b]`
    (sense `false`): the sense, the destination and the two operands. -/
def cmovccArgs? : LinstrR → Option (Bool × String × LOperand × LOperand)
  | .Lopn [.reg d] opn [a, b] =>
      if opn = cmovneMn then some (true, d, a, b)
      else if opn = cmoveMn then some (false, d, a, b) else none
  | _ => none

/-- The opcodes whose printed form writes no flag: the register and memory
    moves, the loads and stores, and `lea`. -/
def isFlagSilent (opn : String) : Bool :=
  match stripWidthTag opn with
  | "MOV" | "MOVQ" | "MOV:8" | "MOV:16" | "LOAD" | "LOADIDX" | "STORE" | "STOREIDX"
  | "LEA" => true
  | _ => false

/-- An instruction whose printed form writes no flag. -/
def flagSilentInstr : LinstrR → Bool
  | .Lopn _ opn _ => isFlagSilent opn
  | _ => false

/-! ## 2. The flag-extended step -/

/-- A linear-machine state with a zero flag, `none` when the flag is not
    known. -/
structure FState (w : Nat) where
  /-- The linear-machine state. -/
  st : Lstate w
  /-- The zero flag. -/
  zf : Option Bool

/-- The observed part of a flag-extended state: register map, memory and zero
    flag. -/
def fview {w : Nat} (x : FState w) :
    ((String → BitVec w) × (String → Int → BitVec w)) × Option Bool :=
  (stateStore x.st, x.zf)

/-- The flag-extended step: the printed semantics of `CMOV:64`, `TEST:64`,
    `CMP:64`, `CMOVNE:64` and `CMOVE:64`, and `lsemStep` on every other instruction with
    the zero flag kept by a flag-silent opcode and unknown after any other. -/
def fstep {w : Nat} (i : LinstrR) (x : FState w) : Option (FState w) :=
  match cmovArgs? i with
  | some (d, c, t, f) =>
      let cv := evalOperand x.st c
      some ⟨(x.st.setReg d (if cv = 0 then evalOperand x.st f else evalOperand x.st t)).nextPc,
        some (decide (cv = 0))⟩
  | none =>
  match testArgs? i with
  | some (a, b) =>
      some ⟨x.st.nextPc, some (decide ((evalOperand x.st a &&& evalOperand x.st b) = 0))⟩
  | none =>
  match cmpArgs? i with
  | some (a, b) =>
      some ⟨x.st.nextPc, some (decide (evalOperand x.st a = evalOperand x.st b))⟩
  | none =>
  match cmovccArgs? i with
  | some (ne, d, a, b) =>
      match x.zf with
      | some z =>
          some ⟨(x.st.setReg d (if z = ne then evalOperand x.st a else evalOperand x.st b)).nextPc,
            some z⟩
      | none => none
  | none => (lsemStep i x.st).map fun s' => ⟨s', if flagSilentInstr i then x.zf else none⟩

/-- The fold of `fstep` over a straight-line body. -/
def fsem {w : Nat} : List LinstrR → FState w → Option (FState w)
  | [], x => some x
  | i :: is, x =>
      match fstep i x with
      | some x' => fsem is x'
      | none => none

/-! ## 3. The pass -/

/-- The `CMOV:64` instructions the pass rewrites: destination, condition and
    both data operands are pool registers, and the destination is not the
    condition. -/
def elig (i : LinstrR) : Option (String × String × String × String) :=
  match cmovArgs? i with
  | some (d, .reg c, .reg t, .reg f) =>
      if isPhysGP d && isPhysGP c && isPhysGP t && isPhysGP f && d != c then
        some (d, c, t, f)
      else none
  | _ => none

/-- `TEST:64 c, c`, printed `testq c, c`. -/
def testL (ii : Nat) (c : String) : Linstr := ⟨ii, .Lopn [.reg c] testMn [.reg c, .reg c]⟩

/-- `MOV:64 d, f`, printed `movq f, d`. -/
def movL (ii : Nat) (d f : String) : Linstr := ⟨ii, .Lopn [.reg d] movMn [.reg f]⟩

/-- A two-address conditional move `Lopn [d] mn [d, s]`, printed
    `cmov<cc>q s, d`. -/
def cmovccL (ii : Nat) (mn d s : String) : Linstr := ⟨ii, .Lopn [.reg d] mn [.reg d, .reg s]⟩

/-- The replacement of one eligible `CMOV:64 [c, t, f]` into `d`, given the
    register whose zero test the flag holds. -/
def cmovRewrite (ii : Nat) (cur : Option String) (d c t f : String) : Lcmd :=
  (if cur = some c then [] else [testL ii c]) ++
    (if d = t then [cmovccL ii cmoveMn d f]
     else (if d = f then [] else [movL ii d f]) ++ [cmovccL ii cmovneMn d t])

/-- The register whose zero test the flag holds after an instruction that the
    pass keeps: kept across a flag-silent single-register write of another
    register, dropped otherwise. -/
def nextCur (cur : Option String) (i : LinstrR) : Option String :=
  match cur, i with
  | some c, .Lopn [.reg x] opn _ => if isFlagSilent opn && x != c then some c else none
  | _, _ => none

/-- The sweep, carrying the register whose zero test the flag holds. -/
def elimGo : Option String → Lcmd → Lcmd
  | _, [] => []
  | cur, k :: rest =>
      match elig k.li_i with
      | some (d, c, t, f) => cmovRewrite k.li_ii cur d c t f ++ elimGo (some c) rest
      | none => k :: elimGo (nextCur cur k.li_i) rest

/-- The pass on one body, from an unknown flag. -/
def cmovTestElimBody (body : Lcmd) : Lcmd := elimGo none body

/-- The pass on one `Lfundef` (body only). -/
def cmovTestElimFundef (f : Lfundef) : Lfundef :=
  { f with lfd_body := cmovTestElimBody f.lfd_body }

/-- The pass on every function body of an `Lprog`. -/
def cmovTestElimLprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map fun (n, f) => (n, cmovTestElimFundef f) }

/-! ## 4. Mnemonic facts -/

theorem testMn_ne_cmovMn : testMn ≠ cmovMn := by decide +kernel
theorem cmovneMn_ne_cmovMn : cmovneMn ≠ cmovMn := by decide +kernel
theorem cmoveMn_ne_cmovMn : cmoveMn ≠ cmovMn := by decide +kernel
theorem cmoveMn_ne_testMn : cmoveMn ≠ testMn := by decide +kernel
theorem cmovneMn_ne_testMn : cmovneMn ≠ testMn := by decide +kernel
theorem cmoveMn_ne_cmovneMn : cmoveMn ≠ cmovneMn := by decide +kernel
theorem movMn_ne_LOADIDX : movMn ≠ "LOADIDX" := by decide +kernel
theorem movMn_ne_STOREIDX : movMn ≠ "STOREIDX" := by decide +kernel
theorem cmovMn_ne_LOADIDX : cmovMn ≠ "LOADIDX" := by decide +kernel
theorem cmovMn_ne_STOREIDX : cmovMn ≠ "STOREIDX" := by decide +kernel
theorem stripWidthTag_movMn : stripWidthTag movMn = "MOV" := by decide +kernel
theorem stripWidthTag_cmovMn : stripWidthTag cmovMn = "CMOV" := by decide +kernel
theorem isFlagSilent_movMn : isFlagSilent movMn = true := by decide +kernel
theorem isFlagSilent_cmovMn : isFlagSilent cmovMn = false := by decide +kernel
theorem isFlagSilent_testMn : isFlagSilent testMn = false := by decide +kernel
theorem isFlagSilent_cmovneMn : isFlagSilent cmovneMn = false := by decide +kernel
theorem isFlagSilent_cmoveMn : isFlagSilent cmoveMn = false := by decide +kernel
theorem isFlagSilent_cmpMn : isFlagSilent cmpMn = false := by decide +kernel
theorem cmpMn_ne_cmovMn : cmpMn ≠ cmovMn := by decide +kernel
theorem cmpMn_ne_testMn : cmpMn ≠ testMn := by decide +kernel
theorem cmovneMn_ne_cmpMn : cmovneMn ≠ cmpMn := by decide +kernel
theorem cmoveMn_ne_cmpMn : cmoveMn ≠ cmpMn := by decide +kernel

/-! ## 5. The flag-extended step and `lsemStep` -/

/-- Operand evaluation reads only the register map and memory. -/
theorem evalOperand_congr {w : Nat} {s t : Lstate w} (hv : s.lvm = t.lvm)
    (hm : s.lmem = t.lmem) (o : LOperand) : evalOperand s o = evalOperand t o := by
  cases o <;> simp [evalOperand, hv, hm]

/-- On every instruction other than `CMOV:64`, `TEST:64`, `CMP:64`, `CMOVNE:64`
    and `CMOVE:64`, the linear-machine part of `fstep` is `lsemStep`. -/
theorem fstep_st_of_plain {w : Nat} (i : LinstrR) (x : FState w)
    (h1 : cmovArgs? i = none) (h2 : testArgs? i = none) (h3 : cmovccArgs? i = none)
    (h4 : cmpArgs? i = none) :
    Option.map FState.st (fstep i x) = lsemStep i x.st := by
  simp only [fstep, h1, h2, h3, h4]
  cases lsemStep i x.st <;> rfl

/-- On a condition word holding `0` or `1`, the low-bit select of `lsemStep`'s
    `CMOV` arm is the whole-word test of the printed `test; cmovne`. -/
theorem selectW_setWidth_of_lt_two {w : Nat} (c a b : BitVec w) (hc : c.toNat < 2) :
    selectW (BitVec.setWidth 1 c) a b = if c = 0 then b else a := by
  unfold selectW
  have key : (BitVec.setWidth 1 c = 1#1) ↔ ¬ c = 0 := by
    simp only [BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show BitVec.toNat (0 : BitVec w) = 0 from rfl]
    omega
  by_cases h0 : c = 0
  · rw [if_pos h0, if_neg (fun h => (key.mp h) h0)]
  · rw [if_neg h0, if_pos (key.mpr h0)]

/-- **`fstep` agrees with `lsemStep` on a `CMOV:64` with a `0`/`1`
    condition.** The store image of the flag-extended step equals that of
    `lsemStep`. -/
theorem fstep_cmov_lsem {w : Nat} (d : String) (c t f : LOperand) (x : FState w)
    (hc : (evalOperand x.st c).toNat < 2) :
    Option.map (fun y => stateStore y.st) (fstep (.Lopn [.reg d] cmovMn [c, t, f]) x)
      = Option.map stateStore (lsemStep (.Lopn [.reg d] cmovMn [c, t, f]) x.st) := by
  rw [lsemStep_reg_nonmem d cmovMn [c, t, f] x.st ⟨cmovMn_ne_LOADIDX, cmovMn_ne_STOREIDX⟩]
  simp only [fstep, cmovArgs?, ↓reduceIte, stripWidthTag_cmovMn, List.map, applyOpn_select,
    selectW_setWidth_of_lt_two _ _ _ hc, Option.map_some]

/-- The step reads and writes the observed state only. -/
theorem fstep_congr {w : Nat} (i : LinstrR) {x y : FState w} (h : fview x = fview y) :
    Option.map fview (fstep i x) = Option.map fview (fstep i y) := by
  obtain ⟨⟨hv, hm⟩, hz⟩ : (x.st.lvm = y.st.lvm ∧ x.st.lmem = y.st.lmem) ∧ x.zf = y.zf := by
    simpa [fview, stateStore] using h
  have he := evalOperand_congr hv hm
  unfold fstep
  split
  · simp [fview, stateStore, Lstate.setReg, he, hv, hm]
  · split
    · simp [fview, stateStore, he, hm, hv]
    · split
      · simp [fview, stateStore, he, hm, hv]
      · split
        · rw [hz]
          split
          · simp [fview, stateStore, Lstate.setReg, he, hv, hm]
          · rfl
        · have hs := lsemStep_stateStore i (s := x.st) (t := y.st) (by simp [stateStore, hv, hm])
          rw [hz]
          cases h1 : lsemStep i x.st <;> cases h2 : lsemStep i y.st <;> simp_all [fview]

/-- The fold reads and writes the observed state only. -/
theorem fsem_congr {w : Nat} :
    ∀ (b : List LinstrR) {x y : FState w}, fview x = fview y →
      Option.map fview (fsem b x) = Option.map fview (fsem b y)
  | [], x, y, h => by simp [fsem, h]
  | i :: is, x, y, h => by
      have hs := fstep_congr i h
      simp only [fsem]
      cases h1 : fstep i x <;> cases h2 : fstep i y <;> rw [h1, h2] at hs <;>
        simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hs
      exact fsem_congr is hs

/-- The fold over a concatenation. -/
theorem fsem_append {w : Nat} :
    ∀ (a b : List LinstrR) (x : FState w), fsem (a ++ b) x = (fsem a x).bind (fsem b)
  | [], b, x => rfl
  | i :: is, b, x => by
      simp only [List.cons_append, fsem]
      cases fstep i x with
      | none => rfl
      | some x' => exact fsem_append is b x'

/-! ## 6. One rewrite -/

/-- The flag holds the zero test of the carried register. -/
def CurOk {w : Nat} (cur : Option String) (x : FState w) : Prop :=
  ∀ c, cur = some c → x.zf = some (decide (x.st.lvm c = 0))

/-- `CMOV:64` over three registers in the flag-extended step. -/
theorem fstep_cmov_reg {w : Nat} (d c t f : String) (x : FState w) :
    fstep (.Lopn [.reg d] cmovMn [.reg c, .reg t, .reg f]) x =
      some ⟨(x.st.setReg d (if x.st.lvm c = 0 then x.st.lvm f else x.st.lvm t)).nextPc,
        some (decide (x.st.lvm c = 0))⟩ := rfl

/-- `CMOV:64` over three operands in the flag-extended step. -/
theorem fstep_cmov {w : Nat} (d : String) (c t f : LOperand) (x : FState w) :
    fstep (.Lopn [.reg d] cmovMn [c, t, f]) x =
      some ⟨(x.st.setReg d (if evalOperand x.st c = 0 then evalOperand x.st f
          else evalOperand x.st t)).nextPc, some (decide (evalOperand x.st c = 0))⟩ := rfl

/-- `TEST:64` in the flag-extended step. -/
theorem fstep_test {w : Nat} (d : String) (a b : LOperand) (x : FState w) :
    fstep (.Lopn [.reg d] testMn [a, b]) x =
      some ⟨x.st.nextPc, some (decide ((evalOperand x.st a &&& evalOperand x.st b) = 0))⟩ := by
  simp [fstep, cmovArgs?, testArgs?]

/-- `CMP:64` in the flag-extended step. -/
theorem fstep_cmp {w : Nat} (d : String) (a b : LOperand) (x : FState w) :
    fstep (.Lopn [.reg d] cmpMn [a, b]) x =
      some ⟨x.st.nextPc, some (decide (evalOperand x.st a = evalOperand x.st b))⟩ := by
  simp [fstep, cmovArgs?, testArgs?, cmpArgs?, cmpMn_ne_testMn]

/-- The optional `TEST c, c` of a rewrite leaves the store unchanged and
    leaves the zero test of `c` in the flag. -/
theorem fsem_testPart {w : Nat} (ii : Nat) (cur : Option String) (c : String)
    (x : FState w) (hok : CurOk cur x) :
    ∃ x0 : FState w,
      fsem ((if cur = some c then [] else [testL ii c]).map Linstr.li_i) x = some x0 ∧
      x0.st.lvm = x.st.lvm ∧ x0.st.lmem = x.st.lmem ∧
      x0.zf = some (decide (x.st.lvm c = 0)) := by
  split
  · exact ⟨x, rfl, rfl, rfl, hok c (by assumption)⟩
  · refine ⟨⟨x.st.nextPc, some (decide ((x.st.lvm c &&& x.st.lvm c) = 0))⟩, ?_, rfl, rfl,
      by simp⟩
    simp [fsem, fstep, testL, cmovArgs?, testArgs?, evalOperand]

/-- The move-and-conditional-move part of a rewrite, from a known flag `z`,
    writes `z ? f : t` to `d` and nothing else. -/
theorem fsem_cmovPart {w : Nat} (ii : Nat) (d t f : String) (x0 : FState w) (z : Bool)
    (hz : x0.zf = some z) :
    ∃ x1 : FState w,
      fsem ((if d = t then [cmovccL ii cmoveMn d f]
        else (if d = f then [] else [movL ii d f]) ++ [cmovccL ii cmovneMn d t]).map
          Linstr.li_i) x0 = some x1 ∧
      x1.st.lvm = (fun r => if r = d then (if z then x0.st.lvm f else x0.st.lvm t)
        else x0.st.lvm r) ∧
      x1.st.lmem = x0.st.lmem ∧ x1.zf = some z := by
  by_cases hdt : d = t
  · subst hdt
    refine ⟨⟨(x0.st.setReg d (if z then x0.st.lvm f else x0.st.lvm d)).nextPc, some z⟩,
      ?_, ?_, rfl, rfl⟩
    · cases z <;> simp [fsem, fstep, cmovccL, cmovArgs?, testArgs?, cmpArgs?, cmovccArgs?, hz,
        cmoveMn_ne_testMn, cmoveMn_ne_cmpMn, cmoveMn_ne_cmovneMn, evalOperand]
    · funext r; simp [Lstate.setReg]
  · rw [if_neg hdt]
    by_cases hdf : d = f
    · subst hdf
      refine ⟨⟨(x0.st.setReg d (if z then x0.st.lvm d else x0.st.lvm t)).nextPc, some z⟩,
        ?_, ?_, rfl, rfl⟩
      · cases z <;> simp [fsem, fstep, cmovccL, cmovArgs?, testArgs?, cmpArgs?, cmovccArgs?, hz,
          cmovneMn_ne_testMn, cmovneMn_ne_cmpMn, evalOperand]
      · funext r; simp [Lstate.setReg]
    · refine ⟨⟨((x0.st.setReg d (x0.st.lvm f)).nextPc.setReg d
          (if z then x0.st.lvm f else x0.st.lvm t)).nextPc, some z⟩, ?_, ?_, rfl, rfl⟩
      · cases z <;> simp [fsem, fstep, movL, cmovccL, cmovArgs?, testArgs?, cmpArgs?,
          cmovccArgs?, hz, cmovneMn_ne_testMn, cmovneMn_ne_cmpMn, evalOperand, lsemStep,
          applyOpn, stripWidthTag_movMn,
          flagSilentInstr, isFlagSilent_movMn, hdf, Ne.symm hdt]
      · funext r; by_cases hr : r = d <;> simp [Lstate.setReg, hr]

/-- **One rewrite preserves the observed state.** From a state whose flag holds
    the zero test of the carried register, the replacement of
    `CMOV:64 [c, t, f]` into `d ≠ c` reaches the observed state of the `CMOV`,
    and leaves the zero test of `c` in the flag. -/
theorem cmovRewrite_fsem {w : Nat} (ii : Nat) (cur : Option String) (d c t f : String)
    (hdc : d ≠ c) (x : FState w) (hok : CurOk cur x) :
    ∃ x1 : FState w,
      fsem ((cmovRewrite ii cur d c t f).map Linstr.li_i) x = some x1 ∧
      Option.map fview (some x1)
        = Option.map fview (fstep (.Lopn [.reg d] cmovMn [.reg c, .reg t, .reg f]) x) ∧
      CurOk (some c) x1 := by
  obtain ⟨x0, h0, hv0, hm0, hz0⟩ := fsem_testPart ii cur c x hok
  obtain ⟨x1, h1, hv1, hm1, hz1⟩ := fsem_cmovPart ii d t f x0 _ hz0
  refine ⟨x1, ?_, ?_, ?_⟩
  · rw [cmovRewrite, List.map_append, fsem_append, h0, Option.bind_some, h1]
  · rw [fstep_cmov_reg]
    simp only [Option.map_some, fview, stateStore, hv1, hm1, hz1, hv0, hm0,
      Lstate.lvm_nextPc, Lstate.lmem_nextPc, Lstate.lvm_setReg, decide_eq_true_eq]
    rfl
  · intro c' hc'
    cases hc'
    rw [hz1, hv1]
    simp only [if_neg (Ne.symm hdc), hv0]

/-! ## 7. The sweep -/

/-- `cmovArgs?` recognises exactly the `CMOV:64` shape. -/
theorem cmovArgs?_spec {i : LinstrR} {d : String} {c t f : LOperand}
    (h : cmovArgs? i = some (d, c, t, f)) : i = .Lopn [.reg d] cmovMn [c, t, f] := by
  unfold cmovArgs? at h
  split at h
  · split_ifs at h with hop
    cases h
    rw [hop]
  · cases h

/-- `elig` recognises a `CMOV:64` over pool registers whose destination is not
    its condition. -/
theorem elig_spec {i : LinstrR} {d c t f : String} (h : elig i = some (d, c, t, f)) :
    i = .Lopn [.reg d] cmovMn [.reg c, .reg t, .reg f] ∧ d ≠ c := by
  unfold elig at h
  split at h
  · rename_i d' c' t' f' hc
    split_ifs at h with hg
    cases h
    refine ⟨cmovArgs?_spec hc, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hg
    exact hg.2
  · cases h

/-- A flag-silent opcode is none of the five flag opcodes. -/
theorem flagArgs_none_of_silent {ds : List LOperand} {opn : String} {srcs : List LOperand}
    (hs : isFlagSilent opn = true) :
    cmovArgs? (.Lopn ds opn srcs) = none ∧ testArgs? (.Lopn ds opn srcs) = none ∧
      cmovccArgs? (.Lopn ds opn srcs) = none ∧ cmpArgs? (.Lopn ds opn srcs) = none := by
  have h1 : opn ≠ cmovMn := fun h => by rw [h, isFlagSilent_cmovMn] at hs; cases hs
  have h2 : opn ≠ testMn := fun h => by rw [h, isFlagSilent_testMn] at hs; cases hs
  have h3 : opn ≠ cmovneMn := fun h => by rw [h, isFlagSilent_cmovneMn] at hs; cases hs
  have h4 : opn ≠ cmoveMn := fun h => by rw [h, isFlagSilent_cmoveMn] at hs; cases hs
  have h5 : opn ≠ cmpMn := fun h => by rw [h, isFlagSilent_cmpMn] at hs; cases hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cmovArgs?; split <;> simp_all
  · unfold testArgs?; split <;> simp_all
  · unfold cmovccArgs?; split <;> simp_all
  · unfold cmpArgs?; split <;> simp_all

/-- A step of `Lopn [.reg x] opn srcs` leaves every other register unchanged. -/
theorem lsemStep_lvm_of_ne {w : Nat} {x opn : String} {srcs : List LOperand}
    {s s' : Lstate w} {c : String} (h : lsemStep (.Lopn [.reg x] opn srcs) s = some s')
    (hne : c ≠ x) : s'.lvm c = s.lvm c := by
  rcases srcs with _ | ⟨o, rest⟩
  · simp only [lsemStep] at h
    split at h
    · cases h; simp [Lstate.setReg, hne]
    · cases h
  · cases o with
    | arrIdx base idx scale =>
      simp only [lsemStep] at h
      split_ifs at h
      · cases h; simp [Lstate.setReg, hne]
      · split at h
        · cases h; rfl
        · cases h
      · split at h
        · cases h; simp [Lstate.setReg, hne]
        · cases h
    | _ =>
      simp only [lsemStep] at h
      split at h
      · cases h; simp [Lstate.setReg, hne]
      · cases h

/-- The carried register stays correct across an instruction the sweep keeps. -/
theorem curOk_nextCur {w : Nat} {cur : Option String} {i : LinstrR} {x x' : FState w}
    (hok : CurOk cur x) (hs : fstep i x = some x') : CurOk (nextCur cur i) x' := by
  intro c hc
  unfold nextCur at hc
  split at hc
  · rename_i c0 xr opn srcs
    split_ifs at hc with hsil
    cases hc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hsil
    obtain ⟨hA, hB, hC, hD⟩ :=
      flagArgs_none_of_silent (ds := [.reg xr]) (srcs := srcs) hsil.1
    simp only [fstep, hA, hB, hC, hD, flagSilentInstr, hsil.1, if_true] at hs
    cases hl : lsemStep (.Lopn [.reg xr] opn srcs) x.st with
    | none => rw [hl] at hs; cases hs
    | some s' =>
      rw [hl] at hs
      cases hs
      show x.zf = some (decide (s'.lvm c = 0))
      rw [lsemStep_lvm_of_ne hl (Ne.symm hsil.2)]
      exact hok c rfl
  · cases hc

/-- The sweep preserves the observed state of `fsem` from every state whose flag
    holds the zero test of the carried register. -/
theorem elimGo_fview {w : Nat} :
    ∀ (body : Lcmd) (cur : Option String) (x : FState w), CurOk cur x →
      Option.map fview (fsem ((elimGo cur body).map Linstr.li_i) x)
        = Option.map fview (fsem (body.map Linstr.li_i) x)
  | [], _, _, _ => rfl
  | k :: rest, cur, x, hok => by
      cases he : elig k.li_i with
      | some q =>
          obtain ⟨d, c, t, f⟩ := q
          obtain ⟨hk, hdc⟩ := elig_spec he
          obtain ⟨x1, h1, hv1, hok1⟩ := cmovRewrite_fsem k.li_ii cur d c t f hdc x hok
          simp only [elimGo, he, List.map_append, fsem_append, h1, Option.bind_some,
            List.map_cons]
          rw [elimGo_fview rest (some c) x1 hok1]
          simp only [fsem, hk]
          cases h2 : fstep (.Lopn [.reg d] cmovMn [.reg c, .reg t, .reg f]) x with
          | none => rw [h2] at hv1; cases hv1
          | some x2 =>
              rw [h2] at hv1
              exact fsem_congr _ (Option.some.inj hv1)
      | none =>
          simp only [elimGo, he, List.map_cons, fsem]
          cases hs : fstep k.li_i x with
          | none => rfl
          | some x' => exact elimGo_fview rest _ x' (curOk_nextCur hok hs)

/-- **The pass preserves the observed state.** On every body and every start
    state, the rewritten body reaches the register map, memory and zero flag
    the original body reaches under `fsem`, and gets stuck exactly when the
    original does. -/
theorem cmovTestElimBody_fview {w : Nat} (body : Lcmd) (x : FState w) :
    Option.map fview (fsem ((cmovTestElimBody body).map Linstr.li_i) x)
      = Option.map fview (fsem (body.map Linstr.li_i) x) :=
  elimGo_fview body none x (fun _ h => by cases h)

/-- The pass on one `Lfundef` preserves the observed state of its body. -/
theorem cmovTestElimFundef_fview {w : Nat} (f : Lfundef) (x : FState w) :
    Option.map fview (fsem ((cmovTestElimFundef f).lfd_body.map Linstr.li_i) x)
      = Option.map fview (fsem (f.lfd_body.map Linstr.li_i) x) :=
  cmovTestElimBody_fview f.lfd_body x

/-! ## 8. Compare-and-select fusion

`JasminOp.cmp` and `JasminOp.cmpImm` at width 64 export to the materialised
comparison `Lopn [b] SET<cc>:64 [x, y]` (`b := x <cc> y ? 1 : 0`), printed
`cmp y, x ; mov $0, b ; set<cc> b`. When `b` only feeds selects,
`cmpFuseBody` replaces the comparison by the flag-only `Lopn [x] CMP:64 [x, y]`
(`cmpq y, x`) and each `Lopn [d] CMOV:64 [b, t, f]` by the two-address moves
reading that flag, so `b` is never materialised. The fusion covers the two
zero-flag conditions `SETE:64` and `SETNE:64`.

The rewritten body leaves `b` with its old value, so the two bodies are related
by `LcmdCopyPropagate.LiveAgree L`, agreement on memory and on the registers of
`L`. The sweep `fuseGo` carries `L`, whether the two zero flags are equal, and
the comparison whose flag the rewritten body holds. It keeps an instruction only
when every register it reads is in `L` and, where the flags differ, it reads no
flag; it fails otherwise, and at the end of the body when a register of
`liveOut` is outside `L`. `cmpFuseBody` returns the body unchanged on failure.
`worthScan` is the lookahead that declines a comparison whose result is read
after the run of selects. -/

/-- The 64-bit materialised equality comparison (`withWidthTag 64 "SETE"`). -/
def seteMn : String := "SETE:64"

/-- The 64-bit materialised disequality comparison (`withWidthTag 64 "SETNE"`). -/
def setneMn : String := "SETNE:64"

/-- `Lopn [b] SETNE:64 [x, y]` (sense `true`) or `Lopn [b] SETE:64 [x, y]`
    (sense `false`): the sense, the destination and the compared operands. -/
def cmpHead? : LinstrR → Option (Bool × String × LOperand × LOperand)
  | .Lopn [.reg b] opn [x, y] =>
      if opn = setneMn then some (true, b, x, y)
      else if opn = seteMn then some (false, b, x, y) else none
  | _ => none

/-- The mnemonic of a sense. -/
def headMn (ne : Bool) : String := if ne then setneMn else seteMn

/-- The condition code of a sense. -/
def headCode (ne : Bool) : JasminCmp := if ne then .ne else .eq

/-- A second compared operand the fusion accepts: a pool register of `L` or an
    immediate. -/
def yOk (L : List String) : LOperand → Bool
  | .reg y => isPhysGP y && L.contains y
  | .imm _ => true
  | _ => false

/-- An eligible select on the boolean `b` whose data operands are not `b`:
    destination, true operand, false operand. -/
def selOn (b : String) (i : LinstrR) : Option (String × String × String) :=
  match elig i with
  | some (d, c, t, f) => if c == b && t != b && f != b then some (d, t, f) else none
  | none => none

/-- Lookahead for a comparison into `b`: no instruction after it reads `b`
    before `b` is fully rewritten or the body ends with `b` outside `liveOut`,
    other than selects on `b` reached through flag-silent instructions. -/
def worthScan (liveOut : List String) (b : String) : Bool → Lcmd → Bool
  | _, [] => !liveOut.contains b
  | inRun, k :: rest =>
      if inRun && (selOn b k.li_i).isSome then worthScan liveOut b true rest
      else
        match k.li_i with
        | .Lopn dsts opn srcs =>
            if (instrUses dsts opn srcs).contains b then false
            else if (fullDefsOf dsts opn).contains b then true
            else worthScan liveOut b (inRun && isFlagSilent opn) rest
        | _ => false

/-- A comparison the fusion replaces: a `SETE:64`/`SETNE:64` into a pool
    register `b` of a pool register `x` of `L` against an operand `yOk` accepts,
    passing the lookahead. -/
def fuseHead (liveOut L : List String) (i : LinstrR) (rest : Lcmd) :
    Option (Bool × String × String × LOperand) :=
  match cmpHead? i with
  | some (ne, b, .reg x, y) =>
      if isPhysGP b && isPhysGP x && L.contains x && yOk L y
          && worthScan liveOut b true rest then some (ne, b, x, y)
      else none
  | _ => none

/-- A select on the carried boolean whose data operands are in `L`. -/
def runSel (L : List String) (cur : Option (String × Bool)) (i : LinstrR) :
    Option (String × Bool × String × String × String) :=
  match cur with
  | some (b, ne) =>
      match selOn b i with
      | some (d, t, f) => if L.contains t && L.contains f then some (b, ne, d, t, f) else none
      | none => none
  | none => none

/-- `CMP:64 x, y`, printed `cmpq y, x`. -/
def cmpL (ii : Nat) (x : String) (y : LOperand) : Linstr :=
  ⟨ii, .Lopn [.reg x] cmpMn [.reg x, y]⟩

/-- The moves writing `z ? f : t` to `d` from a zero flag `z`. -/
def cmovPartL (ii : Nat) (d t f : String) : Lcmd :=
  if d = t then [cmovccL ii cmoveMn d f]
  else (if d = f then [] else [movL ii d f]) ++ [cmovccL ii cmovneMn d t]

/-- The replacement of a select `d := b ? t : f` on a fused comparison of sense
    `ne`. The flag holds equality of the compared words. -/
def selParts (ii : Nat) (ne : Bool) (d t f : String) : Lcmd :=
  if ne then cmovPartL ii d t f else cmovPartL ii d f t

/-- An instruction the sweep may keep: every register it reads is in `L`, and
    it reads no flag unless the flags are equal. -/
def keepOk (L : List String) (fl : Bool) (i : LinstrR) : Bool :=
  match i with
  | .Lopn dsts opn srcs =>
      (instrUses dsts opn srcs).all L.contains && (fl || (cmovccArgs? i).isNone)
  | _ => true

/-- The agreement set after a kept instruction: a full register write adds its
    destination. -/
def nextL (L : List String) (i : LinstrR) : List String :=
  match i with
  | .Lopn [.reg dst] opn _ =>
      if (testArgs? i).isSome || (cmpArgs? i).isSome
          || (fullDefsOf [.reg dst] opn).isEmpty then L
      else dst :: L
  | _ => L

/-- The carried comparison after a kept instruction: kept across a flag-silent
    single-register write of another register. -/
def nextFuseCur (cur : Option (String × Bool)) (i : LinstrR) : Option (String × Bool) :=
  match cur, i with
  | some (b, ne), .Lopn [.reg x] opn _ =>
      if isFlagSilent opn && x != b then some (b, ne) else none
  | _, _ => none

/-- The fusion sweep. `none` when an instruction that must be kept reads a
    register outside `L` or a flag that differs, or when the body ends with a
    register of `liveOut` outside `L`. -/
def fuseGo (liveOut : List String) :
    List String → Bool → Option (String × Bool) → Lcmd → Option Lcmd
  | L, _, _, [] => if liveOut.all L.contains then some [] else none
  | L, fl, cur, k :: rest =>
      match runSel L cur k.li_i with
      | some (_, ne, d, t, f) =>
          (fuseGo liveOut (d :: L) false cur rest).map (selParts k.li_ii ne d t f ++ ·)
      | none =>
        match fuseHead liveOut L k.li_i rest with
        | some (ne, b, x, y) =>
            (fuseGo liveOut (L.filter (· != b)) false (some (b, ne)) rest).map
              (cmpL k.li_ii x y :: ·)
        | none =>
          if keepOk L fl k.li_i then
            (fuseGo liveOut (nextL L k.li_i) (fl || !flagSilentInstr k.li_i)
              (nextFuseCur cur k.li_i) rest).map (k :: ·)
          else none

/-- The fusion on one body, for the registers `liveOut` read after it. The body
    is returned unchanged when the sweep fails. -/
def cmpFuseBody (liveOut : List String) (body : Lcmd) : Lcmd :=
  (fuseGo liveOut physGPs true none body).getD body

/-- The fusion on one `Lfundef` (body only). -/
def cmpFuseFundef (liveOut : List String) (f : Lfundef) : Lfundef :=
  { f with lfd_body := cmpFuseBody liveOut f.lfd_body }

/-! ### The condition word of a comparison -/

/-- **A select on a comparison result reads the same condition from the low bit
    and from the whole register.** `lsemStep`'s `CMOV` arm reads the low bit of
    the condition word, the printed `test; cmovne` tests the whole word; on the
    `0`/`1` word a materialised comparison writes they select the same operand. -/
theorem selectW_setWidth_cmpBit {w v : Nat} (c : JasminCmp) (x y : BitVec v)
    (a b : BitVec w) :
    selectW (BitVec.setWidth 1 (BitVec.setWidth w (cmpBit c x y))) a b
      = if BitVec.setWidth w (cmpBit c x y) = 0 then b else a :=
  selectW_setWidth_of_lt_two _ _ _ (setWidth_cmpBit_lt_two c x y)

/-- The whole-word zero test of a comparison result selects by the relation. -/
theorem ite_setWidth_cmpBit {w v : Nat} (c : JasminCmp) (x y : BitVec v) (T F : BitVec w) :
    (if BitVec.setWidth w (cmpBit c x y) = 0 then F else T)
      = if c.holds x y then T else F := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [Subsingleton.elim T F]; simp
  · unfold cmpBit
    cases c.holds x y
    · simp
    · have h1 : BitVec.setWidth w 1#1 ≠ 0#w := by
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
        have h2 : 2 ≤ 2 ^ w := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
        rw [Nat.mod_eq_of_lt (by omega : 1 % 2 ^ 1 < 2 ^ w)] at this
        simp at this
      simp [h1]

/-! ### The simulation relation -/

/-- The original state `o` and the rewritten state `n` agree on memory and on
    the registers of `L`, and on the zero flag when `fl` holds. -/
def Sim {w : Nat} (L : List String) (fl : Bool) (o n : FState w) : Prop :=
  LiveAgree L o.st n.st ∧ (fl = true → n.zf = o.zf)

/-- The carried comparison: the original state holds its result in `b`, the
    rewritten state holds equality of the compared words in the zero flag. -/
def Fact {w : Nat} (cur : Option (String × Bool)) (o n : FState w) : Prop :=
  ∀ b ne, cur = some (b, ne) → ∃ vx vy : BitVec w,
    o.st.lvm b = BitVec.setWidth w (cmpBit (headCode ne) vx vy) ∧
    n.zf = some (decide (vx = vy))

/-- The relation of two runs: both stuck, or both finished in states agreeing on
    memory and on the registers of `liveOut`. -/
def FinalRel {w : Nat} (liveOut : List String) :
    Option (FState w) → Option (FState w) → Prop
  | some o, some n => LiveAgree liveOut o.st n.st
  | none, none => True
  | _, _ => False

theorem FinalRel.refl {w : Nat} (liveOut : List String) (r : Option (FState w)) :
    FinalRel liveOut r r := by
  cases r with
  | none => trivial
  | some o => exact LiveAgree.refl _ _

/-- `LiveAgree` on a larger set gives it on a smaller one. -/
theorem LiveAgree.mono {w : Nat} {L L' : List String} {s t : Lstate w}
    (h : LiveAgree L s t) (hsub : ∀ r, L'.contains r = true → L.contains r = true) :
    LiveAgree L' s t :=
  ⟨h.1, fun r hr => h.2 r (hr.imp id (hsub r))⟩

/-- The same write to `d` on both sides adds `d` to the agreement set. -/
theorem LiveAgree.setReg_both {w : Nat} {L : List String} {s t : Lstate w}
    (h : LiveAgree L s t) (d : String) (v : BitVec w) :
    LiveAgree (d :: L) (s.setReg d v).nextPc (t.setReg d v).nextPc := by
  refine ⟨h.1, fun r hr => ?_⟩
  simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
  by_cases hrd : r = d
  · simp [hrd]
  · simp only [if_neg hrd]
    refine h.2 r (hr.imp id fun hc => ?_)
    simpa [List.contains_cons, hrd] using hc

/-- A write to a pool register `b` on one side only removes `b` from the
    agreement set. -/
theorem LiveAgree.setReg_left {w : Nat} {L : List String} {s t : Lstate w}
    (h : LiveAgree L s t) {b : String} (hb : isPhysGP b = true) (v : BitVec w) :
    LiveAgree (L.filter (· != b)) (s.setReg b v).nextPc t.nextPc := by
  refine ⟨h.1, fun r hr => ?_⟩
  simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
  have hrb : r ≠ b := by
    rintro rfl
    rcases hr with hr | hr
    · rw [hb] at hr; cases hr
    · simp at hr
  rw [if_neg hrb]
  refine h.2 r (hr.imp id fun hc => ?_)
  simp only [List.contains_eq_mem, List.mem_filter, decide_eq_true_eq] at hc ⊢
  exact hc.1

/-! ### One fused comparison and one fused select -/

theorem setneMn_facts :
    setneMn ≠ testMn ∧ setneMn ≠ cmpMn ∧ setneMn ≠ cmovneMn ∧ setneMn ≠ cmoveMn ∧
      isFlagSilent setneMn = false ∧ stripWidthTag setneMn = "SETNE" := by decide +kernel

theorem seteMn_facts :
    seteMn ≠ testMn ∧ seteMn ≠ cmpMn ∧ seteMn ≠ cmovneMn ∧ seteMn ≠ cmoveMn ∧
      isFlagSilent seteMn = false ∧ stripWidthTag seteMn = "SETE" := by decide +kernel

/-- The materialised comparison in the flag-extended step: it writes the
    comparison bit to `b` and leaves the flag unknown. -/
theorem fstep_head {w : Nat} (ne : Bool) (b x : String) (y : LOperand) (o : FState w) :
    fstep (.Lopn [.reg b] (headMn ne) [.reg x, y]) o =
      some ⟨(o.st.setReg b (BitVec.setWidth w
        (cmpBit (headCode ne) (o.st.lvm x) (evalOperand o.st y)))).nextPc, none⟩ := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := setneMn_facts
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := seteMn_facts
  cases ne <;>
    simp [fstep, headMn, headCode, cmovArgs?, testArgs?, cmpArgs?, cmovccArgs?, lsemStep,
      flagSilentInstr, evalOperand, applyOpn, *]

/-- The flag-only comparison in the flag-extended step. -/
theorem fstep_cmpL {w : Nat} (ii : Nat) (x : String) (y : LOperand) (n : FState w) :
    fstep (cmpL ii x y).li_i n =
      some ⟨n.st.nextPc, some (decide (n.st.lvm x = evalOperand n.st y))⟩ := by
  simp [fstep, cmpL, cmovArgs?, testArgs?, cmpArgs?, cmpMn_ne_testMn, evalOperand]

/-- `cmpHead?` recognises exactly the two materialised comparisons. -/
theorem cmpHead?_spec {i : LinstrR} {ne : Bool} {b : String} {x y : LOperand}
    (h : cmpHead? i = some (ne, b, x, y)) : i = .Lopn [.reg b] (headMn ne) [x, y] := by
  unfold cmpHead? at h
  split at h
  · split_ifs at h with h1 h2
    · cases h; rw [h1]; rfl
    · cases h; rw [h2]; rfl
  · cases h

/-- An operand `yOk` accepts evaluates equally in two `LiveAgree` states. -/
theorem evalOperand_yOk {w : Nat} {L : List String} {s t : Lstate w}
    (h : LiveAgree L s t) {y : LOperand} (hy : yOk L y = true) :
    evalOperand s y = evalOperand t y := by
  cases y with
  | reg r =>
    simp only [yOk, Bool.and_eq_true] at hy
    exact h.2 r (Or.inr hy.2)
  | imm _ => rfl
  | arr _ _ => simp [yOk] at hy
  | arrIdx _ _ _ => simp [yOk] at hy

/-- `fuseHead` recognises a materialised comparison of a register of `L`. -/
theorem fuseHead_spec {liveOut L : List String} {i : LinstrR} {rest : Lcmd} {ne : Bool}
    {b x : String} {y : LOperand} (h : fuseHead liveOut L i rest = some (ne, b, x, y)) :
    i = .Lopn [.reg b] (headMn ne) [.reg x, y] ∧ isPhysGP b = true ∧
      L.contains x = true ∧ yOk L y = true := by
  unfold fuseHead at h
  split at h
  · rename_i ne' b' x' y' hc
    split_ifs at h with hg
    cases h
    simp only [Bool.and_eq_true] at hg
    exact ⟨cmpHead?_spec hc, hg.1.1.1.1, hg.1.1.2, hg.1.2⟩
  · cases h

/-- **The fused comparison.** The original body writes the comparison bit to
    `b`; the rewritten body sets the zero flag by `CMP:64`. -/
theorem head_step {w : Nat} {L : List String} {fl : Bool} {o n : FState w}
    (hs : Sim L fl o n) (ii : Nat) (ne : Bool) {b x : String} {y : LOperand}
    (hb : isPhysGP b = true) (hx : L.contains x = true) (hy : yOk L y = true) :
    ∃ o' n', fstep (.Lopn [.reg b] (headMn ne) [.reg x, y]) o = some o' ∧
      fstep (cmpL ii x y).li_i n = some n' ∧
      Sim (L.filter (· != b)) false o' n' ∧ Fact (some (b, ne)) o' n' := by
  refine ⟨_, _, fstep_head ne b x y o, fstep_cmpL ii x y n, ⟨?_, fun h => by cases h⟩, ?_⟩
  · exact LiveAgree.setReg_left hs.1 hb _
  · intro b' ne' hc
    cases hc
    refine ⟨o.st.lvm x, evalOperand o.st y, by simp [Lstate.setReg], ?_⟩
    rw [hs.1.2 x (Or.inr hx), evalOperand_yOk hs.1 hy]

/-- `runSel` recognises a select on the carried boolean over registers of `L`. -/
theorem runSel_spec {L : List String} {cur : Option (String × Bool)} {i : LinstrR}
    {b : String} {ne : Bool} {d t f : String}
    (h : runSel L cur i = some (b, ne, d, t, f)) :
    cur = some (b, ne) ∧ i = .Lopn [.reg d] cmovMn [.reg b, .reg t, .reg f] ∧ d ≠ b ∧
      L.contains t = true ∧ L.contains f = true := by
  unfold runSel at h
  split at h
  · rename_i b' ne'
    split at h
    · rename_i d' t' f' hsel
      split_ifs at h with hg
      cases h
      simp only [Bool.and_eq_true] at hg
      unfold selOn at hsel
      split at hsel
      · rename_i d'' c'' t'' f'' he
        split_ifs at hsel with hg2
        cases hsel
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hg2
        obtain ⟨hk, hdc⟩ := elig_spec he
        obtain ⟨⟨rfl, _⟩, _⟩ := hg2
        exact ⟨rfl, hk, hdc, hg.1, hg.2⟩
      · cases hsel
    · cases h
  · cases h

/-- **The fused select.** From a carried comparison, the replacement of
    `CMOV:64 [b, t, f]` into `d ≠ b` writes the word the select writes. -/
theorem sel_step {w : Nat} {L : List String} {fl : Bool} {o n : FState w}
    (hs : Sim L fl o n) (ii : Nat) {b : String} {ne : Bool} {d t f : String}
    (hf : Fact (some (b, ne)) o n) (hdb : d ≠ b)
    (ht : L.contains t = true) (hfL : L.contains f = true) :
    ∃ o' n', fstep (.Lopn [.reg d] cmovMn [.reg b, .reg t, .reg f]) o = some o' ∧
      fsem ((selParts ii ne d t f).map Linstr.li_i) n = some n' ∧
      Sim (d :: L) false o' n' ∧ Fact (some (b, ne)) o' n' := by
  obtain ⟨vx, vy, hbv, hz⟩ := hf b ne rfl
  have htv := hs.1.2 t (Or.inr ht)
  have hfv := hs.1.2 f (Or.inr hfL)
  have key : ∀ (t' f' : String) (V : BitVec w),
      (if o.st.lvm b = 0 then o.st.lvm f else o.st.lvm t) = V →
      V = (if decide (vx = vy) then n.st.lvm f' else n.st.lvm t') →
      ∃ o' n', fstep (.Lopn [.reg d] cmovMn [.reg b, .reg t, .reg f]) o = some o' ∧
        fsem ((cmovPartL ii d t' f').map Linstr.li_i) n = some n' ∧
        Sim (d :: L) false o' n' ∧ Fact (some (b, ne)) o' n' := by
    intro t' f' V hV hV'
    obtain ⟨n1, h1, hv1, hm1, hz1⟩ := fsem_cmovPart ii d t' f' n _ hz
    refine ⟨_, n1, fstep_cmov_reg d b t f o, h1, ⟨⟨?_, fun r hr => ?_⟩, fun h => by cases h⟩, ?_⟩
    · exact hs.1.1.trans hm1.symm
    · simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg, hv1, hV, hV']
      by_cases hrd : r = d
      · simp [hrd]
      · simp only [if_neg hrd]
        refine hs.1.2 r (hr.imp id fun hc => ?_)
        simpa [List.contains_cons, hrd] using hc
    · intro b' ne' hc
      cases hc
      exact ⟨vx, vy, by simp [Lstate.setReg, Ne.symm hdb, hbv], hz1⟩
  cases ne with
  | true =>
    refine key t f _ rfl ?_
    rw [hbv, ite_setWidth_cmpBit, ← htv, ← hfv]
    by_cases h : vx = vy <;> simp [headCode, JasminCmp.holds, h]
  | false =>
    refine key f t _ rfl ?_
    rw [hbv, ite_setWidth_cmpBit, ← htv, ← hfv]
    by_cases h : vx = vy <;> simp [headCode, JasminCmp.holds, h]

/-! ### Kept instructions -/

/-- `testArgs?` recognises exactly the `TEST:64` shape. -/
theorem testArgs?_spec {i : LinstrR} {a b : LOperand} (h : testArgs? i = some (a, b)) :
    ∃ d, i = .Lopn [.reg d] testMn [a, b] := by
  unfold testArgs? at h
  split at h
  · split_ifs at h with hop
    cases h
    exact ⟨_, by rw [hop]⟩
  · cases h

/-- `cmpArgs?` recognises exactly the `CMP:64` shape. -/
theorem cmpArgs?_spec {i : LinstrR} {a b : LOperand} (h : cmpArgs? i = some (a, b)) :
    ∃ d, i = .Lopn [.reg d] cmpMn [a, b] := by
  unfold cmpArgs? at h
  split at h
  · split_ifs at h with hop
    cases h
    exact ⟨_, by rw [hop]⟩
  · cases h

/-- `cmovccArgs?` recognises a two-source instruction into one register. -/
theorem cmovccArgs?_spec {i : LinstrR} {ne : Bool} {d : String} {a b : LOperand}
    (h : cmovccArgs? i = some (ne, d, a, b)) : ∃ mn, i = .Lopn [.reg d] mn [a, b] := by
  unfold cmovccArgs? at h
  split at h
  · split_ifs at h <;> cases h <;> exact ⟨_, rfl⟩
  · cases h

/-- The agreement set after a kept single-register instruction is within the
    set extended by its destination. -/
theorem nextL_sub (L : List String) (dst opn : String) (srcs : List LOperand) (r : String)
    (h : (nextL L (.Lopn [.reg dst] opn srcs)).contains r = true) :
    (dst :: L).contains r = true := by
  simp only [nextL] at h
  split_ifs at h
  · simp only [List.contains_cons, Bool.or_eq_true]; exact Or.inr h
  · exact h

/-- **A kept instruction steps in lockstep.** From related states, an
    instruction `keepOk` accepts is stuck on both sides or steps on both to
    related states. -/
theorem keep_step {w : Nat} {L : List String} {fl : Bool} {i : LinstrR} {o n : FState w}
    (hs : Sim L fl o n) (hk : keepOk L fl i = true) :
    (fstep i o = none ∧ fstep i n = none) ∨
      ∃ o' n', fstep i o = some o' ∧ fstep i n = some n' ∧
        Sim (nextL L i) (fl || !flagSilentInstr i) o' n' := by
  cases i with
  | Lopn dsts opn srcs =>
    simp only [keepOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hk
    obtain ⟨huse, hfl⟩ := hk
    have hcov : ∀ op ∈ srcs, ∀ r, (operandReads op).contains r = true →
        L.contains r = true := fun op hop r hr =>
      huse r (by simpa using contains_instrUses_of_src (dsts := dsts) (opn := opn) hop hr)
    have hev : ∀ op ∈ srcs, evalOperand n.st op = evalOperand o.st op := fun op hop =>
      (evalOperand_liveAgree hs.1 op (hcov op hop)).symm
    cases h1 : cmovArgs? (.Lopn dsts opn srcs) with
    | some q =>
      obtain ⟨d, c, t, f⟩ := q
      cases cmovArgs?_spec h1
      refine Or.inr ⟨_, _, fstep_cmov d c t f o, fstep_cmov d c t f n, ?_, ?_⟩
      · rw [hev c (by simp), hev t (by simp), hev f (by simp)]
        exact LiveAgree.mono (LiveAgree.setReg_both hs.1 d _) (nextL_sub L d _ _)
      · intro _
        show some _ = some _
        rw [hev c (by simp)]
    | none =>
    cases h2 : testArgs? (.Lopn dsts opn srcs) with
    | some q =>
      obtain ⟨a, b⟩ := q
      obtain ⟨d, hd⟩ := testArgs?_spec h2
      cases hd
      refine Or.inr ⟨_, _, fstep_test d a b o, fstep_test d a b n, ?_, ?_⟩
      · rw [show nextL L (.Lopn [.reg d] testMn [a, b]) = L by simp [nextL, h2]]
        exact ⟨hs.1.1, hs.1.2⟩
      · intro _
        show some _ = some _
        rw [hev a (by simp), hev b (by simp)]
    | none =>
    cases h3 : cmpArgs? (.Lopn dsts opn srcs) with
    | some q =>
      obtain ⟨a, b⟩ := q
      obtain ⟨d, hd⟩ := cmpArgs?_spec h3
      cases hd
      refine Or.inr ⟨_, _, fstep_cmp d a b o, fstep_cmp d a b n, ?_, ?_⟩
      · rw [show nextL L (.Lopn [.reg d] cmpMn [a, b]) = L by simp [nextL, h3]]
        exact ⟨hs.1.1, hs.1.2⟩
      · intro _
        show some _ = some _
        rw [hev a (by simp), hev b (by simp)]
    | none =>
    cases h4 : cmovccArgs? (.Lopn dsts opn srcs) with
    | some q =>
      obtain ⟨ne, d, a, b⟩ := q
      have hfl' : fl = true := by
        rcases hfl with h | h
        · exact h
        · rw [h4] at h; cases h
      obtain ⟨mn, hd⟩ := cmovccArgs?_spec h4
      cases hd
      have hz := hs.2 hfl'
      cases hzo : o.zf with
      | none =>
        refine Or.inl ⟨?_, ?_⟩
        · simp only [fstep, h1, h2, h3, h4, hzo]
        · simp only [fstep, h1, h2, h3, h4, hz, hzo]
      | some z =>
        have hfo : fstep (.Lopn [.reg d] opn [a, b]) o = some
            ⟨(o.st.setReg d (if z = ne then evalOperand o.st a
              else evalOperand o.st b)).nextPc, some z⟩ := by
          simp only [fstep, h1, h2, h3, h4, hzo]
        have hfn : fstep (.Lopn [.reg d] opn [a, b]) n = some
            ⟨(n.st.setReg d (if z = ne then evalOperand o.st a
              else evalOperand o.st b)).nextPc, some z⟩ := by
          simp only [fstep, h1, h2, h3, h4, hz, hzo, hev a (by simp), hev b (by simp)]
        exact Or.inr ⟨_, _, hfo, hfn,
          LiveAgree.mono (LiveAgree.setReg_both hs.1 d _) (nextL_sub L d _ _), fun _ => rfl⟩
    | none =>
    have hfo : ∀ x : FState w, fstep (.Lopn dsts opn srcs) x =
        (lsemStep (.Lopn dsts opn srcs) x.st).map fun s' =>
          ⟨s', if flagSilentInstr (.Lopn dsts opn srcs) then x.zf else none⟩ := fun x => by
      simp only [fstep, h1, h2, h3, h4]
    have hzf : (fl || !flagSilentInstr (.Lopn dsts opn srcs)) = true →
        (if flagSilentInstr (.Lopn dsts opn srcs) then n.zf else none)
          = (if flagSilentInstr (.Lopn dsts opn srcs) then o.zf else none) := by
      intro h
      cases hsil : flagSilentInstr (.Lopn dsts opn srcs)
      · rfl
      · rw [hsil] at h
        simp only [Bool.not_true, Bool.or_false] at h
        simp only [if_true]
        exact hs.2 h
    cases ho : lsemStep (.Lopn dsts opn srcs) o.st with
    | none =>
      have hn : lsemStep (.Lopn dsts opn srcs) n.st = none := by
        have := lsemStep_isSome_indep (.Lopn dsts opn srcs) o.st n.st
        rw [ho] at this
        cases hn : lsemStep (.Lopn dsts opn srcs) n.st with
        | none => rfl
        | some _ => rw [hn] at this; cases this
      exact Or.inl ⟨by rw [hfo, ho]; rfl, by rw [hfo, hn]; rfl⟩
    | some s1 =>
      obtain ⟨dst, hd, hcase⟩ := lsemStep_liveAgree hs.1 hcov ho
      cases hd
      rcases hcase with ⟨v, hs1, hn⟩ | ⟨t1, hn, holvm, hnlvm, hmem, hfd⟩
      · refine Or.inr ⟨_, _, by rw [hfo, ho]; rfl, by rw [hfo, hn]; rfl, ?_, hzf⟩
        rw [hs1]
        exact LiveAgree.mono (LiveAgree.setReg_both hs.1 dst v) (nextL_sub L dst _ _)
      · refine Or.inr ⟨_, _, by rw [hfo, ho]; rfl, by rw [hfo, hn]; rfl, ?_, hzf⟩
        rw [show nextL L (.Lopn [.reg dst] opn srcs) = L by simp [nextL, hfd]]
        exact ⟨hmem, fun r hr => by
          show s1.lvm r = t1.lvm r
          rw [holvm, hnlvm]; exact hs.1.2 r hr⟩
  | Lalign => exact Or.inr ⟨_, _, rfl, rfl, ⟨hs.1.1, hs.1.2⟩, fun _ => rfl⟩
  | Llabel _ _ => exact Or.inr ⟨_, _, rfl, rfl, ⟨hs.1.1, hs.1.2⟩, fun _ => rfl⟩
  | Lgoto _ => exact Or.inl ⟨rfl, rfl⟩
  | Lcond _ _ => exact Or.inl ⟨rfl, rfl⟩
  | Ligoto _ => exact Or.inl ⟨rfl, rfl⟩
  | Lcall _ _ => exact Or.inl ⟨rfl, rfl⟩
  | Lret => exact Or.inl ⟨rfl, rfl⟩
  | LstoreLabel _ _ => exact Or.inl ⟨rfl, rfl⟩
  | Lsyscall _ => exact Or.inl ⟨rfl, rfl⟩

/-- The carried comparison stays correct across a kept instruction. -/
theorem fact_keep {w : Nat} {cur : Option (String × Bool)} {i : LinstrR}
    {o n o' n' : FState w} (hf : Fact cur o n) (ho : fstep i o = some o')
    (hn : fstep i n = some n') : Fact (nextFuseCur cur i) o' n' := by
  intro b ne hc
  unfold nextFuseCur at hc
  split at hc
  · rename_i b0 ne0 xr opn srcs
    split_ifs at hc with hsil
    cases hc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hsil
    obtain ⟨hA, hB, hC, hD⟩ :=
      flagArgs_none_of_silent (ds := [.reg xr]) (srcs := srcs) hsil.1
    simp only [fstep, hA, hB, hC, hD, flagSilentInstr, hsil.1, if_true] at ho hn
    obtain ⟨vx, vy, hbv, hz⟩ := hf b ne rfl
    cases hlo : lsemStep (.Lopn [.reg xr] opn srcs) o.st with
    | none => rw [hlo] at ho; cases ho
    | some so =>
      cases hln : lsemStep (.Lopn [.reg xr] opn srcs) n.st with
      | none => rw [hln] at hn; cases hn
      | some sn =>
        rw [hlo] at ho; rw [hln] at hn
        cases ho; cases hn
        exact ⟨vx, vy, by
          show so.lvm b = _
          rw [lsemStep_lvm_of_ne hlo (Ne.symm hsil.2)]; exact hbv, hz⟩
  · cases hc

/-! ### The sweep -/

/-- **The sweep relates the two runs.** From related states in which the
    carried comparison holds, the body the sweep returns and the original body
    are both stuck or finish in states agreeing on memory and on `liveOut`. -/
theorem fuseGo_sound {w : Nat} (liveOut : List String) :
    ∀ (body : Lcmd) (L : List String) (fl : Bool) (cur : Option (String × Bool))
      (out : Lcmd) (o n : FState w),
      fuseGo liveOut L fl cur body = some out → Sim L fl o n → Fact cur o n →
      FinalRel liveOut (fsem (body.map Linstr.li_i) o) (fsem (out.map Linstr.li_i) n)
  | [], L, fl, cur, out, o, n, hgo, hs, _ => by
      simp only [fuseGo] at hgo
      split_ifs at hgo with hall
      cases hgo
      simp only [List.all_eq_true] at hall
      exact LiveAgree.mono hs.1 fun r hr => hall r (by simpa using hr)
  | k :: rest, L, fl, cur, out, o, n, hgo, hs, hf => by
      simp only [fuseGo] at hgo
      cases hr : runSel L cur k.li_i with
      | some q =>
        obtain ⟨b, ne, d, t, f⟩ := q
        rw [hr] at hgo
        simp only [Option.map_eq_some_iff] at hgo
        obtain ⟨out', hgo', rfl⟩ := hgo
        obtain ⟨hcur, hk, hdb, ht, hfL⟩ := runSel_spec hr
        subst hcur
        obtain ⟨o', n', ho, hn, hs', hf'⟩ := sel_step hs k.li_ii hf hdb ht hfL
        simp only [List.map_cons, List.map_append, fsem, fsem_append, hk, ho, hn,
          Option.bind_some]
        exact fuseGo_sound liveOut rest _ _ _ _ _ _ hgo' hs' hf'
      | none =>
        rw [hr] at hgo
        cases hh : fuseHead liveOut L k.li_i rest with
        | some q =>
          obtain ⟨ne, b, x, y⟩ := q
          rw [hh] at hgo
          simp only [Option.map_eq_some_iff] at hgo
          obtain ⟨out', hgo', rfl⟩ := hgo
          obtain ⟨hk, hb, hx, hy⟩ := fuseHead_spec hh
          obtain ⟨o', n', ho, hn, hs', hf'⟩ := head_step hs k.li_ii ne hb hx hy
          simp only [List.map_cons, fsem, hk, ho, hn]
          exact fuseGo_sound liveOut rest _ _ _ _ _ _ hgo' hs' hf'
        | none =>
          rw [hh] at hgo
          split_ifs at hgo with hkeep
          simp only [Option.map_eq_some_iff] at hgo
          obtain ⟨out', hgo', rfl⟩ := hgo
          rcases keep_step hs hkeep with ⟨ho, hn⟩ | ⟨o', n', ho, hn, hs'⟩
          · simp only [List.map_cons, fsem, ho, hn]
            trivial
          · simp only [List.map_cons, fsem, ho, hn]
            exact fuseGo_sound liveOut rest _ _ _ _ _ _ hgo' hs' (fact_keep hf ho hn)

/-- **The fusion preserves memory and the live-out registers.** On every body
    and every start state, the fused body and the original body are both stuck
    under `fsem`, or both finish with equal memory and equal words in every
    register of `liveOut` and in every name outside the register pool. -/
theorem cmpFuseBody_sound {w : Nat} (liveOut : List String) (body : Lcmd) (x : FState w) :
    FinalRel liveOut (fsem (body.map Linstr.li_i) x)
      (fsem ((cmpFuseBody liveOut body).map Linstr.li_i) x) := by
  unfold cmpFuseBody
  cases hgo : fuseGo liveOut physGPs true none body with
  | none => exact FinalRel.refl _ _
  | some out =>
    exact fuseGo_sound liveOut body _ _ _ _ x x hgo ⟨LiveAgree.refl _ _, fun _ => rfl⟩
      (fun _ _ h => by cases h)

/-- The fusion on one `Lfundef` preserves memory and the live-out registers of
    its body. -/
theorem cmpFuseFundef_sound {w : Nat} (liveOut : List String) (f : Lfundef) (x : FState w) :
    FinalRel liveOut (fsem (f.lfd_body.map Linstr.li_i) x)
      (fsem ((cmpFuseFundef liveOut f).lfd_body.map Linstr.li_i) x) :=
  cmpFuseBody_sound liveOut f.lfd_body x

/-! ## 9. Static pins of the sweep

The `#guard`s pin the number of `TEST:64` instructions the sweep emits on two
three-instruction bodies in the shape of a comb-select entry (two selects on
one condition around a table load); they are static checks of the rule set,
evaluated at elaboration on lists of three instructions. -/

/-- The number of instructions of a body with mnemonic `mn`. -/
def countMn (mn : String) (b : Lcmd) : Nat :=
  b.countP fun k => match k.li_i with
    | .Lopn _ opn _ => opn == mn
    | _ => false

/-- Two selects on `RCX` around a flag-silent table load. -/
def pinSilent : Lcmd :=
  [ ⟨0, .Lopn [.reg "RAX"] cmovMn [.reg "RCX", .reg "RDX", .reg "RAX"]⟩
  , ⟨0, .Lopn [.reg "RDX"] "LOADIDX" [.arrIdx "RDI" "R8" 8]⟩
  , ⟨0, .Lopn [.reg "RBX"] cmovMn [.reg "RCX", .reg "RDX", .reg "RBX"]⟩ ]

/-- Two selects on `RCX` around a flag-writing add. -/
def pinWriter : Lcmd :=
  [ ⟨0, .Lopn [.reg "RAX"] cmovMn [.reg "RCX", .reg "RDX", .reg "RAX"]⟩
  , ⟨0, .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .imm 1]⟩
  , ⟨0, .Lopn [.reg "RBX"] cmovMn [.reg "RCX", .reg "RDX", .reg "RBX"]⟩ ]

/- Across the load one test serves both selects, and neither select keeps a
   self-move (`f = d`). -/
#guard countMn testMn (cmovTestElimBody pinSilent) == 1
#guard countMn movMn (cmovTestElimBody pinSilent) == 0
#guard countMn cmovneMn (cmovTestElimBody pinSilent) == 2
/- The add writes the flags, so the second select is tested again. -/
#guard countMn testMn (cmovTestElimBody pinWriter) == 2

/-- A disequality against zero into `RCX` feeding two selects around a
    flag-silent table load. -/
def pinFuse : Lcmd :=
  ⟨0, .Lopn [.reg "RCX"] setneMn [.reg "R9", .imm 0]⟩ :: pinSilent

/- With `RCX` dead after the body, the comparison becomes one `CMP:64`, no
   boolean is materialised, and both selects read its flag without a `TEST:64`.
   With `RCX` live after the body, the body is unchanged. These are static
   checks of the rule set on a list of four instructions. -/
#guard countMn cmpMn (cmpFuseBody ["RAX", "RBX"] pinFuse) == 1
#guard countMn setneMn (cmpFuseBody ["RAX", "RBX"] pinFuse) == 0
#guard countMn cmovneMn (cmpFuseBody ["RAX", "RBX"] pinFuse) == 2
#guard countMn testMn (cmpFuseBody ["RAX", "RBX"] pinFuse) == 0
#guard countMn setneMn (cmpFuseBody ["RAX", "RCX"] pinFuse) == 1

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCmovTestElim
