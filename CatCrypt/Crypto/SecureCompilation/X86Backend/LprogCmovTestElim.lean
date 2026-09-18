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
  instruction other than `CMOV:64`, `TEST:64`, `CMOVNE:64`, `CMOVE:64`, and on
  a `CMOV:64` whose condition holds `0` or `1`.
* `cmovTestElimBody_fview`, `cmovTestElimFundef_fview`: the pass preserves the
  observed state of `fsem` on every body and every start state.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCmovTestElim

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (selectW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (isPhysGP lsemStep_reg_nonmem)

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
    `CMOVNE:64` and `CMOVE:64`, and `lsemStep` on every other instruction with
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

/-! ## 5. The flag-extended step and `lsemStep` -/

/-- Operand evaluation reads only the register map and memory. -/
theorem evalOperand_congr {w : Nat} {s t : Lstate w} (hv : s.lvm = t.lvm)
    (hm : s.lmem = t.lmem) (o : LOperand) : evalOperand s o = evalOperand t o := by
  cases o <;> simp [evalOperand, hv, hm]

/-- On every instruction other than `CMOV:64`, `TEST:64`, `CMOVNE:64` and
    `CMOVE:64`, the linear-machine part of `fstep` is `lsemStep`. -/
theorem fstep_st_of_plain {w : Nat} (i : LinstrR) (x : FState w)
    (h1 : cmovArgs? i = none) (h2 : testArgs? i = none) (h3 : cmovccArgs? i = none) :
    Option.map FState.st (fstep i x) = lsemStep i x.st := by
  simp only [fstep, h1, h2, h3]
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
    · cases z <;> simp [fsem, fstep, cmovccL, cmovArgs?, testArgs?, cmovccArgs?, hz,
        cmoveMn_ne_testMn, cmoveMn_ne_cmovneMn, evalOperand]
    · funext r; simp [Lstate.setReg]
  · rw [if_neg hdt]
    by_cases hdf : d = f
    · subst hdf
      refine ⟨⟨(x0.st.setReg d (if z then x0.st.lvm d else x0.st.lvm t)).nextPc, some z⟩,
        ?_, ?_, rfl, rfl⟩
      · cases z <;> simp [fsem, fstep, cmovccL, cmovArgs?, testArgs?, cmovccArgs?, hz,
          cmovneMn_ne_testMn, evalOperand]
      · funext r; simp [Lstate.setReg]
    · refine ⟨⟨((x0.st.setReg d (x0.st.lvm f)).nextPc.setReg d
          (if z then x0.st.lvm f else x0.st.lvm t)).nextPc, some z⟩, ?_, ?_, rfl, rfl⟩
      · cases z <;> simp [fsem, fstep, movL, cmovccL, cmovArgs?, testArgs?, cmovccArgs?, hz,
          cmovneMn_ne_testMn, evalOperand, lsemStep, applyOpn, stripWidthTag_movMn,
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

/-- A flag-silent opcode is none of the four flag opcodes. -/
theorem flagArgs_none_of_silent {ds : List LOperand} {opn : String} {srcs : List LOperand}
    (hs : isFlagSilent opn = true) :
    cmovArgs? (.Lopn ds opn srcs) = none ∧ testArgs? (.Lopn ds opn srcs) = none ∧
      cmovccArgs? (.Lopn ds opn srcs) = none := by
  have h1 : opn ≠ cmovMn := fun h => by rw [h, isFlagSilent_cmovMn] at hs; cases hs
  have h2 : opn ≠ testMn := fun h => by rw [h, isFlagSilent_testMn] at hs; cases hs
  have h3 : opn ≠ cmovneMn := fun h => by rw [h, isFlagSilent_cmovneMn] at hs; cases hs
  have h4 : opn ≠ cmoveMn := fun h => by rw [h, isFlagSilent_cmoveMn] at hs; cases hs
  refine ⟨?_, ?_, ?_⟩
  · unfold cmovArgs?; split <;> simp_all
  · unfold testArgs?; split <;> simp_all
  · unfold cmovccArgs?; split <;> simp_all

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
    obtain ⟨hA, hB, hC⟩ :=
      flagArgs_none_of_silent (ds := [.reg xr]) (srcs := srcs) hsil.1
    simp only [fstep, hA, hB, hC, flagSilentInstr, hsil.1, if_true] at hs
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

/-! ## 8. Static pins of the sweep

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

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCmovTestElim
