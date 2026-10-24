/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CT.LowCTLeakage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT
public import CatCrypt.Crypto.SecureCompilation.CT.LowCTLevelCheck

/-!
# Constant time from `LowCT` to owned structured machine code

A lowering of a `LowCT` fragment with control flow, indexed memory, selects,
wide multiplies, variable shifts, runtime-bound and guarded loops, leaf calls and
tower copies to structured machine blocks `MCF`, and the preservation of constant
time from the source model of `CT/LowCTLeakage.lean` (`RustExecLeak`,
`LowCTConstantTime`) to the machine model of `CT/Leakage.lean`.

* `MCF` is `MachineConstantTime.OwnedCF 64` with a loop `loopRt r` whose trip
  count is the value of register `r` at loop entry and a loop `whileNz g` that
  tests register `g` before each iteration; `mcfExec` and `mcfLeak` are its
  semantics and leakage, the runtime loop emitting a `trip` event and the guarded
  loop a `branch` event per test (`whileLeak`), its iteration count the least
  after which the guard is zero (`whileCount`). `mcfExec_ofOwned` and
  `mcfLeak_ofOwned` state that on `OwnedCF` they are `cfExec` and `cfLeakCT`.
* `CFSrc` is the fragment: two-operand arithmetic (`ArithSrc`), literal
  assignments, word expressions (`WExpr`: reads, literals, `+`, `&`, `^`, `*`,
  lowered by `lowerW` through temporary registers), `RLetU64Zero`, variable shifts
  (`SShr`, `SShl`, `SAsr` by a scalar count), the high word of the unsigned
  wide multiply (`SMulHiU`), the unsigned comparison `SLt`, `RSelect`,
  `RArrLoad`, `RArrStore`, sequence, `RIfNz`, `RFor` with a literal trip count,
  `RForRuntime` with a scalar bound, `RWhileNz`, leaf calls `RCall` with their
  owned code (`LeafCode`), `RCopy`, `RLetZero`, limb stores `RLimbStoreExpr` of a
  word expression and limb reads `SLimb`. `CFSrc.toLowCT` embeds it in `LowCT`.
* `lowerCF ρ τ` lowers it to `MCF`, with `ρ` the register of each scalar and `τ`
  the base register of each tower variable: shifts to `SHRX`/`SHLX`/`SARX`, the
  wide multiply to `MULX`, the comparison to `CMP; SETC`, the select to
  `MOV; TEST; CMOVNE`, array accesses to `loadMemIdx`/`storeMemIdx` at scale 8,
  a leaf call to its owned block, a copy to a load and a store per word
  (`copyBlk`), limb accesses to `loadMem`/`storeMem` at the literal offset.
* `LeafCode` is the owned code of a leaf: a block, the registers it writes, and
  its trace, the same from every state. `notCode` is the code of the complement
  leaves `Not#w`.
* `srcDen` and `srcLeak` are the scalar post-state and the trace of the source.
  Tower values are not tracked: a limb read is opaque. `CFSrc.taint O` states that
  the opaque scalars `O` contain every limb read and every scalar computed from
  one, and that no guard, index, bound, shift operand or compared operand is
  opaque; `srcRun_det` states that under it every run of `c.toLowCT` has the trace
  `srcLeak c` and, outside `O`, the scalar post-state `srcDen c`.
* `mTrace τ c σ` is the machine trace as a function of the source state;
  `lowerCF_leak` states that the machine trace is `mTrace`, provided the scalar
  values the run tests, indexes, shifts by, compares or loops to are in range and
  the guarded loops exit (`InRange`). `srcLeak_prefix` states that the source
  trace determines `mTrace`.
* `lowct_to_machine_ct` derives machine `ConstantTime` from `LowCTConstantTime`
  for machine states agreeing on the public registers whose source images have a
  run and satisfy `InRange`; `lowerCF_leak_eq_of_runs` is its two-run form.
  `lowct_to_machine_ct_towerFree`, `lowct_to_machine_ct_towerOk` (tower accesses
  to names the program binds, `towerB`) and `lowct_to_machine_ct_rangeFree`
  discharge the run and the range condition on the corresponding subfragments.
* `lowerShift_mnem`, `lowerMulHi_mnem` and `lowerArith_mnem` state that the
  lowering emits the mnemonic `sexprMnem` assigns to the source expression;
  `ShiftKind.x86_ofNat` is the denotation of the shifts.
* The negative controls `secretGuard_lowered_not_ct`, `secretIndex_lowered_not_ct`,
  `secretShift_lowered_not_ct`, `secretBound_lowered_not_ct` and
  `secretWhile_lowered_not_ct` show that the lowering of a secret guard, index,
  `SARX` count, loop bound or guarded-loop guard is not constant time under the
  preconditions of `lowct_to_machine_ct`; `limbGuard_rejected` that a branch on a
  limb read fails the decided side conditions.
* `toCFSrc? nm k c` recognises a `LowCT` program as a program of the fragment, with
  the names of loop counters, `MULX` low words and temporaries and the code of leaf
  calls taken from `nm`; `toCFSrc?_spec` states that the recognised program embeds
  back to `c`. `wfB A` decides `CFSrc.WF` for a register allocation `A` whose image
  is recognised by a Boolean (`RegAlloc`), with the opaque scalars `opqOf c`;
  `rangeB` is a sufficient check of `InRange` for every state whose values are
  below `2^64` (`rangeB_sound`), rejecting shifts by a scalar count and loops.
* `machine_ct_of_lowct` and `machine_ct_of_lowct_closed` derive machine constant
  time of the lowering of a recognised program from `LowCTConstantTime`, the second
  for every pair of machine states agreeing on the public registers;
  `machine_ct_of_levelCheck` derives it from acceptance by `levelCheck`.
  `machineCTCheck` is a Boolean decision and `machineCTCheck_sound` its soundness;
  `machineCTCheckAdm` and `machineCTCheckAdm_sound` are the decision for
  admissible states, which admits loops and guarded loops.
* `stdAlloc`, `stdNames` and `stdPub lt` are a register allocation, a name supply
  outside its image with the complement leaves, and the public registers of `lt`
  under it (`stdPub_spec`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CT.LowCTMachine

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT (movImm evalInstr_movImm)
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Structured machine code with runtime-bound loops -/

/-- Structured machine blocks: `OwnedCF 64` and a loop `loopRt bound body` that
    runs `body` as many times as register `bound` holds at loop entry. -/
inductive MCF where
  | straight (body : List (JInstr 64))
  | seq (a b : MCF)
  | ifPub (guard : String) (thenB elseB : MCF)
  | loop (n : Nat) (body : MCF)
  | loopRt (bound : String) (body : MCF)
  | whileNz (guard : String) (body : MCF)

/-- The number of applications of `step` to `a` before `z` holds: the least `k`
    with `z (step^[k] a)`, and `0` when there is none. -/
noncomputable def whileCount {α : Type} (step : α → α) (z : α → Prop) (a : α) : Nat := by
  classical
  exact if h : ∃ k, z (step^[k] a) then Nat.find h else 0

theorem whileCount_eq {α : Type} (step : α → α) (z : α → Prop) (a : α) (k : Nat)
    (hk : z (step^[k] a)) (hlt : ∀ j < k, ¬ z (step^[j] a)) : whileCount step z a = k := by
  classical
  unfold whileCount
  rw [dite_eq_left ⟨k, hk⟩]
  exact (Nat.find_eq_iff _).2 ⟨hk, hlt⟩

/-- The trace of a guarded loop running `k` iterations: per iteration a
    `branch true` event and the trace `l` of the body, then the `branch false`
    event of the failing test. -/
def whileLeak {α : Type} (step : α → α) (l : α → List CTLeak) : Nat → α → List CTLeak
  | 0, _ => [.branch false]
  | k + 1, a => .branch true :: (l a ++ whileLeak step l k (step a))

/-- The machine semantics of `MCF`. A guarded loop runs its body the least number
    of times after which the guard register is zero. -/
noncomputable def mcfExec : JState 64 → MCF → JState 64
  | s, .straight body => runBlock s body
  | s, .seq a b => mcfExec (mcfExec s a) b
  | s, .ifPub g t e => if s.get g = 0 then mcfExec s e else mcfExec s t
  | s, .loop n body => (fun s' => mcfExec s' body)^[n] s
  | s, .loopRt g body => (fun s' => mcfExec s' body)^[(s.get g).toNat] s
  | s, .whileNz g body =>
      (fun s' => mcfExec s' body)^[whileCount (fun s' => mcfExec s' body)
        (fun s' => s'.get g = 0) s] s

/-- The leakage of `MCF` under a regime: as `cfLeakCT`, a runtime loop emits
    its trip count before its iterations, and a guarded loop a branch event per
    guard test. -/
noncomputable def mcfLeak (r : DoitRegime) : JState 64 → MCF → List CTLeak
  | s, .straight body => blockLeakCT r s body
  | s, .seq a b => mcfLeak r s a ++ mcfLeak r (mcfExec s a) b
  | s, .ifPub g t e =>
      if s.get g = 0 then .branch false :: mcfLeak r s e else .branch true :: mcfLeak r s t
  | s, .loop n body => iterLeak (fun s' => mcfLeak r s' body) (fun s' => mcfExec s' body) n s
  | s, .loopRt g body =>
      .trip (s.get g).toNat ::
        iterLeak (fun s' => mcfLeak r s' body) (fun s' => mcfExec s' body) (s.get g).toNat s
  | s, .whileNz g body =>
      whileLeak (fun s' => mcfExec s' body) (fun s' => mcfLeak r s' body)
        (whileCount (fun s' => mcfExec s' body) (fun s' => s'.get g = 0) s) s

/-- The embedding of `OwnedCF 64`. -/
def MCF.ofOwned : OwnedCF 64 → MCF
  | .straight body => .straight body
  | .seq a b => .seq (MCF.ofOwned a) (MCF.ofOwned b)
  | .loop n body => .loop n (MCF.ofOwned body)
  | .ifPub g t e => .ifPub g (MCF.ofOwned t) (MCF.ofOwned e)

theorem mcfExec_ofOwned (cf : OwnedCF 64) (s : JState 64) :
    mcfExec s (MCF.ofOwned cf) = (cfExec s cf).2 := by
  induction cf generalizing s with
  | straight body => rw [MCF.ofOwned, mcfExec, cfExec]
  | seq a b iha ihb => rw [MCF.ofOwned, mcfExec, iha, ihb, cfExec]
  | loop n body ih =>
    rw [MCF.ofOwned, mcfExec, cfExec]
    induction n generalizing s with
    | zero => rw [cfLoop]; rfl
    | succ m ihm => rw [cfLoop, Function.iterate_succ_apply, ih, ihm]
  | ifPub g t e iht ihe =>
    rw [MCF.ofOwned, mcfExec, cfExec]
    split <;> simp only [iht, ihe]

theorem mcfLeak_ofOwned (r : DoitRegime) (cf : OwnedCF 64) (s : JState 64) :
    mcfLeak r s (MCF.ofOwned cf) = cfLeakCT r s cf := by
  induction cf generalizing s with
  | straight body => rw [MCF.ofOwned, mcfLeak, cfLeakCT]
  | seq a b iha ihb => rw [MCF.ofOwned, mcfLeak, iha, ihb, cfLeakCT, mcfExec_ofOwned]
  | loop n body ih =>
    rw [MCF.ofOwned, mcfLeak, cfLeakCT]
    induction n generalizing s with
    | zero => rfl
    | succ m ihm => rw [iterLeak, iterLeak, ih, ihm, mcfExec_ofOwned]
  | ifPub g t e iht ihe => rw [MCF.ofOwned, mcfLeak, cfLeakCT, iht, ihe]

/-! ## 2. The fragment and its lowering -/

/-- The variable-count shifts: logical right, left, arithmetic right. -/
inductive ShiftKind where
  | shr | shl | sar
  deriving DecidableEq, Repr

/-- The source expression of a shift. -/
def ShiftKind.toSExpr : ShiftKind → SExpr → SExpr → SExpr
  | .shr, a, b => .SShr a b
  | .shl, a, b => .SShl a b
  | .sar, a, b => .SAsr a b

/-- The source value of a shift (`SExpr.eval` of its expression). -/
def ShiftKind.eval : ShiftKind → Nat → Nat → Nat
  | .shr, a, c => a >>> c
  | .shl, a, c => a <<< c
  | .sar, a, c => sexprOfSignedInt64 (sexprToSignedInt64 a >>> c)

/-- The BMI2 instruction of a shift: `dst := src ⟨shift⟩ cnt`. -/
def ShiftKind.toJInstr : ShiftKind → String → String → String → JInstr 64
  | .shr, d, a, c => .shrx d a c
  | .shl, d, a, c => .shlx d a c
  | .sar, d, a, c => .sarx d a c

/-- The machine value of a shift. -/
def ShiftKind.x86 : ShiftKind → BitVec 64 → BitVec 64 → BitVec 64
  | .shr => x86_SHRX
  | .shl => x86_SHLX
  | .sar => x86_SARX

/-- The source leakage of a shift under `LowCTLeakModel.owned`: `SARX` is
    variable time and leaks both operands; `SHRX` and `SHLX` leak nothing. -/
def ShiftKind.leak : ShiftKind → Nat → Nat → List CTLeak
  | .sar, a, c => [.vt .sarx [a, c]]
  | _, _, _ => []

/-- Word expressions: scalar reads, literals, and the operations of `ArithOp`
    (`+`, `&`, `^`, `*`), each of which commutes with truncation to 64 bits. -/
inductive WExpr where
  | var (v : String)
  | lit (n : Nat)
  | bin (op : ArithOp) (a b : WExpr)
  deriving Repr

/-- The source node of an `ArithOp`. -/
def arithNode : ArithOp → SExpr → SExpr → SExpr
  | .add, a, b => .SAdd a b
  | .and_, a, b => .SAnd a b
  | .xor_, a, b => .SXor a b
  | .mul_, a, b => .SMul a b

/-- The source expression of a word expression. -/
def WExpr.toSExpr : WExpr → SExpr
  | .var v => .SVar v
  | .lit n => .SLit n
  | .bin op a b => arithNode op a.toSExpr b.toSExpr

/-- The number of temporary registers the lowering of a word expression uses. -/
def WExpr.depth : WExpr → Nat
  | .var _ | .lit _ => 1
  | .bin _ a b => max a.depth (b.depth + 1)

/-- The lowering of a word expression into the first of the temporaries `ts`:
    the left operand into the first temporary, the right operand into the rest,
    then the operation. -/
def lowerW (ρ : RegMap) : List String → WExpr → List (JInstr 64)
  | [], _ => []
  | t :: _, .var v => [.mov t (.reg (ρ v))]
  | t :: _, .lit n => [movImm t n]
  | t :: ts, .bin op a b =>
      lowerW ρ (t :: ts) a ++ lowerW ρ ts b ++ [op.toJInstr t (.reg (ts.headD t))]

/-- The variables a word expression reads. -/
def WExpr.vars : WExpr → List String
  | .var v => [v]
  | .lit _ => []
  | .bin _ a b => a.vars ++ b.vars

/-- The owned machine code of a leaf call: a straight-line block `blk`, the
    registers `clob` it may write, and its trace `leak`, which is the trace of
    `blk` under DOITM from every state. -/
structure LeafCode where
  blk : List (JInstr 64)
  clob : List String
  leak : List CTLeak
  leak_eq : ∀ s, blockLeakCT .doitm s blk = leak
  get_other : ∀ s r, r ∉ clob → (runBlock s blk).get r = s.get r

/-- The number of 64-bit words of a tower type. -/
def towerWords (t : TowerType) : Nat := (t.storageBytes + 7) / 8

/-- The copy of the first `n` words from base register `src` to base register
    `dst` through register `t`: a load and a store per word, at the literal byte
    offset `8 * i`. -/
def copyBlk (dst src t : String) : Nat → List (JInstr 64)
  | 0 => []
  | n + 1 => copyBlk dst src t n ++
      [.loadMem t src ((8 * n : Nat) : Int), .storeMem dst ((8 * n : Nat) : Int) (.reg t)]

/-- The trace of `copyBlk dst src t n`: the address events of its loads and
    stores. -/
def copyLeak (dst src : String) : Nat → List CTLeak
  | 0 => []
  | n + 1 => copyLeak dst src n ++
      [.addr src ((8 * n : Nat) : Int), .addr dst ((8 * n : Nat) : Int)]

/-- The source fragment. `ctr` names the machine counter register of a loop,
    `lo` the machine register receiving the discarded low word of `MULX`,
    `tmps` the temporaries of a word expression, `tmp` the register a tower copy
    moves words through, and `code` the owned block of a leaf call. -/
inductive CFSrc where
  | skip
  | arith (p : ArithSrc)
  | setLit (dst : String) (n : Nat)
  | expr (dst : String) (e : WExpr) (tmps : List String)
  | letU64 (x : String) (body : CFSrc)
  | shift (k : ShiftKind) (dst a cnt : String)
  | mulHi (dst a b lo : String)
  | select (dst : Located) (sel : String) (src0 src1 : Located)
  | arrLoad (dst src : Located) (idx : String)
  | arrStore (arr : Located) (idx : String) (src : Located)
  | seq (a b : CFSrc)
  | ifNz (g : String) (thenB elseB : CFSrc)
  | forLit (x ctr : String) (n : Nat) (body : CFSrc)
  | forRt (x ctr bnd : String) (body : CFSrc)
  | ltSet (dst a b : String)
  | whileNz (g : String) (body : CFSrc)
  | call (f : String) (dest : Located) (args : List Located) (code : LeafCode)
  | copy (dst src : Located) (tmp : String)
  | letT (x : String) (t : TowerType) (body : CFSrc)
  | limbSet (loc : Located) (idx : Nat) (e : WExpr) (tmps : List String)
  | limbGet (dst v : String) (idx : Nat)

/-- The embedding into `LowCT`. -/
def CFSrc.toLowCT : CFSrc → LowCT
  | .skip => .RSkip
  | .arith p => p.toLowCT
  | .setLit d n => .RScalarSet d n
  | .expr d e _ => .RScalarSetExpr d e.toSExpr
  | .letU64 x body => .RLetU64Zero x body.toLowCT
  | .shift k d a c => .RScalarSetExpr d (k.toSExpr (.SVar a) (.SVar c))
  | .mulHi d a b _ => .RScalarSetExpr d (.SMulHiU (.SVar a) (.SVar b))
  | .select dst sel s0 s1 => .RSelect dst sel s0 s1
  | .arrLoad dst src idx => .RArrLoad dst src idx
  | .arrStore arr idx src => .RArrStore arr idx src
  | .seq a b => .RSeq a.toLowCT b.toLowCT
  | .ifNz g t e => .RIfNz g t.toLowCT e.toLowCT
  | .forLit x _ n body => .RFor x n body.toLowCT
  | .forRt x _ bnd body => .RForRuntime x (.SVar bnd) body.toLowCT
  | .ltSet d a b => .RScalarSetExpr d (.SLt (.SVar a) (.SVar b))
  | .whileNz g body => .RWhileNz g body.toLowCT
  | .call f dest args _ => .RCall f dest args
  | .copy dst src _ => .RCopy dst src
  | .letT x t body => .RLetZero x t body.toLowCT
  | .limbSet loc idx e _ => .RLimbStoreExpr loc idx e.toSExpr
  | .limbGet d v idx => .RScalarSetExpr d (.SLimb v idx)

/-- The machine body of one loop iteration: `ρ x := ctr`, the lowered body,
    `ctr := ctr + 1`. -/
def loopBody (ρ : RegMap) (x ctr : String) (body : MCF) : MCF :=
  .seq (.straight [.mov (ρ x) (.reg ctr)]) (.seq body (.straight [.add ctr (.imm 1)]))

/-- The select `dst := sel ≠ 0 ? src1 : src0` as `MOV; TEST; CMOVNE`. -/
def lowerSelect (ρ τ : RegMap) (dst : Located) (sel : String) (src0 src1 : Located) :
    List (JInstr 64) :=
  [ .mov (τ dst.locVar) (.reg (τ src0.locVar)), .test (ρ sel) (.reg (ρ sel)),
    .cmovne (τ dst.locVar) (.reg (τ src1.locVar)) ]

/-- The lowering to structured machine code. -/
def lowerCF (ρ τ : RegMap) : CFSrc → MCF
  | .skip => .straight []
  | .arith p => .straight (lowerArith ρ p)
  | .setLit d n => .straight [movImm (ρ d) n]
  | .expr d e ts => .straight (lowerW ρ ts e ++ [.mov (ρ d) (.reg (ts.headD (ρ d)))])
  | .letU64 x body => .seq (.straight [movImm (ρ x) 0]) (lowerCF ρ τ body)
  | .shift k d a c => .straight [k.toJInstr (ρ d) (ρ a) (ρ c)]
  | .mulHi d a b lo => .straight [.mulx (ρ d) lo (.reg (ρ a)) (.reg (ρ b))]
  | .select dst sel s0 s1 => .straight (lowerSelect ρ τ dst sel s0 s1)
  | .arrLoad dst src idx => .straight [.loadMemIdx (τ dst.locVar) (τ src.locVar) (ρ idx) 8]
  | .arrStore arr idx src =>
      .straight [.storeMemIdx (τ arr.locVar) (ρ idx) 8 (.reg (τ src.locVar))]
  | .seq a b => .seq (lowerCF ρ τ a) (lowerCF ρ τ b)
  | .ifNz g t e => .ifPub (ρ g) (lowerCF ρ τ t) (lowerCF ρ τ e)
  | .forLit x ctr n body =>
      .seq (.straight [movImm ctr 0]) (.loop n (loopBody ρ x ctr (lowerCF ρ τ body)))
  | .forRt x ctr bnd body =>
      .seq (.straight [movImm ctr 0]) (.loopRt (ρ bnd) (loopBody ρ x ctr (lowerCF ρ τ body)))
  | .ltSet d a b => .straight [.cmp (ρ a) (.reg (ρ b)), .setc (ρ d)]
  | .whileNz g body => .whileNz (ρ g) (lowerCF ρ τ body)
  | .call _ _ _ code => .straight code.blk
  | .copy dst src tmp => .straight (copyBlk (τ dst.locVar) (τ src.locVar) tmp (towerWords dst.locDst))
  | .letT _ _ body => lowerCF ρ τ body
  | .limbSet loc idx e ts =>
      .straight (lowerW ρ ts e ++
        [.storeMem (τ loc.locVar) ((8 * idx : Nat) : Int) (.reg (ts.headD (τ loc.locVar)))])
  | .limbGet d v idx => .straight [.loadMem (ρ d) (τ v) ((8 * idx : Nat) : Int)]

/-- The machine registers outside the image of `ρ` that the lowering writes:
    loop counters, `MULX` low words, the tower registers of select and load
    destinations, the registers leaf blocks write, and temporaries. -/
def CFSrc.writes (τ : RegMap) : CFSrc → List String
  | .skip | .arith _ | .setLit .. | .shift .. | .arrStore .. | .ltSet .. | .limbGet .. => []
  | .expr _ _ ts | .limbSet _ _ _ ts => ts
  | .letU64 _ body | .whileNz _ body | .letT _ _ body => body.writes τ
  | .call _ _ _ code => code.clob
  | .copy _ _ tmp => [tmp]
  | .mulHi _ _ _ lo => [lo]
  | .select dst .. => [τ dst.locVar]
  | .arrLoad dst .. => [τ dst.locVar]
  | .seq a b => a.writes τ ++ b.writes τ
  | .ifNz _ t e => t.writes τ ++ e.writes τ
  | .forLit _ ctr _ body | .forRt _ ctr _ body => ctr :: body.writes τ

/-- Register-allocation side conditions: the second operand of an arithmetic
    statement is not its destination; the temporaries of a word expression are
    distinct, at least its depth in number, and outside the image of `ρ`; `MULX`
    low words, tower destinations and loop counters lie outside the image of `ρ`;
    a loop counter is not written by the loop body; the registers of leaf blocks,
    copies and limb stores lie outside the image of `ρ`. -/
def CFSrc.RegWF (ρ τ : RegMap) : CFSrc → Prop
  | .skip | .setLit .. | .shift .. | .arrStore .. | .ltSet .. | .limbGet .. => True
  | .arith p => p.b ≠ p.dst
  | .expr _ e ts => (∀ v, ∀ t ∈ ts, ρ v ≠ t) ∧ ts.Nodup ∧ e.depth ≤ ts.length
  | .letU64 _ body | .whileNz _ body | .letT _ _ body => body.RegWF ρ τ
  | .mulHi _ _ _ lo => ∀ v, ρ v ≠ lo
  | .select dst .. => ∀ v, ρ v ≠ τ dst.locVar
  | .arrLoad dst .. => ∀ v, ρ v ≠ τ dst.locVar
  | .seq a b => a.RegWF ρ τ ∧ b.RegWF ρ τ
  | .ifNz _ t e => t.RegWF ρ τ ∧ e.RegWF ρ τ
  | .forLit _ ctr _ body | .forRt _ ctr _ body =>
      (∀ v, ρ v ≠ ctr) ∧ ctr ∉ body.writes τ ∧ body.RegWF ρ τ
  | .call _ _ _ code => ∀ v, ∀ t ∈ code.clob, ρ v ≠ t
  | .copy _ _ tmp => ∀ v, ρ v ≠ tmp
  | .limbSet _ _ _ ts => ∀ v, ∀ t ∈ ts, ρ v ≠ t

/-- The taint condition for the opaque scalars `O`, the scalars whose value may
    come from a tower: a limb read writes an opaque scalar; a statement writing a
    scalar outside `O` reads only scalars outside `O`; guards, indices, loop
    bounds, shift operands and compared operands lie outside `O`. -/
def CFSrc.taint (O : String → Bool) : CFSrc → Bool
  | .skip | .setLit .. | .select .. | .call .. | .copy .. | .limbSet .. => true
  | .arith p => O p.dst || (!O p.a && !O p.b)
  | .expr d e _ => O d || e.vars.all (fun v => !O v)
  | .letU64 _ b | .letT _ _ b | .forLit _ _ _ b => b.taint O
  | .shift _ _ a c => !O a && !O c
  | .mulHi d a b _ => O d || (!O a && !O b)
  | .ltSet _ a b => !O a && !O b
  | .arrLoad _ _ idx | .arrStore _ idx _ => !O idx
  | .seq a b => a.taint O && b.taint O
  | .ifNz g t e => !O g && t.taint O && e.taint O
  | .forRt _ _ bnd b | .whileNz bnd b => !O bnd && b.taint O
  | .limbGet d _ _ => O d

/-- Register-allocation side conditions and the taint condition for some set of
    opaque scalars. -/
def CFSrc.WF (ρ τ : RegMap) (c : CFSrc) : Prop := c.RegWF ρ τ ∧ ∃ O, c.taint O = true

/-- Whether a program accesses no tower and has a run from every state: no
    select, array access, leaf call, copy, tower binding, limb access or guarded
    loop. -/
def CFSrc.towerFree : CFSrc → Bool
  | .select .. | .arrLoad .. | .arrStore .. | .whileNz .. | .call .. | .copy .. | .letT ..
  | .limbSet .. | .limbGet .. => false
  | .seq a b => a.towerFree && b.towerFree
  | .ifNz _ t e => t.towerFree && e.towerFree
  | .forLit _ _ _ body | .forRt _ _ _ body | .letU64 _ body => body.towerFree
  | _ => true

/-- Whether a program has no range condition and accesses no tower: arithmetic,
    wide multiplies, sequences and literal loops only. -/
def CFSrc.rangeFree : CFSrc → Bool
  | .skip | .arith _ | .setLit .. | .expr .. | .mulHi .. => true
  | .seq a b => a.rangeFree && b.rangeFree
  | .forLit _ _ _ body | .letU64 _ body => body.rangeFree
  | _ => false

/-! ## 3. Source post-state and trace -/

/-- A scalar environment. -/
abbrev Env := String → Nat

/-- Update a scalar environment; `(rsSetScalar rs x v).rsScalar` is
    `setS rs.rsScalar x v` by definition. -/
def setS (σ : Env) (x : String) (v : Nat) : Env := fun y => if y == x then v else σ y

theorem rsSetScalar_rsScalar (rs : RustState) (x : String) (v : Nat) :
    (rsSetScalar rs x v).rsScalar = setS rs.rsScalar x v := rfl

/-- `k` loop iterations starting at index `i`: each sets `x` to the index, then
    applies `f`. -/
def iterDen (x : String) (f : Env → Env) : Nat → Nat → Env → Env
  | 0, _, σ => σ
  | k + 1, i, σ => iterDen x f k (i + 1) (f (setS σ x i))

/-- The trace of `k` loop iterations starting at index `i`. -/
def iterTrace (x : String) (f : Env → Env) (l : Env → List CTLeak) :
    Nat → Nat → Env → List CTLeak
  | 0, _, _ => []
  | k + 1, i, σ => l (setS σ x i) ++ iterTrace x f l k (i + 1) (f (setS σ x i))

/-- A predicate on the entry state of each of `k` loop iterations. -/
def iterAll (x : String) (f : Env → Env) (P : Env → Prop) : Nat → Nat → Env → Prop
  | 0, _, _ => True
  | k + 1, i, σ => P (setS σ x i) ∧ iterAll x f P k (i + 1) (f (setS σ x i))

/-- The scalar post-state of the source. A limb read sets its destination to `0`,
    the value `SExpr.eval` gives `SLimb`; a guarded loop runs its body the least
    number of times after which the guard is zero. -/
noncomputable def srcDen : CFSrc → Env → Env
  | .skip, σ => σ
  | .arith p, σ => setS σ p.dst (p.toSExpr.eval σ)
  | .setLit d n, σ => setS σ d n
  | .expr d e _, σ => setS σ d (e.toSExpr.eval σ)
  | .letU64 x body, σ => srcDen body (setS σ x 0)
  | .shift k d a c, σ => setS σ d (k.eval (σ a) (σ c))
  | .mulHi d a b _, σ => setS σ d (sexprMulHiU (σ a) (σ b))
  | .select .., σ | .arrLoad .., σ | .arrStore .., σ => σ
  | .seq a b, σ => srcDen b (srcDen a σ)
  | .ifNz g t e, σ => if σ g = 0 then srcDen e σ else srcDen t σ
  | .forLit x _ n body, σ => iterDen x (srcDen body) n 0 σ
  | .forRt x _ bnd body, σ => iterDen x (srcDen body) (σ bnd) 0 σ
  | .ltSet d a b, σ => setS σ d (if σ a < σ b then 1 else 0)
  | .whileNz g body, σ =>
      (srcDen body)^[whileCount (srcDen body) (fun σ' => σ' g = 0) σ] σ
  | .call .., σ | .copy .., σ | .limbSet .., σ => σ
  | .letT _ _ body, σ => srcDen body σ
  | .limbGet d _ _, σ => setS σ d 0

/-- The source trace under `LowCTLeakModel.owned`. -/
noncomputable def srcLeak : CFSrc → Env → List CTLeak
  | .skip, _ | .arith _, _ | .setLit .., _ | .expr .., _ | .mulHi .., _ | .select .., _
  | .ltSet .., _ | .call .., _ | .copy .., _ | .limbSet .., _ | .limbGet .., _ => []
  | .letU64 x body, σ => srcLeak body (setS σ x 0)
  | .letT _ _ body, σ => srcLeak body σ
  | .whileNz g body, σ =>
      whileLeak (srcDen body) (srcLeak body) (whileCount (srcDen body) (fun σ' => σ' g = 0) σ) σ
  | .shift k _ a c, σ => k.leak (σ a) (σ c)
  | .arrLoad _ src idx, σ => [.addr src.locVar (σ idx)]
  | .arrStore arr idx _, σ => [.addr arr.locVar (σ idx)]
  | .seq a b, σ => srcLeak a σ ++ srcLeak b (srcDen a σ)
  | .ifNz g t e, σ =>
      if σ g = 0 then .branch false :: srcLeak e σ else .branch true :: srcLeak t σ
  | .forLit x _ n body, σ => iterTrace x (srcDen body) (srcLeak body) n 0 σ
  | .forRt x _ bnd body, σ =>
      .trip (σ bnd) :: iterTrace x (srcDen body) (srcLeak body) (σ bnd) 0 σ

/-- The range conditions of a guarded loop from `σ`: it exits after some `k`
    iterations, and before each of them the guard is nonzero and below `2^64` and
    the condition `P` of the body holds. -/
def WhileRange (g : String) (f : Env → Env) (P : Env → Prop) (σ : Env) : Prop :=
  ∃ k, (f^[k] σ) g = 0 ∧ ∀ j < k, (f^[j] σ) g ≠ 0 ∧ (f^[j] σ) g < 2 ^ 64 ∧ P (f^[j] σ)

/-- The range conditions of a run: guards, indices and loop bounds below `2^64`,
    shifted values below `2^64`, shift counts below `64`, compared operands below
    `2^64`, and termination of guarded loops. -/
def InRange : CFSrc → Env → Prop
  | .skip, _ | .arith _, _ | .setLit .., _ | .expr .., _ | .mulHi .., _ | .select .., _
  | .call .., _ | .copy .., _ | .limbSet .., _ | .limbGet .., _ => True
  | .letU64 x body, σ => InRange body (setS σ x 0)
  | .letT _ _ body, σ => InRange body σ
  | .ltSet _ a b, σ => σ a < 2 ^ 64 ∧ σ b < 2 ^ 64
  | .whileNz g body, σ => WhileRange g (srcDen body) (InRange body) σ
  | .shift _ _ a c, σ => σ a < 2 ^ 64 ∧ σ c < 64
  | .arrLoad _ _ idx, σ => σ idx < 2 ^ 64
  | .arrStore _ idx _, σ => σ idx < 2 ^ 64
  | .seq a b, σ => InRange a σ ∧ InRange b (srcDen a σ)
  | .ifNz g t e, σ => σ g < 2 ^ 64 ∧ (if σ g = 0 then InRange e σ else InRange t σ)
  | .forLit x _ n body, σ => iterAll x (srcDen body) (InRange body) n 0 σ
  | .forRt x _ bnd body, σ => σ bnd < 2 ^ 64 ∧ iterAll x (srcDen body) (InRange body) (σ bnd) 0 σ

/-- The machine trace of the lowering as a function of the source scalar state:
    the source element event `addr a i` becomes the machine address event
    `addr (τ a) (8 * i)`, a leaf call contributes the trace of its block, and a
    copy or limb access the address events of its loads and stores. -/
noncomputable def mTrace (τ : RegMap) : CFSrc → Env → List CTLeak
  | .skip, _ | .arith _, _ | .setLit .., _ | .expr .., _ | .mulHi .., _ | .select .., _
  | .ltSet .., _ => []
  | .letU64 x body, σ => mTrace τ body (setS σ x 0)
  | .letT _ _ body, σ => mTrace τ body σ
  | .shift k _ a c, σ => k.leak (σ a) (σ c)
  | .arrLoad _ src idx, σ => [.addr (τ src.locVar) (8 * ((σ idx : Nat) : Int))]
  | .arrStore arr idx _, σ => [.addr (τ arr.locVar) (8 * ((σ idx : Nat) : Int))]
  | .seq a b, σ => mTrace τ a σ ++ mTrace τ b (srcDen a σ)
  | .ifNz g t e, σ =>
      if σ g = 0 then .branch false :: mTrace τ e σ else .branch true :: mTrace τ t σ
  | .forLit x _ n body, σ => iterTrace x (srcDen body) (mTrace τ body) n 0 σ
  | .forRt x _ bnd body, σ =>
      .trip (σ bnd) :: iterTrace x (srcDen body) (mTrace τ body) (σ bnd) 0 σ
  | .whileNz g body, σ =>
      whileLeak (srcDen body) (mTrace τ body) (whileCount (srcDen body) (fun σ' => σ' g = 0) σ) σ
  | .call _ _ _ code, _ => code.leak
  | .copy dst src _, _ => copyLeak (τ dst.locVar) (τ src.locVar) (towerWords dst.locDst)
  | .limbSet loc idx _ _, _ => [.addr (τ loc.locVar) ((8 * idx : Nat) : Int)]
  | .limbGet _ v idx, _ => [.addr (τ v) ((8 * idx : Nat) : Int)]

theorem iterAll_of_forall (x : String) (f : Env → Env) (P : Env → Prop)
    (hP : ∀ σ, P σ) : ∀ k i σ, iterAll x f P k i σ := by
  intro k
  induction k with
  | zero => intro _ _; trivial
  | succ k ih => intro i σ; exact ⟨hP _, ih _ _⟩

theorem inRange_of_rangeFree : ∀ (c : CFSrc), c.rangeFree = true → ∀ σ, InRange c σ
  | .skip, _, _ | .arith _, _, _ | .setLit .., _, _ | .expr .., _, _ | .mulHi .., _, _ => trivial
  | .letU64 _ body, h, _ => inRange_of_rangeFree body h _
  | .seq a b, h, σ => by
    simp only [CFSrc.rangeFree, Bool.and_eq_true] at h
    exact ⟨inRange_of_rangeFree a h.1 σ, inRange_of_rangeFree b h.2 _⟩
  | .forLit x _ n body, h, σ => iterAll_of_forall x _ _ (inRange_of_rangeFree body h) n 0 σ
  | .shift .., h, _ | .select .., h, _ | .arrLoad .., h, _ | .arrStore .., h, _
  | .ifNz .., h, _ | .forRt .., h, _ | .ltSet .., h, _ | .whileNz .., h, _ | .call .., h, _
  | .copy .., h, _ | .letT .., h, _ | .limbSet .., h, _ | .limbGet .., h, _ => by
    simp [CFSrc.rangeFree] at h

theorem towerFree_of_rangeFree : ∀ (c : CFSrc), c.rangeFree = true → c.towerFree = true
  | .skip, _ | .arith _, _ | .setLit .., _ | .expr .., _ | .mulHi .., _ => rfl
  | .letU64 _ body, h => towerFree_of_rangeFree body h
  | .seq a b, h => by
    simp only [CFSrc.rangeFree, Bool.and_eq_true] at h
    simp only [CFSrc.towerFree, towerFree_of_rangeFree a h.1, towerFree_of_rangeFree b h.2,
      Bool.and_self]
  | .forLit _ _ _ body, h => towerFree_of_rangeFree body h
  | .shift .., h | .select .., h | .arrLoad .., h | .arrStore .., h
  | .ifNz .., h | .forRt .., h | .ltSet .., h | .whileNz .., h | .call .., h
  | .copy .., h | .letT .., h | .limbSet .., h | .limbGet .., h => by
    simp [CFSrc.rangeFree] at h

/-! ### 3.1 The source trace is the trace of `RustExecLeak` -/

theorem iterDen_succ (x : String) (f : Env → Env) :
    ∀ k i σ, iterDen x f (k + 1) i σ = f (setS (iterDen x f k i σ) x (i + k)) := by
  intro k
  induction k with
  | zero => intro i σ; rfl
  | succ k ih =>
    intro i σ
    rw [iterDen, ih, iterDen, Nat.add_right_comm, Nat.add_assoc]

theorem iterTrace_succ (x : String) (f : Env → Env) (l : Env → List CTLeak) :
    ∀ k i σ, iterTrace x f l (k + 1) i σ =
      iterTrace x f l k i σ ++ l (setS (iterDen x f k i σ) x (i + k)) := by
  intro k
  induction k with
  | zero => intro i σ; simp [iterTrace, iterDen]
  | succ k ih =>
    intro i σ
    rw [iterTrace, ih, iterTrace, iterDen, List.append_assoc, Nat.add_right_comm,
      Nat.add_assoc]

theorem arith_limbFree (p : ArithSrc) : p.toSExpr.limbFree := ArithSrc.toSExpr_limbFree p

/-- The arithmetic source trace is empty under the owned model. -/
theorem sexprLeak_arith (p : ArithSrc) (rs : RustState) :
    sexprLeak .owned rs p.toSExpr = [] := by
  cases p with
  | mk dst a op b => cases op <;> rfl

theorem WExpr.limbFree : ∀ e : WExpr, e.toSExpr.limbFree
  | .var _ | .lit _ => trivial
  | .bin op a b => by
    cases op <;>
      exact (show _ ∧ _ from ⟨WExpr.limbFree a, WExpr.limbFree b⟩)

/-- A word expression has an empty source trace under the owned model. -/
theorem WExpr.sexprLeak_nil (rs : RustState) : ∀ e : WExpr, sexprLeak .owned rs e.toSExpr = []
  | .var _ | .lit _ => rfl
  | .bin op a b => by
    cases op <;>
      simp only [WExpr.toSExpr, arithNode, sexprLeak, WExpr.sexprLeak_nil rs a,
        WExpr.sexprLeak_nil rs b, List.nil_append] <;> rfl

theorem sexprLeak_shift (k : ShiftKind) (a c : String) (rs : RustState) :
    sexprLeak .owned rs (k.toSExpr (.SVar a) (.SVar c)) =
      k.leak (rs.rsScalar a) (rs.rsScalar c) := by
  cases k <;> rfl

theorem evalState_shift (k : ShiftKind) (a c : String) (rs : RustState) :
    (k.toSExpr (.SVar a) (.SVar c)).evalState rs = k.eval (rs.rsScalar a) (rs.rsScalar c) := by
  cases k <;> rfl

/-- Two scalar states agree outside the opaque scalars `O`. -/
def AgreeT (O : String → Bool) (σ σ' : Env) : Prop := ∀ v, O v = false → σ v = σ' v

theorem AgreeT.setS {O : String → Bool} {σ σ' : Env} (h : AgreeT O σ σ') (x : String)
    (v v' : Nat) (hv : O x = false → v = v') :
    AgreeT O (LowCTMachine.setS σ x v) (LowCTMachine.setS σ' x v') := by
  intro u hu
  by_cases hux : u = x
  · subst hux; simp [LowCTMachine.setS, hv hu]
  · simp [LowCTMachine.setS, hux, h u hu]

theorem WExpr.eval_congr (σ₁ σ₂ : Env) :
    ∀ e : WExpr, (∀ v ∈ e.vars, σ₁ v = σ₂ v) → e.toSExpr.eval σ₁ = e.toSExpr.eval σ₂
  | .var v, h => h v (by simp [WExpr.vars])
  | .lit _, _ => rfl
  | .bin op a b, h => by
    have ha := WExpr.eval_congr σ₁ σ₂ a (fun v hv => h v (by simp [WExpr.vars, hv]))
    have hb := WExpr.eval_congr σ₁ σ₂ b (fun v hv => h v (by simp [WExpr.vars, hv]))
    cases op <;> simp only [WExpr.toSExpr, arithNode, SExpr.eval, ha, hb]

theorem WExpr.eval_congrT {O : String → Bool} {σ₁ σ₂ : Env} (h : AgreeT O σ₁ σ₂) (e : WExpr)
    (he : e.vars.all (fun v => !O v) = true) : e.toSExpr.eval σ₁ = e.toSExpr.eval σ₂ := by
  refine WExpr.eval_congr σ₁ σ₂ e fun v hv => h v ?_
  have := List.all_eq_true.mp he v hv
  simpa using this

theorem ArithSrc.eval_congr (p : ArithSrc) (σ₁ σ₂ : Env) (ha : σ₁ p.a = σ₂ p.a)
    (hb : σ₁ p.b = σ₂ p.b) : p.toSExpr.eval σ₁ = p.toSExpr.eval σ₂ := by
  cases p with
  | mk d a op b =>
    cases op <;> simp only [ArithSrc.toSExpr, SExpr.eval] at ha hb ⊢ <;> rw [ha, hb]

/-- Every run of `RFor x n body` has the iterated trace and, outside `O`, the
    iterated scalar post-state, given that every run of `body` has the trace and
    post-state of the source. -/
theorem forRun_det (N : Nat) (leafSpec : LeafSpec) (O : String → Bool) (x : String)
    (body : CFSrc)
    (hb : ∀ rs t rs' σ, AgreeT O σ rs.rsScalar →
      RustExecLeak N leafSpec .owned body.toLowCT rs t rs' →
      t = srcLeak body σ ∧ AgreeT O (srcDen body σ) rs'.rsScalar) :
    ∀ (n : Nat) (rs : RustState) (t : List CTLeak) (rs' : RustState) (σ : Env),
      AgreeT O σ rs.rsScalar →
      RustExecLeak N leafSpec .owned (.RFor x n body.toLowCT) rs t rs' →
      t = iterTrace x (srcDen body) (srcLeak body) n 0 σ ∧
        AgreeT O (iterDen x (srcDen body) n 0 σ) rs'.rsScalar := by
  intro n
  induction n with
  | zero => intro rs t rs' σ hag h; cases h; exact ⟨rfl, hag⟩
  | succ n ih =>
    intro rs t rs' σ hag h
    cases h with
    | forSucc _ _ _ _ r1 _ t1 t2 h1 h2 =>
      obtain ⟨rfl, hr1⟩ := ih rs t1 r1 σ hag h1
      obtain ⟨rfl, hr'⟩ := hb _ t2 rs' _ (hr1.setS x n n fun _ => rfl) h2
      rw [iterDen_succ, iterTrace_succ, Nat.zero_add]
      exact ⟨rfl, hr'⟩

/-- Every run of `RWhileNz g body` from a state agreeing with `σ` outside `O` runs
    `k` iterations for some `k` after which the guard of the source iterate is zero
    and before which it is not, and has the guarded-loop trace of `k` iterations. -/
theorem whileRun_det (N : Nat) (leafSpec : LeafSpec) (O : String → Bool) (g : String)
    (hg : O g = false) (body : CFSrc)
    (hb : ∀ rs t rs' σ, AgreeT O σ rs.rsScalar →
      RustExecLeak N leafSpec .owned body.toLowCT rs t rs' →
      t = srcLeak body σ ∧ AgreeT O (srcDen body σ) rs'.rsScalar) :
    ∀ (rs : RustState) (t : List CTLeak) (rs' : RustState),
      RustExecLeak N leafSpec .owned (.RWhileNz g body.toLowCT) rs t rs' →
      ∀ σ, AgreeT O σ rs.rsScalar →
      ∃ k, ((srcDen body)^[k] σ) g = 0 ∧ (∀ j < k, ¬ ((srcDen body)^[j] σ) g = 0) ∧
        t = whileLeak (srcDen body) (srcLeak body) k σ ∧
        AgreeT O ((srcDen body)^[k] σ) rs'.rsScalar := by
  intro rs t rs' h
  generalize hc : LowCT.RWhileNz g body.toLowCT = c at h
  induction h with
  | whileFalse e b rs he =>
    cases hc
    intro σ hag
    exact ⟨0, (hag g hg).trans he, fun j hj => absurd hj (Nat.not_lt_zero _), rfl, hag⟩
  | whileTrue e b rs r1 rs' v t1 t2 hv hv0 hb1 _ _ ih2 =>
    cases hc
    intro σ hag
    obtain ⟨rfl, hag1⟩ := hb _ _ _ σ hag hb1
    obtain ⟨k, hk0, hlt, rfl, hag'⟩ := ih2 rfl _ hag1
    refine ⟨k + 1, ?_, ?_, rfl, ?_⟩
    · rwa [Function.iterate_succ_apply]
    · intro j hj
      cases j with
      | zero =>
        simp only [Function.iterate_zero, id]
        rw [hag g hg, hv]; exact hv0
      | succ j => rw [Function.iterate_succ_apply]; exact hlt j (by omega)
    · rwa [Function.iterate_succ_apply]
  | _ => cases hc

/-- Every run of `c.toLowCT` from a state agreeing with `σ` outside the opaque
    scalars `O` has the trace `srcLeak c σ`, and its scalar post-state agrees
    with `srcDen c σ` outside `O`. -/
theorem srcRun_det (N : Nat) (leafSpec : LeafSpec) (O : String → Bool) :
    ∀ (c : CFSrc), c.taint O = true → ∀ (rs : RustState) (t : List CTLeak) (rs' : RustState)
      (σ : Env), AgreeT O σ rs.rsScalar →
      RustExecLeak N leafSpec .owned c.toLowCT rs t rs' →
      t = srcLeak c σ ∧ AgreeT O (srcDen c σ) rs'.rsScalar
  | .skip, _, rs, t, rs', σ, hag, h => by cases h; exact ⟨rfl, hag⟩
  | .arith p, ht, rs, t, rs', σ, hag, h => by
    cases h
    refine ⟨sexprLeak_arith p rs, ?_⟩
    rw [rsSetScalar_rsScalar, SExpr.evalState_eq_eval rs _ (arith_limbFree p)]
    refine hag.setS _ _ _ fun hd => ?_
    simp only [CFSrc.taint, hd, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at ht
    exact ArithSrc.eval_congr p _ _ (hag _ ht.1) (hag _ ht.2)
  | .setLit d n, _, rs, t, rs', σ, hag, h => by
    cases h; exact ⟨rfl, hag.setS _ _ _ fun _ => rfl⟩
  | .expr d e ts, ht, rs, t, rs', σ, hag, h => by
    cases h
    refine ⟨WExpr.sexprLeak_nil rs e, ?_⟩
    rw [rsSetScalar_rsScalar, SExpr.evalState_eq_eval rs _ (WExpr.limbFree e)]
    refine hag.setS _ _ _ fun hd => ?_
    simp only [CFSrc.taint, hd, Bool.false_or] at ht
    exact WExpr.eval_congrT hag e ht
  | .letU64 x body, ht, rs, t, rs', σ, hag, h => by
    cases h with
    | letU64Zero _ _ _ _ _ hb =>
      exact srcRun_det N leafSpec O body ht _ t rs' _ (hag.setS x 0 0 fun _ => rfl) hb
  | .shift k d a c, ht, rs, t, rs', σ, hag, h => by
    simp only [CFSrc.taint, Bool.and_eq_true, Bool.not_eq_true'] at ht
    cases h
    refine ⟨?_, ?_⟩
    · rw [sexprLeak_shift]; simp only [srcLeak, hag a ht.1, hag c ht.2]
    · rw [rsSetScalar_rsScalar, evalState_shift]
      exact hag.setS _ _ _ fun _ => by rw [hag a ht.1, hag c ht.2]
  | .mulHi d a b lo, ht, rs, t, rs', σ, hag, h => by
    cases h
    refine ⟨rfl, hag.setS _ _ _ fun hd => ?_⟩
    simp only [CFSrc.taint, hd, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at ht
    show sexprMulHiU (σ a) (σ b) = sexprMulHiU (rs.rsScalar a) (rs.rsScalar b)
    rw [hag a ht.1, hag b ht.2]
  | .select dst sel s0 s1, _, rs, t, rs', σ, hag, h => by cases h <;> exact ⟨rfl, hag⟩
  | .arrLoad dst src idx, ht, rs, t, rs', σ, hag, h => by
    simp only [CFSrc.taint, Bool.not_eq_true'] at ht
    cases h with
    | arrLoad _ _ _ _ i _ _ hi _ _ =>
      subst hi; exact ⟨by simp only [srcLeak, hag idx ht], hag⟩
  | .arrStore arr idx src, ht, rs, t, rs', σ, hag, h => by
    simp only [CFSrc.taint, Bool.not_eq_true'] at ht
    cases h with
    | arrStore _ _ _ _ i _ _ hi _ _ =>
      subst hi; exact ⟨by simp only [srcLeak, hag idx ht], hag⟩
  | .seq a b, ht, rs, t, rs', σ, hag, h => by
    simp only [CFSrc.taint, Bool.and_eq_true] at ht
    cases h with
    | seq _ _ _ r1 _ t1 t2 h1 h2 =>
      obtain ⟨rfl, hr1⟩ := srcRun_det N leafSpec O a ht.1 rs t1 r1 σ hag h1
      obtain ⟨rfl, hr'⟩ := srcRun_det N leafSpec O b ht.2 _ t2 rs' _ hr1 h2
      exact ⟨rfl, hr'⟩
  | .ifNz g th el, ht, rs, t, rs', σ, hag, h => by
    simp only [CFSrc.taint, Bool.and_eq_true, Bool.not_eq_true'] at ht
    have hg := hag g ht.1.1
    cases h with
    | ifTrue _ _ _ _ _ v tr hv hv0 hb =>
      obtain ⟨rfl, hr⟩ := srcRun_det N leafSpec O th ht.1.2 rs tr rs' σ hag hb
      have hz : ¬ σ g = 0 := by rw [hg, hv]; exact hv0
      simp only [srcLeak, srcDen, ite_eq_right hz]
      exact ⟨trivial, hr⟩
    | ifFalse _ _ _ _ _ tr hv hb =>
      obtain ⟨rfl, hr⟩ := srcRun_det N leafSpec O el ht.2 rs tr rs' σ hag hb
      have hz : σ g = 0 := hg.trans hv
      simp only [srcLeak, srcDen, ite_eq_left hz]
      exact ⟨trivial, hr⟩
  | .forLit x ctr n body, ht, rs, t, rs', σ, hag, h =>
    forRun_det N leafSpec O x body (srcRun_det N leafSpec O body ht) n rs t rs' σ hag h
  | .forRt x ctr bnd body, ht, rs, t, rs', σ, hag, h => by
    simp only [CFSrc.taint, Bool.and_eq_true, Bool.not_eq_true'] at ht
    cases h with
    | forRuntime _ _ _ _ _ tr hr =>
      have hn : (SExpr.SVar bnd).evalState rs = σ bnd := (hag bnd ht.1).symm
      rw [hn] at hr
      obtain ⟨rfl, hr'⟩ :=
        forRun_det N leafSpec O x body (srcRun_det N leafSpec O body ht.2) _ rs tr rs' σ hag hr
      refine ⟨?_, hr'⟩
      rw [hn]; rfl
  | .ltSet d a b, ht, rs, t, rs', σ, hag, h => by
    simp only [CFSrc.taint, Bool.and_eq_true, Bool.not_eq_true'] at ht
    cases h
    refine ⟨rfl, hag.setS _ _ _ fun _ => ?_⟩
    show (if σ a < σ b then 1 else 0) = if rs.rsScalar a < rs.rsScalar b then 1 else 0
    rw [hag a ht.1, hag b ht.2]
  | .whileNz g body, ht, rs, t, rs', σ, hag, h => by
    simp only [CFSrc.taint, Bool.and_eq_true, Bool.not_eq_true'] at ht
    obtain ⟨k, hk0, hlt, rfl, hag'⟩ := whileRun_det N leafSpec O g ht.1 body
      (srcRun_det N leafSpec O body ht.2) rs t rs' h σ hag
    have hc := whileCount_eq (srcDen body) (fun σ' => σ' g = 0) σ k hk0 hlt
    simp only [srcLeak, srcDen, hc]
    exact ⟨trivial, hag'⟩
  | .call f dest args code, _, rs, t, rs', σ, hag, h => by cases h; exact ⟨rfl, hag⟩
  | .copy dst src tmp, _, rs, t, rs', σ, hag, h => by cases h; exact ⟨rfl, hag⟩
  | .letT x ty body, ht, rs, t, rs', σ, hag, h => by
    cases h with
    | letZero _ _ _ _ _ _ hb =>
      exact srcRun_det N leafSpec O body ht _ _ rs' σ (by exact hag) hb
  | .limbSet loc idx e ts, _, rs, t, rs', σ, hag, h => by
    cases h; exact ⟨WExpr.sexprLeak_nil rs e, hag⟩
  | .limbGet d v idx, ht, rs, t, rs', σ, hag, h => by
    simp only [CFSrc.taint] at ht
    cases h
    exact ⟨rfl, hag.setS _ _ _ fun hd => absurd (ht ▸ hd) (by simp)⟩

/-- Runs of `RFor x n body` exist when runs of `body` exist from every state. -/
theorem forRun_exists (N : Nat) (leafSpec : LeafSpec) (x : String) (body : LowCT)
    (hb : ∀ rs, ∃ t rs', RustExecLeak N leafSpec .owned body rs t rs') :
    ∀ (n : Nat) (rs : RustState), ∃ t rs', RustExecLeak N leafSpec .owned (.RFor x n body) rs t rs' := by
  intro n
  induction n with
  | zero => intro rs; exact ⟨_, _, .forZero _ _ _⟩
  | succ n ih =>
    intro rs
    obtain ⟨t1, r1, h1⟩ := ih rs
    obtain ⟨t2, r2, h2⟩ := hb (rsSetScalar r1 x n)
    exact ⟨_, _, .forSucc _ _ _ _ _ _ _ _ h1 h2⟩

/-- A tower-free program has a run from every state. -/
theorem srcRun_exists (N : Nat) (leafSpec : LeafSpec) :
    ∀ (c : CFSrc), c.towerFree = true → ∀ (rs : RustState),
      ∃ t rs', RustExecLeak N leafSpec .owned c.toLowCT rs t rs'
  | .skip, _, rs => ⟨_, _, .skip rs⟩
  | .arith p, _, rs => ⟨_, _, .scalarSetExpr p.dst p.toSExpr rs⟩
  | .setLit d n, _, rs => ⟨_, _, .scalarSet d n rs⟩
  | .expr d e _, _, rs => ⟨_, _, .scalarSetExpr d e.toSExpr rs⟩
  | .letU64 x body, h, rs => by
    obtain ⟨t1, r1, h1⟩ := srcRun_exists N leafSpec body h (rsSetScalar rs x 0)
    exact ⟨_, _, .letU64Zero _ _ _ _ _ h1⟩
  | .shift k d a c, _, rs => ⟨_, _, .scalarSetExpr _ _ rs⟩
  | .mulHi d a b _, _, rs => ⟨_, _, .scalarSetExpr _ _ rs⟩
  | .seq a b, h, rs => by
    simp only [CFSrc.towerFree, Bool.and_eq_true] at h
    obtain ⟨t1, r1, h1⟩ := srcRun_exists N leafSpec a h.1 rs
    obtain ⟨t2, r2, h2⟩ := srcRun_exists N leafSpec b h.2 r1
    exact ⟨_, _, .seq _ _ _ _ _ _ _ h1 h2⟩
  | .ifNz g t e, h, rs => by
    simp only [CFSrc.towerFree, Bool.and_eq_true] at h
    by_cases hz : rs.rsScalar g = 0
    · obtain ⟨t1, r1, h1⟩ := srcRun_exists N leafSpec e h.2 rs
      exact ⟨_, _, .ifFalse _ _ _ _ _ _ hz h1⟩
    · obtain ⟨t1, r1, h1⟩ := srcRun_exists N leafSpec t h.1 rs
      exact ⟨_, _, .ifTrue _ _ _ _ _ _ _ rfl hz h1⟩
  | .forLit x _ n body, h, rs =>
    forRun_exists N leafSpec x _ (srcRun_exists N leafSpec body h) n rs
  | .forRt x _ bnd body, h, rs => by
    obtain ⟨t1, r1, h1⟩ := forRun_exists N leafSpec x _ (srcRun_exists N leafSpec body h) _ rs
    exact ⟨_, _, .forRuntime _ _ _ _ _ _ h1⟩
  | .ltSet d a b, _, rs => ⟨_, _, .scalarSetExpr _ _ rs⟩
  | .select .., h, _ | .arrLoad .., h, _ | .arrStore .., h, _ | .whileNz .., h, _
  | .call .., h, _ | .copy .., h, _ | .letT .., h, _ | .limbSet .., h, _
  | .limbGet .., h, _ => by
    simp [CFSrc.towerFree] at h

/-! ### 3.2 Runs of programs whose tower accesses are bound -/

/-- The type of the tower name `x` in the bindings `Γ`, the first binding of `x`. -/
def lookT : List (String × TowerType) → String → Option TowerType
  | [], _ => none
  | (y, t) :: Γ, x => if x = y then some t else lookT Γ x

theorem lookT_mem : ∀ (Γ : List (String × TowerType)) (x : String) (t : TowerType),
    lookT Γ x = some t → ∃ p ∈ Γ, p.1 = x
  | [], _, _, h => by simp [lookT] at h
  | (y, u) :: Γ, x, t, h => by
    unfold lookT at h
    split at h
    · exact ⟨(y, u), List.mem_cons_self .., by simp_all⟩
    · obtain ⟨p, hp, hpx⟩ := lookT_mem Γ x t h
      exact ⟨p, List.mem_cons_of_mem _ hp, hpx⟩

/-- Every binding of `Γ` is a binding of `Γ'`, as a Boolean. -/
def subB (Γ Γ' : List (String × TowerType)) : Bool :=
  Γ.all fun p => decide (lookT Γ' p.1 = lookT Γ p.1)

theorem subB_spec {Γ Γ' : List (String × TowerType)} (h : subB Γ Γ' = true) (x : String)
    (t : TowerType) (hx : lookT Γ x = some t) : lookT Γ' x = some t := by
  obtain ⟨p, hp, rfl⟩ := lookT_mem Γ x t hx
  have := List.all_eq_true.mp h p hp
  simp only [decide_eq_true_eq] at this
  rw [this, hx]

/-- The tower heap holds a value of the bound type at every name bound in `Γ`. -/
def TowerInv (Γ : List (String × TowerType)) (rs : RustState) : Prop :=
  ∀ x t, lookT Γ x = some t → ∃ v, rs.rsTower x = some ⟨t, v⟩

/-- The tower bindings after a program from the bindings `Γ`, or `none` when a leaf
    call, copy or limb store accesses a name not bound at its type, or the program
    has a select, an array access or a guarded loop. A binding `letT` adds its
    name; a branch or a loop body must keep the bindings it starts from. -/
def towerB (Γ : List (String × TowerType)) : CFSrc → Option (List (String × TowerType))
  | .skip | .arith _ | .setLit .. | .expr .. | .shift .. | .mulHi .. | .ltSet ..
  | .limbGet .. => some Γ
  | .letU64 _ b => towerB Γ b
  | .letT x t b => towerB ((x, t) :: Γ) b
  | .call _ dest args _ =>
      if decide (lookT Γ dest.locVar = some dest.locSrc) &&
          args.all (fun a => decide (lookT Γ a.locVar = some a.locSrc)) then some Γ else none
  | .copy dst src _ =>
      if decide (lookT Γ dst.locVar = some dst.locSrc) &&
          decide (lookT Γ src.locVar = some dst.locSrc) && decide (src.locSrc = dst.locSrc)
      then some Γ else none
  | .limbSet loc _ _ _ =>
      if decide (lookT Γ loc.locVar = some loc.locSrc) then some Γ else none
  | .seq a b => (towerB Γ a).bind fun Γ' => towerB Γ' b
  | .ifNz _ t e =>
      match towerB Γ t, towerB Γ e with
      | some Γt, some Γe => if subB Γ Γt && subB Γ Γe then some Γ else none
      | _, _ => none
  | .forLit _ _ _ b | .forRt _ _ _ b =>
      match towerB Γ b with
      | some Γ' => if subB Γ Γ' then some Γ else none
      | none => none
  | .select .. | .arrLoad .. | .arrStore .. | .whileNz .. => none

/-- Whether every tower access of a program is to a name an enclosing `letT` binds at
    the accessed type (`towerB` from no binding). -/
def CFSrc.towerOk (c : CFSrc) : Bool := (towerB [] c).isSome

theorem TowerInv.setScalar {Γ : List (String × TowerType)} {rs : RustState} (h : TowerInv Γ rs)
    (x : String) (v : Nat) : TowerInv Γ (rsSetScalar rs x v) := h

theorem TowerInv.update {Γ : List (String × TowerType)} {rs : RustState} (h : TowerInv Γ rs)
    (l : Located) (hl : lookT Γ l.locVar = some l.locSrc) (v : RustVal l.locDst) :
    TowerInv Γ (locatedUpdate rs l v) := by
  intro x t hx
  by_cases hxl : x = l.locVar
  · subst hxl
    rw [hl] at hx
    cases hx
    exact ⟨v, by simp [locatedUpdate, rsSetTower]⟩
  · obtain ⟨w, hw⟩ := h x t hx
    exact ⟨w, by simp [locatedUpdate, rsSetTower, hxl, hw]⟩

theorem TowerInv.lookup {Γ : List (String × TowerType)} {rs : RustState} (h : TowerInv Γ rs)
    (l : Located) (hl : lookT Γ l.locVar = some l.locSrc) :
    ∃ v, locatedLookup rs l = some v := by
  obtain ⟨v, hv⟩ := h _ _ hl
  exact ⟨v, by simp [locatedLookup, hv]⟩

/-- Runs of `RFor x n body` exist and keep `TowerInv Γ` when runs of `body` exist
    from every state satisfying it and keep it. -/
theorem forRun_exists_inv (N : Nat) (leafSpec : LeafSpec) (x : String) (body : LowCT)
    (Γ : List (String × TowerType))
    (hb : ∀ rs, TowerInv Γ rs → ∃ t rs', RustExecLeak N leafSpec .owned body rs t rs' ∧
      TowerInv Γ rs') :
    ∀ (n : Nat) (rs : RustState), TowerInv Γ rs →
      ∃ t rs', RustExecLeak N leafSpec .owned (.RFor x n body) rs t rs' ∧ TowerInv Γ rs' := by
  intro n
  induction n with
  | zero => intro rs h; exact ⟨_, _, .forZero _ _ _, h⟩
  | succ n ih =>
    intro rs h
    obtain ⟨t1, r1, h1, i1⟩ := ih rs h
    obtain ⟨t2, r2, h2, i2⟩ := hb (rsSetScalar r1 x n) (i1.setScalar x n)
    exact ⟨_, _, .forSucc _ _ _ _ _ _ _ _ h1 h2, i2⟩

/-- A program accepted by `towerB Γ` has a run from every state satisfying
    `TowerInv Γ`, ending in a state satisfying the returned bindings. -/
theorem srcRun_exists_tower (N : Nat) (leafSpec : LeafSpec) :
    ∀ (c : CFSrc) (Γ Γ' : List (String × TowerType)), towerB Γ c = some Γ' →
      ∀ (rs : RustState), TowerInv Γ rs →
      ∃ t rs', RustExecLeak N leafSpec .owned c.toLowCT rs t rs' ∧ TowerInv Γ' rs'
  | .skip, Γ, Γ', h, rs, hi => by
    simp only [towerB, Option.some.injEq] at h; subst h; exact ⟨_, _, .skip rs, hi⟩
  | .arith p, Γ, Γ', h, rs, hi => by
    simp only [towerB, Option.some.injEq] at h; subst h
    exact ⟨_, _, .scalarSetExpr p.dst p.toSExpr rs, hi.setScalar _ _⟩
  | .setLit d n, Γ, Γ', h, rs, hi => by
    simp only [towerB, Option.some.injEq] at h; subst h
    exact ⟨_, _, .scalarSet d n rs, hi.setScalar _ _⟩
  | .expr d e _, Γ, Γ', h, rs, hi | .shift _ d _ _, Γ, Γ', h, rs, hi
  | .mulHi d _ _ _, Γ, Γ', h, rs, hi | .ltSet d _ _, Γ, Γ', h, rs, hi
  | .limbGet d _ _, Γ, Γ', h, rs, hi => by
    simp only [towerB, Option.some.injEq] at h; subst h
    exact ⟨_, _, .scalarSetExpr _ _ rs, hi.setScalar _ _⟩
  | .letU64 x b, Γ, Γ', h, rs, hi => by
    obtain ⟨t, r, hr, i⟩ := srcRun_exists_tower N leafSpec b Γ Γ' h _ (hi.setScalar x 0)
    exact ⟨_, _, .letU64Zero _ _ _ _ _ hr, i⟩
  | .letT x ty b, Γ, Γ', h, rs, hi => by
    have hi' : TowerInv ((x, ty) :: Γ) (rsSetTower rs x ⟨ty, default⟩) := by
      intro y u hy
      by_cases hyx : y = x
      · subst hyx
        simp only [lookT, ite_true, Option.some.injEq] at hy
        subst hy
        exact ⟨default, by simp [rsSetTower]⟩
      · simp only [lookT, hyx, ite_false] at hy
        obtain ⟨w, hw⟩ := hi y u hy
        exact ⟨w, by simp [rsSetTower, hyx, hw]⟩
    obtain ⟨t, r, hr, i⟩ := srcRun_exists_tower N leafSpec b _ Γ' h _ hi'
    exact ⟨_, _, .letZero _ _ _ _ _ _ hr, i⟩
  | .call f dest args code, Γ, Γ', h, rs, hi => by
    simp only [towerB] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
      obtain ⟨old, hold⟩ := hi.lookup dest hc.1
      have hargs : ∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩ :=
        fun a ha => hi _ _ (hc.2 a ha)
      exact ⟨_, _, .call f dest args rs old _ hold rfl hargs, hi.update dest hc.1 _⟩
    · cases h
  | .copy dst src tmp, Γ, Γ', h, rs, hi => by
    simp only [towerB] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hd, hs⟩, hty⟩ := hc
      obtain ⟨sv, hsv⟩ := hi.lookup src (hty ▸ hs)
      exact ⟨_, _, .copy dst src rs hty sv hsv, hi.update dst hd _⟩
    · cases h
  | .limbSet loc idx e ts, Γ, Γ', h, rs, hi => by
    simp only [towerB] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      simp only [decide_eq_true_eq] at hc
      obtain ⟨old, hold⟩ := hi.lookup loc hc
      exact ⟨_, _, .limbStoreExpr loc idx _ rs old hold, hi.update loc hc _⟩
    · cases h
  | .seq a b, Γ, Γ', h, rs, hi => by
    simp only [towerB, Option.bind_eq_some_iff] at h
    obtain ⟨Γa, ha, hb⟩ := h
    obtain ⟨t1, r1, h1, i1⟩ := srcRun_exists_tower N leafSpec a Γ Γa ha rs hi
    obtain ⟨t2, r2, h2, i2⟩ := srcRun_exists_tower N leafSpec b Γa Γ' hb r1 i1
    exact ⟨_, _, .seq _ _ _ _ _ _ _ h1 h2, i2⟩
  | .ifNz g t e, Γ, Γ', h, rs, hi => by
    simp only [towerB] at h
    split at h
    · rename_i Γt Γe ht he
      split at h
      · rename_i hs
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.and_eq_true] at hs
        by_cases hz : rs.rsScalar g = 0
        · obtain ⟨t1, r1, h1, i1⟩ := srcRun_exists_tower N leafSpec e Γ Γe he rs hi
          exact ⟨_, _, .ifFalse _ _ _ _ _ _ hz h1,
            fun x u hx => i1 x u (subB_spec hs.2 x u hx)⟩
        · obtain ⟨t1, r1, h1, i1⟩ := srcRun_exists_tower N leafSpec t Γ Γt ht rs hi
          exact ⟨_, _, .ifTrue _ _ _ _ _ _ _ rfl hz h1,
            fun x u hx => i1 x u (subB_spec hs.1 x u hx)⟩
      · cases h
    · cases h
  | .forLit x ctr n b, Γ, Γ', h, rs, hi => by
    simp only [towerB] at h
    split at h
    · rename_i Γb hb
      split at h
      · rename_i hs
        simp only [Option.some.injEq] at h; subst h
        exact forRun_exists_inv N leafSpec x _ Γ (fun rs' hi' => by
          obtain ⟨t, r, hr, i⟩ := srcRun_exists_tower N leafSpec b Γ Γb hb rs' hi'
          exact ⟨t, r, hr, fun y u hy => i y u (subB_spec hs y u hy)⟩) n rs hi
      · cases h
    · cases h
  | .forRt x ctr bnd b, Γ, Γ', h, rs, hi => by
    simp only [towerB] at h
    split at h
    · rename_i Γb hb
      split at h
      · rename_i hs
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨t, r, hr, i⟩ := forRun_exists_inv N leafSpec x _ Γ (fun rs' hi' => by
          obtain ⟨t, r, hr, i⟩ := srcRun_exists_tower N leafSpec b Γ Γb hb rs' hi'
          exact ⟨t, r, hr, fun y u hy => i y u (subB_spec hs y u hy)⟩) _ rs hi
        exact ⟨_, _, .forRuntime _ _ _ _ _ _ hr, i⟩
      · cases h
    · cases h
  | .select .., _, _, h, _, _ | .arrLoad .., _, _, h, _, _ | .arrStore .., _, _, h, _, _
  | .whileNz .., _, _, h, _, _ => by simp [towerB] at h

/-! ## 4. The machine side -/

/-! ### 4.1 Mnemonics and denotation of the new instructions -/

/-- The owned mnemonic of the arithmetic instruction is `sexprMnem` of the source
    expression: the lowering emits `MOV` and then that mnemonic. -/
theorem lowerArith_mnem (ρ : RegMap) (p : ArithSrc) :
    (lowerArith ρ p).map JInstr.mnem = X86Mnem.mov :: (sexprMnem p.toSExpr).toList := by
  cases p with
  | mk dst a op b => cases op <;> rfl

/-- The lowering of a shift by a scalar count emits exactly the mnemonic
    `sexprMnem` assigns to the source expression (`SHRX`, `SHLX`, `SARX`). -/
theorem lowerShift_mnem (ρ : RegMap) (k : ShiftKind) (d a c : String) :
    [(k.toJInstr (ρ d) (ρ a) (ρ c)).mnem] = (sexprMnem (k.toSExpr (.SVar a) (.SVar c))).toList := by
  cases k <;> rfl

/-- The lowering of the high word of the unsigned wide multiply emits `MULX`, the
    mnemonic `sexprMnem` assigns to `SMulHiU`. -/
theorem lowerMulHi_mnem (ρ : RegMap) (d a b lo : String) :
    [(JInstr.mulx (w := 64) (ρ d) lo (.reg (ρ a)) (.reg (ρ b))).mnem] =
      (sexprMnem (.SMulHiU (.SVar a) (.SVar b))).toList := rfl

theorem x86_SARX_ofNat (a c : Nat) (hc : c < 64) :
    x86_SARX (BitVec.ofNat 64 a) (BitVec.ofNat 64 c) =
      BitVec.ofNat 64 (sexprOfSignedInt64 (sexprToSignedInt64 a >>> c)) := by
  simp only [x86_SARX, wsar, shiftCount, BitVec.toNat_ofNat, sexprOfSignedInt64,
    sexprToSignedInt64, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), VIR.shiftMask_of_lt hc,
    show min 64 c = c by omega, ← BitVec.toInt_sshiftRight, BitVec.ofInt_toInt]

theorem x86_SHRX_ofNat (a c : Nat) (ha : a < 2 ^ 64) (hc : c < 64) :
    x86_SHRX (BitVec.ofNat 64 a) (BitVec.ofNat 64 c) = BitVec.ofNat 64 (a >>> c) := by
  simp only [x86_SHRX, wshr, shiftCount, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), VIR.shiftMask_of_lt hc,
    show min 64 c = c by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) ha)]

theorem x86_SHLX_ofNat (a c : Nat) (hc : c < 64) :
    x86_SHLX (BitVec.ofNat 64 a) (BitVec.ofNat 64 c) = BitVec.ofNat 64 (a <<< c) := by
  simp only [x86_SHLX, wshl, shiftCount, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), VIR.shiftMask_of_lt hc,
    show min 64 c = c by omega]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftLeft_eq, Nat.mul_mod]

/-- The denotation of the shifts: on a shifted value below `2^64` and a count
    below `64`, the BMI2 instruction computes the truncated source value. -/
theorem ShiftKind.x86_ofNat (k : ShiftKind) (a c : Nat) (ha : a < 2 ^ 64) (hc : c < 64) :
    k.x86 (BitVec.ofNat 64 a) (BitVec.ofNat 64 c) = BitVec.ofNat 64 (k.eval a c) := by
  cases k
  · exact x86_SHRX_ofNat a c ha hc
  · exact x86_SHLX_ofNat a c hc
  · exact x86_SARX_ofNat a c hc

/-- The high word of `MULX` is the truncated `SMulHiU` value. -/
theorem x86_MULX_hi_ofNat (a b : Nat) :
    (x86_MULX_lo_hi (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)).2 =
      BitVec.ofNat 64 (sexprMulHiU a b) := by
  simp [x86_MULX_lo_hi, wumul, sexprMulHiU, high_bits, Nat.shiftRight_eq_div_pow]

theorem evalInstr_shift (k : ShiftKind) (s : JState 64) (d a c : String) :
    evalInstr s (k.toJInstr d a c) = s.setReg d (k.x86 (s.get a) (s.get c)) := by
  cases k <;> rfl

theorem evalInstr_mulx_get (s : JState 64) (h l : String) (a b : JOperand) (r : String) :
    (evalInstr s (.mulx h l a b)).get r =
      if r = h then (x86_MULX_lo_hi (a.eval s) (b.eval s)).2
      else if r = l then (x86_MULX_lo_hi (a.eval s) (b.eval s)).1 else s.get r := by
  simp only [evalInstr, JState.get, JState.setReg]

theorem lowerSelect_get (ρ τ : RegMap) (dst : Located) (sel : String) (s0 s1 : Located)
    (s : JState 64) (r : String) (hr : r ≠ τ dst.locVar) :
    (runBlock s (lowerSelect ρ τ dst sel s0 s1)).get r = s.get r := by
  simp [lowerSelect, evalInstr, JState.setReg, JState.writeB5, hr]

/-! ### 4.2 Leakage of the new leaves -/

/-- The select lowering has an empty machine trace under DOITM. -/
theorem blockLeakCT_lowerSelect (ρ τ : RegMap) (dst : Located) (sel : String)
    (s0 s1 : Located) (s : JState 64) :
    blockLeakCT .doitm s (lowerSelect ρ τ dst sel s0 s1) = [] := rfl

/-- `MULX` has an empty machine trace under DOITM. -/
theorem blockLeakCT_mulx (s : JState 64) (h l : String) (a b : JOperand) :
    blockLeakCT .doitm s [.mulx h l a b] = [] := rfl

/-- The arithmetic lowering has an empty machine trace under DOITM. -/
theorem blockLeakCT_lowerArith (ρ : RegMap) (p : ArithSrc) (s : JState 64) :
    blockLeakCT .doitm s (lowerArith ρ p) = [] := by
  cases p with
  | mk dst a op b => cases op <;> rfl

theorem blockLeakCT_shift (k : ShiftKind) (s : JState 64) (d a c : String) :
    blockLeakCT .doitm s [k.toJInstr d a c] = k.leak (s.get a).toNat (s.get c).toNat := by
  cases k <;> rfl

theorem blockLeakCT_append (r : DoitRegime) :
    ∀ (s : JState 64) (l₁ l₂ : List (JInstr 64)),
      blockLeakCT r s (l₁ ++ l₂) = blockLeakCT r s l₁ ++ blockLeakCT r (runBlock s l₁) l₂
  | _, [], _ => rfl
  | s, i :: is, l₂ => by
    rw [List.cons_append, blockLeakCT_cons, blockLeakCT_cons, blockLeakCT_append r _ is l₂,
      runBlock_cons, List.append_assoc]

/-- The lowering of a word expression has an empty machine trace under DOITM. -/
theorem blockLeakCT_lowerW (ρ : RegMap) :
    ∀ (e : WExpr) (ts : List String) (s : JState 64), blockLeakCT .doitm s (lowerW ρ ts e) = []
  | e, [], _ => by cases e <;> rfl
  | .var _, _ :: _, _ => rfl
  | .lit _, _ :: _, _ => rfl
  | .bin op a b, t :: ts, s => by
    rw [lowerW, blockLeakCT_append, blockLeakCT_append, blockLeakCT_lowerW ρ a,
      blockLeakCT_lowerW ρ b]
    cases op <;> rfl

/-- The copy block has the trace `copyLeak` from every state. -/
theorem blockLeakCT_copyBlk (dst src t : String) :
    ∀ (n : Nat) (s : JState 64), blockLeakCT .doitm s (copyBlk dst src t n) = copyLeak dst src n
  | 0, _ => rfl
  | n + 1, s => by
    rw [copyBlk, blockLeakCT_append, blockLeakCT_copyBlk dst src t n, copyLeak]
    simp [instrLeakCT, instrLeak, mleakToCT, JInstr.mnem, DoitRegime.leaksOperands,
      X86Mnem.timing]

/-- `CMP; SETC` has an empty machine trace under DOITM. -/
theorem blockLeakCT_cmp_setc (s : JState 64) (d a b : String) :
    blockLeakCT .doitm s [.cmp a (.reg b), .setc d] = [] := by
  simp [instrLeakCT, instrLeak, JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing]

/-- The carry flag of `SUB` is the unsigned borrow. -/
theorem x86_SUB_cf (x y : BitVec 64) :
    (x86_SUB x y).cf = some (decide (x.toNat < y.toNat)) := by
  simp only [x86_SUB, wunsigned, BitVec.toNat_sub, Option.some.injEq]
  have hx := x.isLt
  have hy := y.isLt
  apply decide_eq_decide.mpr
  omega

/-- `CMP a, b; SETC d` writes to `d` the unsigned comparison `a < b` as `0` or `1`. -/
theorem cmp_setc_get (s : JState 64) (d a b : String) :
    (evalInstr (evalInstr s (.cmp a (.reg b))) (.setc d)).get d =
      if (s.get a).toNat < (s.get b).toNat then 1 else 0 := by
  simp only [evalInstr, JState.flagB, x86_CMP, JOperand.eval, JState.get_setReg_same]
  simp only [JState.writeB5, x86_SUB_cf, Option.getD_some, decide_eq_true_eq]

theorem cmp_setc_get_other (s : JState 64) (d a b r : String) (hr : r ≠ d) :
    (evalInstr (evalInstr s (.cmp a (.reg b))) (.setc d)).get r = s.get r := by
  simp only [evalInstr]
  rw [JState.get_setReg_other _ _ _ _ hr, JState.get_writeB5]

/-! ### 4.3 Preservation of registers outside the image of `ρ` -/

theorem copyBlk_get_other (dst src t r : String) (hr : r ≠ t) :
    ∀ (n : Nat) (s : JState 64), (runBlock s (copyBlk dst src t n)).get r = s.get r
  | 0, _ => rfl
  | n + 1, s => by
    have ih := copyBlk_get_other dst src t r hr n s
    rw [copyBlk, runBlock_append, runBlock_cons, runBlock_cons, runBlock_nil]
    simp only [evalInstr, JState.store, JState.get, JState.setReg] at ih ⊢
    simp [hr, ih]

theorem evalInstr_mov_reg (s : JState 64) (d r : String) :
    evalInstr s (.mov d (.reg r)) = s.setReg d (s.get r) := by
  simp [evalInstr, x86_MOV, JOperand.eval]

/-- A register outside the temporaries keeps its value across the lowering of a
    word expression. -/
theorem lowerW_get_other (ρ : RegMap) :
    ∀ (e : WExpr) (ts : List String) (s : JState 64) (r : String), r ∉ ts →
      (runBlock s (lowerW ρ ts e)).get r = s.get r
  | e, [], _, _, _ => by cases e <;> rfl
  | .var v, t :: _, s, r, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [lowerW, runBlock_cons, runBlock_nil]
    rw [evalInstr_mov_reg, JState.get_setReg_other _ _ _ _ h.1]
  | .lit n, t :: _, s, r, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [lowerW, runBlock_cons, runBlock_nil]
    rw [evalInstr_movImm, JState.get_setReg_other _ _ _ _ h.1]
  | .bin op a b, t :: ts, s, r, h => by
    have h' := h
    simp only [List.mem_cons, not_or] at h'
    rw [lowerW, runBlock_append, runBlock_append, runBlock_cons, runBlock_nil,
      ArithOp.toJInstr_get_other _ _ _ _ _ h'.1, lowerW_get_other ρ b ts _ r h'.2,
      lowerW_get_other ρ a (t :: ts) s r h]

theorem iterate_get (B : MCF) (r : String) (h : ∀ s, (mcfExec s B).get r = s.get r) :
    ∀ (k : Nat) (s : JState 64), ((fun s' => mcfExec s' B)^[k] s).get r = s.get r
  | 0, _ => rfl
  | k + 1, s => by rw [Function.iterate_succ_apply, iterate_get B r h k, h]

theorem evalInstr_add_imm_get (s : JState 64) (d r : String) (n : Nat) :
    (evalInstr s (.add d (.imm n))).get r = if r = d then s.get d + BitVec.ofNat 64 n
      else s.get r := by
  by_cases h : r = d
  · subst h; simp [evalInstr, x86_ADD, rflags_of_aluop, JState.writeB5W, JState.get]
  · simp [evalInstr, x86_ADD, rflags_of_aluop, JState.writeB5W, JState.get, h]

theorem loopBody_get (ρ : RegMap) (x ctr : String) (B : MCF) (r : String) (hx : r ≠ ρ x)
    (hc : r ≠ ctr) (hB : ∀ s, (mcfExec s B).get r = s.get r) (s : JState 64) :
    (mcfExec s (loopBody ρ x ctr B)).get r = s.get r := by
  simp only [loopBody, mcfExec, runBlock_cons, runBlock_nil]
  rw [evalInstr_add_imm_get, ite_eq_right hc, hB, evalInstr_mov_reg, JState.get_setReg_other _ _ _ _ hx]

/-- A register outside the image of `ρ` and outside `c.writes τ` keeps its value
    across the lowered program. -/
theorem lowerCF_preserves (ρ τ : RegMap) (r : String) (hr : ∀ v, ρ v ≠ r) :
    ∀ (c : CFSrc), r ∉ c.writes τ → ∀ s, (mcfExec s (lowerCF ρ τ c)).get r = s.get r
  | .skip, _, s => rfl
  | .arith p, _, s => by
    simp only [lowerCF, mcfExec, lowerArith, runBlock_cons, runBlock_nil]
    have hd : r ≠ ρ p.dst := fun h => hr p.dst h.symm
    rw [ArithOp.toJInstr_get_other _ _ _ _ _ hd, evalInstr_mov_reg,
      JState.get_setReg_other _ _ _ _ hd]
  | .setLit d n, _, s => by
    simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil]
    rw [evalInstr_movImm, JState.get_setReg_other _ _ _ _ (fun h => hr d h.symm)]
  | .expr d e ts, h, s => by
    simp only [CFSrc.writes] at h
    simp only [lowerCF, mcfExec]
    rw [runBlock_append, runBlock_cons, runBlock_nil, evalInstr_mov_reg,
      JState.get_setReg_other _ _ _ _ (fun h' => hr d h'.symm), lowerW_get_other ρ e ts s r h]
  | .letU64 x body, h, s => by
    simp only [CFSrc.writes] at h
    simp only [lowerCF, mcfExec]
    rw [lowerCF_preserves ρ τ r hr body h, runBlock_cons, runBlock_nil, evalInstr_movImm,
      JState.get_setReg_other _ _ _ _ (fun h' => hr x h'.symm)]
  | .shift k d a c, _, s => by
    simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil]
    rw [evalInstr_shift, JState.get_setReg_other _ _ _ _ (fun h => hr d h.symm)]
  | .mulHi d a b lo, h, s => by
    simp only [CFSrc.writes, List.mem_singleton] at h
    simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil]
    rw [evalInstr_mulx_get, ite_eq_right (fun h' => hr d h'.symm), ite_eq_right h]
  | .select dst sel s0 s1, h, s => by
    simp only [CFSrc.writes, List.mem_singleton] at h
    exact lowerSelect_get ρ τ dst sel s0 s1 s r h
  | .arrLoad dst src idx, h, s => by
    simp only [CFSrc.writes, List.mem_singleton] at h
    simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, evalInstr]
    exact JState.get_setReg_other _ _ _ _ h
  | .arrStore arr idx src, _, s => by
    simp [lowerCF, mcfExec, evalInstr, JState.storeIdx, JState.store]
  | .seq a b, h, s => by
    simp only [CFSrc.writes, List.mem_append, not_or] at h
    rw [lowerCF, mcfExec, lowerCF_preserves ρ τ r hr b h.2, lowerCF_preserves ρ τ r hr a h.1]
  | .ifNz g t e, h, s => by
    simp only [CFSrc.writes, List.mem_append, not_or] at h
    rw [lowerCF, mcfExec]
    split
    · exact lowerCF_preserves ρ τ r hr e h.2 s
    · exact lowerCF_preserves ρ τ r hr t h.1 s
  | .forLit x ctr n body, h, s => by
    simp only [CFSrc.writes, List.mem_cons, not_or] at h
    have hB := loopBody_get ρ x ctr _ r (fun h' => hr x h'.symm) h.1
      (lowerCF_preserves ρ τ r hr body h.2)
    simp only [lowerCF, mcfExec]
    rw [iterate_get _ r hB, runBlock_cons, runBlock_nil, evalInstr_movImm,
      JState.get_setReg_other _ _ _ _ h.1]
  | .forRt x ctr bnd body, h, s => by
    simp only [CFSrc.writes, List.mem_cons, not_or] at h
    have hB := loopBody_get ρ x ctr _ r (fun h' => hr x h'.symm) h.1
      (lowerCF_preserves ρ τ r hr body h.2)
    simp only [lowerCF, mcfExec]
    rw [iterate_get _ r hB, runBlock_cons, runBlock_nil, evalInstr_movImm,
      JState.get_setReg_other _ _ _ _ h.1]
  | .ltSet d a b, _, s => by
    simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil]
    exact cmp_setc_get_other s _ _ _ r (fun h => hr d h.symm)
  | .whileNz g body, h, s => by
    simp only [CFSrc.writes] at h
    simp only [lowerCF, mcfExec]
    exact iterate_get _ r (lowerCF_preserves ρ τ r hr body h) _ s
  | .call _ _ _ code, h, s => code.get_other s r h
  | .copy dst src tmp, h, s => by
    simp only [CFSrc.writes, List.mem_singleton] at h
    exact copyBlk_get_other _ _ _ r h _ s
  | .letT _ _ body, h, s => lowerCF_preserves ρ τ r hr body h s
  | .limbSet loc idx e ts, h, s => by
    simp only [CFSrc.writes] at h
    simp only [lowerCF, mcfExec]
    rw [runBlock_append, runBlock_cons, runBlock_nil]
    simp only [evalInstr, JState.store]
    exact lowerW_get_other ρ e ts s r h
  | .limbGet d v idx, _, s => by
    simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, evalInstr]
    exact JState.get_setReg_other _ _ _ _ (fun h => hr d h.symm)

/-! ### 4.4 The simulation and the leak transformer -/

/-- The scalar state relation: register `ρ v` holds the truncation of `σ v`.
    `StateMatch ρ rs js` is `SMatch ρ rs.rsScalar js`. -/
def SMatch (ρ : RegMap) (σ : Env) (js : JState 64) : Prop :=
  ∀ v, js.get (ρ v) = BitVec.ofNat 64 (σ v)

/-- The scalar state relation outside the opaque scalars `O`: register `ρ v`
    holds the truncation of `σ v` for every `v` outside `O`. -/
def SMatchT (O : String → Bool) (ρ : RegMap) (σ : Env) (js : JState 64) : Prop :=
  ∀ v, O v = false → js.get (ρ v) = BitVec.ofNat 64 (σ v)

theorem SMatch.toT {ρ : RegMap} {σ : Env} {js : JState 64} (h : SMatch ρ σ js)
    (O : String → Bool) : SMatchT O ρ σ js := fun v _ => h v

/-- The scalar state that agrees with `σ` outside `O` and with the machine
    registers on `O`. -/
def fillEnv (O : String → Bool) (ρ : RegMap) (σ : Env) (js : JState 64) : Env :=
  fun v => if O v then (js.get (ρ v)).toNat else σ v

theorem SMatchT.fill {O : String → Bool} {ρ : RegMap} {σ : Env} {js : JState 64}
    (h : SMatchT O ρ σ js) : SMatch ρ (fillEnv O ρ σ js) js := by
  intro v
  by_cases hv : O v = true
  · simp [fillEnv, hv]
  · simp only [fillEnv, hv]; exact h v (by simpa using hv)

theorem fillEnv_of_false {O : String → Bool} {ρ : RegMap} {σ : Env} {js : JState 64} {v : String}
    (hv : O v = false) : fillEnv O ρ σ js v = σ v := by
  simp [fillEnv, hv]

theorem SMatchT.of_regs {O : String → Bool} {ρ : RegMap} {σ : Env} {js js' : JState 64}
    (h : SMatchT O ρ σ js) (hr : ∀ v, js'.get (ρ v) = js.get (ρ v)) : SMatchT O ρ σ js' :=
  fun v hv => (hr v).trans (h v hv)

theorem SMatchT.setS {O : String → Bool} {ρ : RegMap} {σ : Env} {js : JState 64}
    (hm : SMatchT O ρ σ js) (d : String) (v : Nat) (js' : JState 64)
    (hd : O d = false → js'.get (ρ d) = BitVec.ofNat 64 v)
    (ho : ∀ u, u ≠ d → js'.get (ρ u) = js.get (ρ u)) :
    SMatchT O ρ (LowCTMachine.setS σ d v) js' := by
  intro u hu
  by_cases hud : u = d
  · subst hud; rw [hd hu]; simp [LowCTMachine.setS]
  · rw [ho u hud, hm u hu]; simp [LowCTMachine.setS, hud]

/-- From a full match with the filled state updated at `d`, the partial match with
    `σ` updated at `d`, when the two values agree for `d` outside `O`. -/
theorem SMatchT.of_fill_setS {O : String → Bool} {ρ : RegMap} {σ : Env} {js js' : JState 64}
    (d : String) (v v' : Nat)
    (hden : SMatch ρ (LowCTMachine.setS (fillEnv O ρ σ js) d v') js')
    (hv : O d = false → v' = v) : SMatchT O ρ (LowCTMachine.setS σ d v) js' := by
  intro u hu
  rw [hden u]
  by_cases hud : u = d
  · subst hud; simp [LowCTMachine.setS, hv hu]
  · simp [LowCTMachine.setS, hud, fillEnv_of_false hu]

theorem toNat_of_matchT {O : String → Bool} {ρ : RegMap} {σ : Env} {js : JState 64}
    (hm : SMatchT O ρ σ js) (v : String) (hO : O v = false) (hv : σ v < 2 ^ 64) :
    (js.get (ρ v)).toNat = σ v := by
  rw [hm v hO, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

theorem ofNat_eq_zero_iff_of_lt (v : Nat) (hv : v < 2 ^ 64) :
    BitVec.ofNat 64 v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt hv] at this
  · rintro rfl; rfl

theorem toNat_of_match (ρ : RegMap) (σ : Env) (js : JState 64) (hm : SMatch ρ σ js) (v : String)
    (hv : σ v < 2 ^ 64) : (js.get (ρ v)).toNat = σ v := by
  rw [hm v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

theorem SMatch.setS (ρ : RegMap) (σ : Env) (js : JState 64)
    (hm : SMatch ρ σ js) (d : String) (v : Nat) (js' : JState 64)
    (hd : js'.get (ρ d) = BitVec.ofNat 64 v) (ho : ∀ u, u ≠ d → js'.get (ρ u) = js.get (ρ u)) :
    SMatch ρ (LowCTMachine.setS σ d v) js' := by
  intro u
  by_cases hu : u = d
  · subst hu; rw [hd]; simp [LowCTMachine.setS]
  · rw [ho u hu, hm u]; simp [LowCTMachine.setS, hu]

theorem WExpr.depth_pos : ∀ e : WExpr, 0 < e.depth
  | .var _ | .lit _ => Nat.one_pos
  | .bin _ _ b => by simp only [WExpr.depth]; omega

/-- The value of the lowering of a word expression: with distinct temporaries
    outside the image of `ρ`, at least the depth of the expression in number, the
    first temporary holds the truncated source value. -/
theorem lowerW_val (ρ : RegMap) (σ : Env) :
    ∀ (e : WExpr) (ts : List String) (s : JState 64) (x : String), SMatch ρ σ s →
      (∀ v, ∀ t ∈ ts, ρ v ≠ t) → ts.Nodup → e.depth ≤ ts.length →
      (runBlock s (lowerW ρ ts e)).get (ts.headD x) = BitVec.ofNat 64 (e.toSExpr.eval σ)
  | e, [], _, _, _, _, _, hd => absurd hd (by have := e.depth_pos; simp; omega)
  | .var v, t :: _, s, _, hm, _, _, _ => by
    simp only [lowerW, runBlock_cons, runBlock_nil, List.headD_cons]
    rw [evalInstr_mov_reg, JState.get_setReg_same, hm v]
    rfl
  | .lit n, t :: _, s, _, _, _, _, _ => by
    simp only [lowerW, runBlock_cons, runBlock_nil, List.headD_cons]
    rw [evalInstr_movImm, JState.get_setReg_same]
    rfl
  | .bin op a b, t :: ts, s, _, hm, hρt, hnd, hd => by
    simp only [WExpr.depth, List.length_cons] at hd
    have hda : a.depth ≤ (t :: ts).length := by simp; omega
    have hdb : b.depth ≤ ts.length := by omega
    have hnd' := List.nodup_cons.mp hnd
    have hρts : ∀ v, ∀ u ∈ ts, ρ v ≠ u := fun v u hu => hρt v u (List.mem_cons_of_mem _ hu)
    set s₁ := runBlock s (lowerW ρ (t :: ts) a) with hs₁
    have ha : s₁.get t = BitVec.ofNat 64 (a.toSExpr.eval σ) :=
      lowerW_val ρ σ a (t :: ts) s t hm hρt hnd hda
    have hm₁ : SMatch ρ σ s₁ := by
      intro v
      rw [hs₁, lowerW_get_other ρ a (t :: ts) s (ρ v) (fun h => hρt v _ h rfl), hm v]
    have hb : (runBlock s₁ (lowerW ρ ts b)).get (ts.headD t) =
        BitVec.ofNat 64 (b.toSExpr.eval σ) :=
      lowerW_val ρ σ b ts s₁ t hm₁ hρts hnd'.2 hdb
    have ht : (runBlock s₁ (lowerW ρ ts b)).get t = s₁.get t :=
      lowerW_get_other ρ b ts s₁ t hnd'.1
    simp only [lowerW, List.headD_cons]
    rw [runBlock_append, runBlock_append, runBlock_cons, runBlock_nil, ← hs₁,
      ArithOp.toJInstr_word, ht, hb, ha]
    cases op <;>
      simp [WExpr.toSExpr, arithNode, SExpr.eval, BitVec.ofNat_add, BitVec.ofNat_and,
        BitVec.ofNat_xor, BitVec.ofNat_mul]

/-- The iterations of a loop: from matching states with the counter at `i`, the
    machine iterations of the lowered body track the source iterations. -/
theorem loop_sim (ρ τ : RegMap) (hρ : Function.Injective ρ) (O : String → Bool)
    (x ctr : String) (body : CFSrc)
    (hctrρ : ∀ v, ρ v ≠ ctr)
    (ih : ∀ σ js, SMatchT O ρ σ js → InRange body σ →
      SMatchT O ρ (srcDen body σ) (mcfExec js (lowerCF ρ τ body)) ∧
        mcfLeak .doitm js (lowerCF ρ τ body) = mTrace τ body σ)
    (hpres : ∀ s, (mcfExec s (lowerCF ρ τ body)).get ctr = s.get ctr) :
    ∀ (k i : Nat) (σ : Env) (js : JState 64), SMatchT O ρ σ js →
      js.get ctr = BitVec.ofNat 64 i →
      iterAll x (srcDen body) (InRange body) k i σ →
      SMatchT O ρ (iterDen x (srcDen body) k i σ)
          ((fun s => mcfExec s (loopBody ρ x ctr (lowerCF ρ τ body)))^[k] js) ∧
        iterLeak (fun s => mcfLeak .doitm s (loopBody ρ x ctr (lowerCF ρ τ body)))
            (fun s => mcfExec s (loopBody ρ x ctr (lowerCF ρ τ body))) k js =
          iterTrace x (srcDen body) (mTrace τ body) k i σ := by
  set B := loopBody ρ x ctr (lowerCF ρ τ body) with hB
  have hstep : ∀ (i : Nat) σ js, SMatchT O ρ σ js → js.get ctr = BitVec.ofNat 64 i →
      InRange body (setS σ x i) →
      SMatchT O ρ (srcDen body (setS σ x i)) (mcfExec js B) ∧
        (mcfExec js B).get ctr = BitVec.ofNat 64 (i + 1) ∧
        mcfLeak .doitm js B = mTrace τ body (setS σ x i) := by
    intro i σ js hm hc hinb
    have hm1 : SMatchT O ρ (setS σ x i) (evalInstr js (.mov (ρ x) (.reg ctr))) := by
      refine hm.setS x i _ (fun _ => ?_) ?_
      · rw [evalInstr_mov_reg, JState.get_setReg_same, hc]
      · intro u hu
        rw [evalInstr_mov_reg, JState.get_setReg_other _ _ _ _ (fun h => hu (hρ h))]
    have hc1 : (evalInstr js (.mov (ρ x) (.reg ctr))).get ctr = BitVec.ofNat 64 i := by
      rw [evalInstr_mov_reg, JState.get_setReg_other _ _ _ _ (fun h => hctrρ x h.symm), hc]
    obtain ⟨hmb, hlb⟩ := ih _ _ hm1 hinb
    refine ⟨?_, ?_, ?_⟩
    · rw [hB]
      simp only [loopBody, mcfExec, runBlock_cons, runBlock_nil]
      intro v hv
      rw [evalInstr_add_imm_get, ite_eq_right (hctrρ v)]
      exact hmb v hv
    · rw [hB]
      simp only [loopBody, mcfExec, runBlock_cons, runBlock_nil]
      rw [evalInstr_add_imm_get, ite_eq_left rfl, hpres, hc1]
      simp [BitVec.ofNat_add]
    · rw [hB]
      simp only [loopBody, mcfLeak, mcfExec, runBlock_cons, runBlock_nil]
      rw [hlb]
      simp [blockLeakCT, instrLeakCT, instrLeak, JInstr.mnem, DoitRegime.leaksOperands,
        X86Mnem.timing]
  intro k
  induction k with
  | zero => intro i σ js hm _ _; exact ⟨hm, rfl⟩
  | succ k ihk =>
    intro i σ js hm hc hall
    obtain ⟨hm', hc', hl'⟩ := hstep i σ js hm hc hall.1
    obtain ⟨hmk, hlk⟩ := ihk (i + 1) _ _ hm' hc' hall.2
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply, iterDen]; exact hmk
    · rw [iterLeak, iterTrace, hl', hlk]

/-- The iterations of a guarded loop: from matching states, the machine iterations
    of the lowered body track the source iterations, the machine guard is zero
    exactly where the source guard is, and the traces agree. -/
theorem while_sim (ρ τ : RegMap) (O : String → Bool) (g : String) (hg : O g = false)
    (body : CFSrc)
    (ih : ∀ σ js, SMatchT O ρ σ js → InRange body σ →
      SMatchT O ρ (srcDen body σ) (mcfExec js (lowerCF ρ τ body)) ∧
        mcfLeak .doitm js (lowerCF ρ τ body) = mTrace τ body σ) :
    ∀ (k : Nat) (σ : Env) (js : JState 64), SMatchT O ρ σ js →
      ((srcDen body)^[k] σ) g = 0 →
      (∀ j < k, ((srcDen body)^[j] σ) g ≠ 0 ∧ ((srcDen body)^[j] σ) g < 2 ^ 64 ∧
        InRange body ((srcDen body)^[j] σ)) →
      SMatchT O ρ ((srcDen body)^[k] σ) ((fun s => mcfExec s (lowerCF ρ τ body))^[k] js) ∧
      ((fun s => mcfExec s (lowerCF ρ τ body))^[k] js).get (ρ g) = 0 ∧
      (∀ j < k, ¬ ((fun s => mcfExec s (lowerCF ρ τ body))^[j] js).get (ρ g) = 0) ∧
      whileLeak (fun s => mcfExec s (lowerCF ρ τ body)) (fun s => mcfLeak .doitm s (lowerCF ρ τ body))
          k js = whileLeak (srcDen body) (mTrace τ body) k σ := by
  intro k
  induction k with
  | zero =>
    intro σ js hm h0 _
    refine ⟨hm, ?_, fun j hj => absurd hj (Nat.not_lt_zero _), rfl⟩
    simp only [Function.iterate_zero, id] at h0 ⊢
    rw [hm g hg, h0]; rfl
  | succ k ihk =>
    intro σ js hm h0 hall
    obtain ⟨hne, hlt, hinb⟩ := hall 0 (Nat.succ_pos k)
    simp only [Function.iterate_zero, id] at hne hlt hinb
    obtain ⟨hm1, hl1⟩ := ih σ js hm hinb
    have h0' : ((srcDen body)^[k] (srcDen body σ)) g = 0 := by
      rwa [Function.iterate_succ_apply] at h0
    have hall' : ∀ j < k, ((srcDen body)^[j] (srcDen body σ)) g ≠ 0 ∧
        ((srcDen body)^[j] (srcDen body σ)) g < 2 ^ 64 ∧
        InRange body ((srcDen body)^[j] (srcDen body σ)) := by
      intro j hj
      have := hall (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    obtain ⟨hmk, hzk, hnk, hlk⟩ := ihk _ _ hm1 h0' hall'
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Function.iterate_succ_apply, Function.iterate_succ_apply]; exact hmk
    · rw [Function.iterate_succ_apply]; exact hzk
    · intro j hj
      cases j with
      | zero =>
        simp only [Function.iterate_zero, id]
        rw [hm g hg]
        exact fun h => hne ((ofNat_eq_zero_iff_of_lt _ hlt).1 h)
      | succ j => rw [Function.iterate_succ_apply]; exact hnk j (by omega)
    · rw [whileLeak, whileLeak, hl1, hlk]

/-- The simulation: from states related by `SMatchT O ρ`, the machine post-state of
    the lowering is related to the source post-state, and the machine trace is
    `mTrace τ c σ`. -/
theorem lowerCF_sim (ρ τ : RegMap) (hρ : Function.Injective ρ) (O : String → Bool) :
    ∀ (c : CFSrc), c.RegWF ρ τ → c.taint O = true → ∀ σ js, SMatchT O ρ σ js → InRange c σ →
      SMatchT O ρ (srcDen c σ) (mcfExec js (lowerCF ρ τ c)) ∧
        mcfLeak .doitm js (lowerCF ρ τ c) = mTrace τ c σ
  | .skip, _, _, σ, js, hm, _ => ⟨hm, rfl⟩
  | .arith p, hwf, ht, σ, js, hm, _ => by
    refine ⟨?_, ?_⟩
    · refine SMatchT.of_fill_setS p.dst _ _
        (lowerArith_denote ρ p { rsTower := fun _ => none, rsScalar := fillEnv O ρ σ js } js hρ
          hwf hm.fill) fun hd => ?_
      simp only [CFSrc.taint, hd, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at ht
      exact ArithSrc.eval_congr p _ _ (fillEnv_of_false ht.1) (fillEnv_of_false ht.2)
    · rw [lowerCF, mcfLeak, blockLeakCT_lowerArith]; rfl
  | .setLit d n, _, _, σ, js, hm, _ => by
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]
      refine hm.setS d _ _ (fun _ => ?_) ?_
      · rw [evalInstr_movImm, JState.get_setReg_same]
      · intro u hu
        rw [evalInstr_movImm, JState.get_setReg_other _ _ _ _ (fun h => hu (hρ h))]
    · rfl
  | .expr d e ts, hwf, ht, σ, js, hm, _ => by
    obtain ⟨hρt, hnd, hdep⟩ := hwf
    have hmf := hm.fill
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, srcDen]
      rw [runBlock_append, runBlock_cons, runBlock_nil]
      refine SMatchT.of_fill_setS (js := js) d _ (e.toSExpr.eval (fillEnv O ρ σ js)) ?_
        fun hd => ?_
      · refine SMatch.setS ρ _ js hmf d _ _ ?_ ?_
        · rw [evalInstr_mov_reg, JState.get_setReg_same]
          exact lowerW_val ρ _ e ts js (ρ d) hmf hρt hnd hdep
        · intro u hu
          rw [evalInstr_mov_reg, JState.get_setReg_other _ _ _ _ (fun h => hu (hρ h)),
            lowerW_get_other ρ e ts js (ρ u) (fun h => hρt u _ h rfl)]
      · simp only [CFSrc.taint, hd, Bool.false_or] at ht
        exact WExpr.eval_congrT (fun v hv => fillEnv_of_false hv) e ht
    · simp only [lowerCF, mcfLeak]
      rw [blockLeakCT_append, blockLeakCT_lowerW]
      rfl
  | .letU64 x body, hwf, ht, σ, js, hm, hin => by
    have hm0 : SMatchT O ρ (setS σ x 0) (evalInstr js (movImm (ρ x) 0)) := by
      refine hm.setS x 0 _ (fun _ => ?_) ?_
      · rw [evalInstr_movImm, JState.get_setReg_same]
      · intro u hu
        rw [evalInstr_movImm, JState.get_setReg_other _ _ _ _ (fun h => hu (hρ h))]
    obtain ⟨hmb, hlb⟩ := lowerCF_sim ρ τ hρ O body hwf ht _ _ hm0 hin
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]; exact hmb
    · simp only [lowerCF, mcfLeak, mcfExec, runBlock_cons, runBlock_nil, mTrace]
      rw [hlb]
      rfl
  | .shift k d a c, _, ht, σ, js, hm, hin => by
    simp only [CFSrc.taint, Bool.and_eq_true, Bool.not_eq_true'] at ht
    obtain ⟨ha, hc⟩ := hin
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]
      refine hm.setS d _ _ (fun _ => ?_) ?_
      · rw [evalInstr_shift, JState.get_setReg_same, hm a ht.1, hm c ht.2,
          ShiftKind.x86_ofNat k _ _ ha hc]
      · intro u hu
        rw [evalInstr_shift, JState.get_setReg_other _ _ _ _ (fun h => hu (hρ h))]
    · rw [lowerCF, mcfLeak, blockLeakCT_shift, toNat_of_matchT hm a ht.1 ha,
        toNat_of_matchT hm c ht.2 (by omega), mTrace]
  | .mulHi d a b lo, hwf, ht, σ, js, hm, _ => by
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]
      refine hm.setS d _ _ (fun hd => ?_) ?_
      · simp only [CFSrc.taint, hd, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at ht
        rw [evalInstr_mulx_get, ite_eq_left rfl]
        simp only [JOperand.eval]
        rw [hm a ht.1, hm b ht.2, x86_MULX_hi_ofNat]
      · intro u hu
        rw [evalInstr_mulx_get, ite_eq_right (fun h => hu (hρ h)), ite_eq_right (hwf u)]
    · rw [lowerCF, mcfLeak, blockLeakCT_mulx]; rfl
  | .select dst sel s0 s1, hwf, _, σ, js, hm, _ => by
    refine ⟨hm.of_regs fun v => ?_, ?_⟩
    · simp only [lowerCF, mcfExec]
      exact lowerSelect_get ρ τ dst sel s0 s1 js _ (hwf v)
    · rw [lowerCF, mcfLeak, blockLeakCT_lowerSelect]; rfl
  | .arrLoad dst src idx, hwf, ht, σ, js, hm, hin => by
    simp only [CFSrc.taint, Bool.not_eq_true'] at ht
    refine ⟨hm.of_regs fun v => ?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, evalInstr]
      exact JState.get_setReg_other _ _ _ _ (hwf v)
    · simp only [lowerCF, mcfLeak, blockLeakCT_cons, blockLeakCT_nil, instrLeakCT, instrLeak,
        mTrace, toNat_of_matchT hm idx ht hin]
      simp [JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing, mleakToCT]
  | .arrStore arr idx src, _, ht, σ, js, hm, hin => by
    simp only [CFSrc.taint, Bool.not_eq_true'] at ht
    refine ⟨hm.of_regs fun v => ?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil]
      simp only [evalInstr, JState.storeIdx, JState.store]
      rfl
    · simp only [lowerCF, mcfLeak, blockLeakCT_cons, blockLeakCT_nil, instrLeakCT, instrLeak,
        mTrace, toNat_of_matchT hm idx ht hin]
      simp [JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing, mleakToCT]
  | .seq a b, hwf, ht, σ, js, hm, hin => by
    simp only [CFSrc.taint, Bool.and_eq_true] at ht
    obtain ⟨hma, hla⟩ := lowerCF_sim ρ τ hρ O a hwf.1 ht.1 σ js hm hin.1
    obtain ⟨hmb, hlb⟩ := lowerCF_sim ρ τ hρ O b hwf.2 ht.2 _ _ hma hin.2
    refine ⟨hmb, ?_⟩
    rw [lowerCF, mcfLeak, hla, hlb, mTrace]
  | .ifNz g t e, hwf, ht, σ, js, hm, hin => by
    simp only [CFSrc.taint, Bool.and_eq_true, Bool.not_eq_true'] at ht
    obtain ⟨hlt, hin'⟩ := hin
    have hg : js.get (ρ g) = 0 ↔ σ g = 0 := by
      rw [hm g ht.1.1]; exact ofNat_eq_zero_iff_of_lt _ hlt
    by_cases hz : σ g = 0
    · have hjz : js.get (ρ g) = 0 := hg.2 hz
      rw [ite_eq_left hz] at hin'
      obtain ⟨hme, hle⟩ := lowerCF_sim ρ τ hρ O e hwf.2 ht.2 σ js hm hin'
      refine ⟨?_, ?_⟩
      · rw [lowerCF, mcfExec, ite_eq_left hjz, srcDen, ite_eq_left hz]; exact hme
      · rw [lowerCF, mcfLeak, ite_eq_left hjz, mTrace, ite_eq_left hz, hle]
    · have hjz : ¬ js.get (ρ g) = 0 := fun h => hz (hg.1 h)
      rw [ite_eq_right hz] at hin'
      obtain ⟨hmt, hlt'⟩ := lowerCF_sim ρ τ hρ O t hwf.1 ht.1.2 σ js hm hin'
      refine ⟨?_, ?_⟩
      · rw [lowerCF, mcfExec, ite_eq_right hjz, srcDen, ite_eq_right hz]; exact hmt
      · rw [lowerCF, mcfLeak, ite_eq_right hjz, mTrace, ite_eq_right hz, hlt']
  | .forLit x ctr n body, hwf, ht, σ, js, hm, hin => by
    obtain ⟨hctrρ, hctrb, hwfb⟩ := hwf
    have hloop := loop_sim ρ τ hρ O x ctr body hctrρ (lowerCF_sim ρ τ hρ O body hwfb ht)
      (lowerCF_preserves ρ τ ctr hctrρ body hctrb)
    have hm0 : SMatchT O ρ σ (evalInstr js (movImm ctr 0)) :=
      hm.of_regs fun v => by rw [evalInstr_movImm, JState.get_setReg_other _ _ _ _ (hctrρ v)]
    have hc0 : (evalInstr js (movImm ctr 0)).get ctr = BitVec.ofNat 64 0 := by
      rw [evalInstr_movImm, JState.get_setReg_same]
    obtain ⟨hmL, hlL⟩ := hloop n 0 σ _ hm0 hc0 hin
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]; exact hmL
    · simp only [lowerCF, mcfLeak, mcfExec, runBlock_cons, runBlock_nil, mTrace]
      rw [hlL]
      simp [blockLeakCT, instrLeakCT, instrLeak, movImm, JInstr.mnem, DoitRegime.leaksOperands,
        X86Mnem.timing]
  | .forRt x ctr bnd body, hwf, ht, σ, js, hm, hin => by
    simp only [CFSrc.taint, Bool.and_eq_true, Bool.not_eq_true'] at ht
    obtain ⟨hctrρ, hctrb, hwfb⟩ := hwf
    obtain ⟨hbnd, hall⟩ := hin
    have hloop := loop_sim ρ τ hρ O x ctr body hctrρ (lowerCF_sim ρ τ hρ O body hwfb ht.2)
      (lowerCF_preserves ρ τ ctr hctrρ body hctrb)
    have hm0 : SMatchT O ρ σ (evalInstr js (movImm ctr 0)) :=
      hm.of_regs fun v => by rw [evalInstr_movImm, JState.get_setReg_other _ _ _ _ (hctrρ v)]
    have hc0 : (evalInstr js (movImm ctr 0)).get ctr = BitVec.ofNat 64 0 := by
      rw [evalInstr_movImm, JState.get_setReg_same]
    have hn : ((evalInstr js (movImm ctr 0)).get (ρ bnd)).toNat = σ bnd :=
      toNat_of_matchT hm0 bnd ht.1 hbnd
    obtain ⟨hmL, hlL⟩ := hloop (σ bnd) 0 σ _ hm0 hc0 hall
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]
      rw [hn]; exact hmL
    · simp only [lowerCF, mcfLeak, mcfExec, runBlock_cons, runBlock_nil, mTrace]
      rw [hn, hlL]
      simp [blockLeakCT, instrLeakCT, instrLeak, movImm, JInstr.mnem, DoitRegime.leaksOperands,
        X86Mnem.timing]
  | .ltSet d a b, _, ht, σ, js, hm, hin => by
    simp only [CFSrc.taint, Bool.and_eq_true, Bool.not_eq_true'] at ht
    obtain ⟨ha, hb⟩ := hin
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]
      refine hm.setS d _ _ (fun _ => ?_) fun u hu => cmp_setc_get_other js _ _ _ _
        (fun h => hu (hρ h))
      rw [cmp_setc_get, toNat_of_matchT hm a ht.1 ha, toNat_of_matchT hm b ht.2 hb]
      split <;> rfl
    · simp only [lowerCF, mcfLeak, mTrace]
      exact blockLeakCT_cmp_setc js _ _ _
  | .whileNz g body, hwf, ht, σ, js, hm, hin => by
    simp only [CFSrc.taint, Bool.and_eq_true, Bool.not_eq_true'] at ht
    obtain ⟨k, hk0, hall⟩ := hin
    obtain ⟨hmk, hzk, hnk, hlk⟩ := while_sim ρ τ O g ht.1 body
      (lowerCF_sim ρ τ hρ O body hwf ht.2) k σ js hm hk0 hall
    have hcs := whileCount_eq (srcDen body) (fun σ' => σ' g = 0) σ k hk0
      (fun j hj => (hall j hj).1)
    have hcm := whileCount_eq (fun s => mcfExec s (lowerCF ρ τ body)) (fun s => s.get (ρ g) = 0)
      js k hzk hnk
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, srcDen, hcs, hcm]; exact hmk
    · simp only [lowerCF, mcfLeak, mTrace, hcs, hcm]; exact hlk
  | .call _ _ _ code, hwf, _, σ, js, hm, _ => by
    refine ⟨hm.of_regs fun v => code.get_other js _ fun h => hwf v _ h rfl, ?_⟩
    simp only [lowerCF, mcfLeak, mTrace]
    exact code.leak_eq js
  | .copy dst src tmp, hwf, _, σ, js, hm, _ => by
    refine ⟨hm.of_regs fun v => copyBlk_get_other _ _ _ _ (hwf v) _ js, ?_⟩
    simp only [lowerCF, mcfLeak, mTrace]
    exact blockLeakCT_copyBlk _ _ _ _ js
  | .letT _ _ body, hwf, ht, σ, js, hm, hin => lowerCF_sim ρ τ hρ O body hwf ht σ js hm hin
  | .limbSet loc idx e ts, hwf, _, σ, js, hm, _ => by
    refine ⟨hm.of_regs fun v => ?_, ?_⟩
    · simp only [lowerCF, mcfExec]
      rw [runBlock_append, runBlock_cons, runBlock_nil]
      simp only [evalInstr, JState.store]
      exact lowerW_get_other ρ e ts js (ρ v) (fun h => hwf v _ h rfl)
    · simp only [lowerCF, mcfLeak, mTrace]
      rw [blockLeakCT_append, blockLeakCT_lowerW]
      simp [instrLeakCT, instrLeak, mleakToCT, JInstr.mnem, DoitRegime.leaksOperands,
        X86Mnem.timing]
  | .limbGet d v idx, _, ht, σ, js, hm, _ => by
    simp only [CFSrc.taint] at ht
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]
      refine hm.setS d _ _ (fun hd => absurd (ht ▸ hd) (by simp)) fun u hu => ?_
      simp only [evalInstr]
      exact JState.get_setReg_other _ _ _ _ (fun h => hu (hρ h))
    · simp [lowerCF, mcfLeak, mTrace, instrLeakCT, instrLeak, mleakToCT, JInstr.mnem,
        DoitRegime.leaksOperands, X86Mnem.timing]

/-- The machine trace: from states related by `SMatch ρ`, the machine trace of the
    lowering is `mTrace τ c σ`. -/
theorem lowerCF_leak (ρ τ : RegMap) (hρ : Function.Injective ρ) (c : CFSrc) (hwf : c.WF ρ τ)
    (σ : Env) (js : JState 64) (hm : SMatch ρ σ js) (hin : InRange c σ) :
    mcfLeak .doitm js (lowerCF ρ τ c) = mTrace τ c σ := by
  obtain ⟨hr, O, hO⟩ := hwf
  exact (lowerCF_sim ρ τ hρ O c hr hO σ js (hm.toT O) hin).2

/-! ### 4.5 The source trace determines the machine trace -/

theorem iterTrace_prefix (x : String) (f : Env → Env) (ls lm : Env → List CTLeak)
    (hb : ∀ σ₁ σ₂ l₁ l₂, ls σ₁ ++ l₁ = ls σ₂ ++ l₂ → ls σ₁ = ls σ₂ ∧ lm σ₁ = lm σ₂) :
    ∀ (n i : Nat) (σ₁ σ₂ : Env) (l₁ l₂ : List CTLeak),
      iterTrace x f ls n i σ₁ ++ l₁ = iterTrace x f ls n i σ₂ ++ l₂ →
      iterTrace x f ls n i σ₁ = iterTrace x f ls n i σ₂ ∧
        iterTrace x f lm n i σ₁ = iterTrace x f lm n i σ₂ := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro i σ₁ σ₂ l₁ l₂ h
    simp only [iterTrace, List.append_assoc] at h ⊢
    obtain ⟨e1, m1⟩ := hb _ _ _ _ h
    rw [e1, List.append_cancel_left_eq] at h
    obtain ⟨e2, m2⟩ := ih _ _ _ _ _ h
    exact ⟨by rw [e1, e2], by rw [m1, m2]⟩

theorem whileLeak_prefix {α : Type} (f : α → α) (ls lm : α → List CTLeak)
    (hb : ∀ a₁ a₂ l₁ l₂, ls a₁ ++ l₁ = ls a₂ ++ l₂ → ls a₁ = ls a₂ ∧ lm a₁ = lm a₂) :
    ∀ (k₁ k₂ : Nat) (a₁ a₂ : α) (l₁ l₂ : List CTLeak),
      whileLeak f ls k₁ a₁ ++ l₁ = whileLeak f ls k₂ a₂ ++ l₂ →
      whileLeak f ls k₁ a₁ = whileLeak f ls k₂ a₂ ∧
        whileLeak f lm k₁ a₁ = whileLeak f lm k₂ a₂ := by
  intro k₁
  induction k₁ with
  | zero =>
    intro k₂ a₁ a₂ l₁ l₂ h
    cases k₂ with
    | zero => exact ⟨rfl, rfl⟩
    | succ k₂ => simp [whileLeak] at h
  | succ k ih =>
    intro k₂ a₁ a₂ l₁ l₂ h
    cases k₂ with
    | zero => simp [whileLeak] at h
    | succ k₂ =>
      simp only [whileLeak, List.cons_append, List.cons.injEq, true_and,
        List.append_assoc] at h ⊢
      obtain ⟨e1, m1⟩ := hb _ _ _ _ h
      rw [e1, List.append_cancel_left_eq] at h
      obtain ⟨e2, m2⟩ := ih _ _ _ _ _ h
      exact ⟨by rw [e1, e2], by rw [m1, m2]⟩

/-- The source trace determines the machine trace: two source traces of `c` of
    which one extended is the other extended are equal, and so are the machine
    traces. -/
theorem srcLeak_prefix (τ : RegMap) :
    ∀ (c : CFSrc) (σ₁ σ₂ : Env) (l₁ l₂ : List CTLeak),
      srcLeak c σ₁ ++ l₁ = srcLeak c σ₂ ++ l₂ →
      srcLeak c σ₁ = srcLeak c σ₂ ∧ mTrace τ c σ₁ = mTrace τ c σ₂
  | .skip, _, _, _, _, _ | .arith _, _, _, _, _, _ | .setLit .., _, _, _, _, _
  | .expr .., _, _, _, _, _ | .mulHi .., _, _, _, _, _ | .select .., _, _, _, _, _
  | .ltSet .., _, _, _, _, _ | .call .., _, _, _, _, _ | .copy .., _, _, _, _, _
  | .limbSet .., _, _, _, _, _ | .limbGet .., _, _, _, _, _ => ⟨rfl, rfl⟩
  | .letU64 x body, σ₁, σ₂, l₁, l₂, h => srcLeak_prefix τ body _ _ l₁ l₂ h
  | .letT _ _ body, σ₁, σ₂, l₁, l₂, h => srcLeak_prefix τ body _ _ l₁ l₂ h
  | .shift k _ a c, σ₁, σ₂, l₁, l₂, h => by
    cases k with
    | shr | shl => exact ⟨rfl, rfl⟩
    | sar =>
      simp only [srcLeak, mTrace, ShiftKind.leak, List.cons_append, List.nil_append,
        List.cons.injEq] at h ⊢
      refine ⟨?_, ?_⟩ <;> simp [h.1]
  | .arrLoad _ src idx, σ₁, σ₂, l₁, l₂, h | .arrStore src idx _, σ₁, σ₂, l₁, l₂, h => by
    simp only [srcLeak, mTrace, List.cons_append, List.nil_append, List.cons.injEq,
      CTLeak.addr.injEq, true_and] at h ⊢
    refine ⟨?_, ?_⟩ <;> simp [h.1]
  | .seq a b, σ₁, σ₂, l₁, l₂, h => by
    simp only [srcLeak, mTrace, List.append_assoc] at h ⊢
    obtain ⟨e1, m1⟩ := srcLeak_prefix τ a _ _ _ _ h
    rw [e1, List.append_cancel_left_eq] at h
    obtain ⟨e2, m2⟩ := srcLeak_prefix τ b _ _ _ _ h
    exact ⟨by rw [e1, e2], by rw [m1, m2]⟩
  | .ifNz g t e, σ₁, σ₂, l₁, l₂, h => by
    simp only [srcLeak, mTrace] at h ⊢
    by_cases h₁ : σ₁ g = 0 <;> by_cases h₂ : σ₂ g = 0 <;>
      simp only [h₁, h₂, ite_true, ite_false, List.cons_append, List.cons.injEq,
        CTLeak.branch.injEq, reduceCtorEq, false_and, true_and] at h ⊢
    · exact srcLeak_prefix τ e _ _ _ _ h
    · exact srcLeak_prefix τ t _ _ _ _ h
  | .forLit x _ n body, σ₁, σ₂, l₁, l₂, h =>
    iterTrace_prefix x _ _ _ (srcLeak_prefix τ body) n 0 σ₁ σ₂ l₁ l₂ h
  | .forRt x _ bnd body, σ₁, σ₂, l₁, l₂, h => by
    simp only [srcLeak, mTrace, List.cons_append, List.cons.injEq, CTLeak.trip.injEq] at h ⊢
    obtain ⟨hb, h⟩ := h
    rw [hb] at h ⊢
    obtain ⟨e, m⟩ := iterTrace_prefix x _ _ _ (srcLeak_prefix τ body) _ 0 σ₁ σ₂ l₁ l₂ h
    exact ⟨⟨rfl, e⟩, ⟨rfl, m⟩⟩
  | .whileNz g body, σ₁, σ₂, l₁, l₂, h =>
    whileLeak_prefix _ _ _ (srcLeak_prefix τ body) _ _ σ₁ σ₂ l₁ l₂ h

/-- Machine traces of the lowering are equal for two runs of the source program
    with equal traces from states related by `StateMatch ρ` that satisfy the range
    conditions. -/
theorem lowerCF_leak_eq_of_runs (N : Nat) (leafSpec : LeafSpec) (ρ τ : RegMap)
    (hρ : Function.Injective ρ) (c : CFSrc) (hwf : c.WF ρ τ)
    (rs₁ rs₂ r₁ r₂ : RustState) (t₁ t₂ : List CTLeak) (js₁ js₂ : JState 64)
    (hm₁ : StateMatch ρ rs₁ js₁) (hm₂ : StateMatch ρ rs₂ js₂)
    (hin₁ : InRange c rs₁.rsScalar) (hin₂ : InRange c rs₂.rsScalar)
    (h₁ : RustExecLeak N leafSpec .owned c.toLowCT rs₁ t₁ r₁)
    (h₂ : RustExecLeak N leafSpec .owned c.toLowCT rs₂ t₂ r₂) (ht : t₁ = t₂) :
    mcfLeak .doitm js₁ (lowerCF ρ τ c) = mcfLeak .doitm js₂ (lowerCF ρ τ c) := by
  rw [lowerCF_leak ρ τ hρ c hwf _ js₁ hm₁ hin₁, lowerCF_leak ρ τ hρ c hwf _ js₂ hm₂ hin₂]
  obtain ⟨-, O, hO⟩ := hwf
  have e₁ := (srcRun_det N leafSpec O c hO rs₁ t₁ r₁ _ (fun _ _ => rfl) h₁).1
  have e₂ := (srcRun_det N leafSpec O c hO rs₂ t₂ r₂ _ (fun _ _ => rfl) h₂).1
  exact (srcLeak_prefix τ c _ _ [] [] (by rw [← e₁, ← e₂, ht])).2

/-! ## 5. Constant time -/

/-- The scalar environment read off a machine state through `ρ`. -/
def liftEnv (ρ : RegMap) (js : JState 64) : Env := fun v => (js.get (ρ v)).toNat

/-- The source state read off a machine state through `ρ`, with tower heap `T`. -/
def liftState (ρ : RegMap) (T : String → Option (Σ t : TowerType, RustVal t))
    (js : JState 64) : RustState :=
  { rsTower := T, rsScalar := liftEnv ρ js }

theorem liftEnv_match (ρ : RegMap) (js : JState 64) : SMatch ρ (liftEnv ρ js) js := by
  intro v
  simp [liftEnv]

theorem liftState_pubEq (ρ : RegMap) (T : String → Option (Σ t : TowerType, RustVal t))
    (lt : LevelTable) (pub : PubPred)
    (hpub : ∀ x, lt x = .Public → pub (ρ x) = true) (js₁ js₂ : JState 64)
    (hag : agreePub pub js₁ js₂) : PubEqRS lt (liftState ρ T js₁) (liftState ρ T js₂) := by
  intro x hx
  refine ⟨?_, rfl⟩
  simp only [liftState, liftEnv]
  rw [hag (ρ x) (hpub x hx)]

/-- The machine states the lowering is run from: the source image under `ρ` and
    the tower heap `T` has a run of `c.toLowCT`, and the range conditions hold. -/
def Admissible (N : Nat) (leafSpec : LeafSpec) (ρ : RegMap)
    (T : String → Option (Σ t : TowerType, RustVal t)) (c : CFSrc) (js : JState 64) : Prop :=
  InRange c (liftEnv ρ js) ∧
    ∃ t rs', RustExecLeak N leafSpec .owned c.toLowCT (liftState ρ T js) t rs'

/-- Constant time from `LowCT` to owned machine code. If the source program is
    constant time for the split `lt` in the owned leakage model, its lowering is
    constant time in the machine model under DOITM, for machine states agreeing on
    the public registers `pub` (which contain the image of every public slot)
    that are admissible: their source images have a run and satisfy `InRange`. -/
theorem lowct_to_machine_ct (N : Nat) (leafSpec : LeafSpec) (lt : LevelTable)
    (pub : PubPred) (ρ τ : RegMap) (T : String → Option (Σ t : TowerType, RustVal t))
    (hρ : Function.Injective ρ) (c : CFSrc) (hwf : c.WF ρ τ)
    (hpub : ∀ x, lt x = .Public → pub (ρ x) = true)
    (hsrc : LowCTConstantTime N leafSpec .owned lt c.toLowCT) :
    ConstantTime
      (fun js₁ js₂ : JState 64 => agreePub pub js₁ js₂ ∧
        Admissible N leafSpec ρ T c js₁ ∧ Admissible N leafSpec ρ T c js₂)
      (fun js => mcfLeak .doitm js (lowerCF ρ τ c)) := by
  rintro js₁ js₂ ⟨hag, ⟨h₁, t₁, r₁, run₁⟩, ⟨h₂, t₂, r₂, run₂⟩⟩
  exact lowerCF_leak_eq_of_runs N leafSpec ρ τ hρ c hwf (liftState ρ T js₁) (liftState ρ T js₂)
    r₁ r₂ t₁ t₂ js₁ js₂
    (liftEnv_match ρ js₁) (liftEnv_match ρ js₂) h₁ h₂ run₁ run₂
    (hsrc _ _ _ _ (liftState_pubEq ρ T lt pub hpub js₁ js₂ hag) ⟨_, run₁⟩ ⟨_, run₂⟩)

/-- Constant time from `LowCT` to owned machine code for a program without select
    or array access: runs exist, and only the range conditions remain. -/
theorem lowct_to_machine_ct_towerFree (N : Nat) (leafSpec : LeafSpec) (lt : LevelTable)
    (pub : PubPred) (ρ τ : RegMap) (hρ : Function.Injective ρ) (c : CFSrc) (hwf : c.WF ρ τ)
    (htf : c.towerFree = true)
    (hpub : ∀ x, lt x = .Public → pub (ρ x) = true)
    (hsrc : LowCTConstantTime N leafSpec .owned lt c.toLowCT) :
    ConstantTime
      (fun js₁ js₂ : JState 64 => agreePub pub js₁ js₂ ∧
        InRange c (liftEnv ρ js₁) ∧ InRange c (liftEnv ρ js₂))
      (fun js => mcfLeak .doitm js (lowerCF ρ τ c)) := fun js₁ js₂ ⟨hag, h₁, h₂⟩ =>
  lowct_to_machine_ct N leafSpec lt pub ρ τ (fun _ => none) hρ c hwf hpub hsrc js₁ js₂
    ⟨hag, ⟨h₁, srcRun_exists N leafSpec c htf _⟩, ⟨h₂, srcRun_exists N leafSpec c htf _⟩⟩

/-- Constant time from `LowCT` to owned machine code for a program whose tower
    accesses are to names it binds (`towerOk`): runs exist from every state, and
    only the range conditions remain. -/
theorem lowct_to_machine_ct_towerOk (N : Nat) (leafSpec : LeafSpec) (lt : LevelTable)
    (pub : PubPred) (ρ τ : RegMap) (hρ : Function.Injective ρ) (c : CFSrc) (hwf : c.WF ρ τ)
    (hto : c.towerOk = true)
    (hpub : ∀ x, lt x = .Public → pub (ρ x) = true)
    (hsrc : LowCTConstantTime N leafSpec .owned lt c.toLowCT) :
    ConstantTime
      (fun js₁ js₂ : JState 64 => agreePub pub js₁ js₂ ∧
        InRange c (liftEnv ρ js₁) ∧ InRange c (liftEnv ρ js₂))
      (fun js => mcfLeak .doitm js (lowerCF ρ τ c)) := by
  intro js₁ js₂ ⟨hag, h₁, h₂⟩
  obtain ⟨Γ', hΓ⟩ := Option.isSome_iff_exists.mp hto
  have hrun : ∀ js, ∃ t rs', RustExecLeak N leafSpec .owned c.toLowCT
      (liftState ρ (fun _ => none) js) t rs' := fun js => by
    obtain ⟨t, rs', h, -⟩ := srcRun_exists_tower N leafSpec c [] Γ' hΓ _
      (fun x t hx => by simp [lookT] at hx)
    exact ⟨t, rs', h⟩
  exact lowct_to_machine_ct N leafSpec lt pub ρ τ (fun _ => none) hρ c hwf hpub hsrc js₁ js₂
    ⟨hag, ⟨h₁, hrun js₁⟩, ⟨h₂, hrun js₂⟩⟩

/-- Constant time from `LowCT` to owned machine code for straight-line arithmetic,
    wide multiplies and literal loops: no range condition. -/
theorem lowct_to_machine_ct_rangeFree (N : Nat) (leafSpec : LeafSpec) (lt : LevelTable)
    (pub : PubPred) (ρ τ : RegMap) (hρ : Function.Injective ρ) (c : CFSrc) (hwf : c.WF ρ τ)
    (hrf : c.rangeFree = true)
    (hpub : ∀ x, lt x = .Public → pub (ρ x) = true)
    (hsrc : LowCTConstantTime N leafSpec .owned lt c.toLowCT) :
    ConstantTime (fun js₁ js₂ : JState 64 => agreePub pub js₁ js₂)
      (fun js => mcfLeak .doitm js (lowerCF ρ τ c)) := fun js₁ js₂ hag =>
  lowct_to_machine_ct_towerFree N leafSpec lt pub ρ τ hρ c hwf (towerFree_of_rangeFree c hrf)
    hpub hsrc js₁ js₂ ⟨hag, inRange_of_rangeFree c hrf _, inRange_of_rangeFree c hrf _⟩

/-- **Source CT ⇒ machine CT for one arithmetic statement**, with source constant time in the `CTP-1` model as the premise and machine
    constant time in the `CTP-1` model as the conclusion. -/
theorem lowerArith_source_to_machine_CT (N : Nat) (leafSpec : LeafSpec) (lt : LevelTable)
    (pub : PubPred) (ρ : RegMap) (hρ : Function.Injective ρ) (p : ArithSrc) (hb : p.b ≠ p.dst)
    (hpub : ∀ x, lt x = .Public → pub (ρ x) = true)
    (hsrc : LowCTConstantTime N leafSpec .owned lt p.toLowCT) :
    MachineCT .doitm pub (lowerArith ρ p) := fun js₁ js₂ hag =>
  lowct_to_machine_ct_rangeFree N leafSpec lt pub ρ id hρ (.arith p) ⟨hb, fun _ => false, rfl⟩
    rfl hpub hsrc js₁ js₂ hag

/-! ## 6. Negative controls -/

/-- The lowering of a conditional on the secret scalar `k` is not constant time
    at the machine: two admissible states that differ only in `k` take different
    branches. -/
theorem secretGuard_lowered_not_ct (N : Nat) (leafSpec : LeafSpec) :
    ¬ ConstantTime
      (fun js₁ js₂ : JState 64 => agreePub (fun r => r != "k") js₁ js₂ ∧
        Admissible N leafSpec id (fun _ => none) (.ifNz "k" .skip .skip) js₁ ∧
        Admissible N leafSpec id (fun _ => none) (.ifNz "k" .skip .skip) js₂)
      (fun js => mcfLeak .doitm js (lowerCF id id (.ifNz "k" .skip .skip))) := by
  intro h
  have hadm : ∀ js : JState 64, Admissible N leafSpec id (fun _ => none)
      (.ifNz "k" .skip .skip) js := by
    intro js
    refine ⟨⟨(js.get "k").isLt, ?_⟩, srcRun_exists N leafSpec _ rfl _⟩
    split <;> trivial
  have := h zeroState kOneState ⟨zero_kOne_agree _ rfl, hadm _, hadm _⟩
  simp [lowerCF, mcfLeak, zeroState, kOneState, JState.get] at this

/-- The tower heap in which every variable holds a `u64` tower value. -/
def u64Heap : String → Option (Σ t : TowerType, RustVal t) := fun _ => some ⟨.TU64, default⟩

/-- The `u64` locations `d` (destination) and `tab` (table). -/
def locD : Located := ⟨"d", .TU64⟩
def locTab : Located := ⟨"tab", .TU64⟩

/-- A load from the table `tab` at the secret index `k` is not constant time at
    the machine: two admissible states differing only in `k` access `tab + 0` and
    `tab + 8`. -/
theorem secretIndex_lowered_not_ct (N : Nat) (leafSpec : LeafSpec) :
    ¬ ConstantTime
      (fun js₁ js₂ : JState 64 => agreePub (fun r => r != "k") js₁ js₂ ∧
        Admissible N leafSpec id u64Heap (.arrLoad locD locTab "k") js₁ ∧
        Admissible N leafSpec id u64Heap (.arrLoad locD locTab "k") js₂)
      (fun js => mcfLeak .doitm js (lowerCF id id (.arrLoad locD locTab "k"))) := by
  intro h
  have hlook : ∀ (js : JState 64) (l : Located), l.locDst = .TU64 →
      ∃ v, locatedLookup (liftState id u64Heap js) l = some v := by
    intro js l hl
    refine ⟨hl ▸ default, ?_⟩
    simp only [locatedLookup, liftState, u64Heap]
    rw [dite_eq_left hl.symm]
  have hadm : ∀ js : JState 64, Admissible N leafSpec id u64Heap (.arrLoad locD locTab "k") js := by
    intro js
    obtain ⟨vd, hd⟩ := hlook js locD rfl
    obtain ⟨vt, ht⟩ := hlook js locTab rfl
    exact ⟨(js.get "k").isLt, _, _, .arrLoad _ _ _ _ _ vd vt rfl hd ht⟩
  have := h zeroState kOneState ⟨zero_kOne_agree _ rfl, hadm _, hadm _⟩
  simp [lowerCF, mcfLeak, blockLeakCT, instrLeakCT, instrLeak, locTab, zeroState, kOneState,
    JState.get, mleakToCT] at this

/-- An arithmetic shift by the secret count `k` is not constant time at the
    machine: it is lowered to `SARX`, whose `vt` event carries the count. -/
theorem secretShift_lowered_not_ct (N : Nat) (leafSpec : LeafSpec) :
    ¬ ConstantTime
      (fun js₁ js₂ : JState 64 => agreePub (fun r => r != "k") js₁ js₂ ∧
        Admissible N leafSpec id (fun _ => none) (.shift .sar "y" "a" "k") js₁ ∧
        Admissible N leafSpec id (fun _ => none) (.shift .sar "y" "a" "k") js₂)
      (fun js => mcfLeak .doitm js (lowerCF id id (.shift .sar "y" "a" "k"))) := by
  intro h
  have h0 : Admissible N leafSpec id (fun _ => none) (.shift .sar "y" "a" "k") zeroState :=
    ⟨⟨by simp [liftEnv, zeroState], by simp [liftEnv, zeroState]⟩,
      srcRun_exists N leafSpec _ rfl _⟩
  have h1 : Admissible N leafSpec id (fun _ => none) (.shift .sar "y" "a" "k") kOneState :=
    ⟨⟨by simp [liftEnv, kOneState], by simp [liftEnv, kOneState]⟩,
      srcRun_exists N leafSpec _ rfl _⟩
  have := h zeroState kOneState ⟨zero_kOne_agree _ rfl, h0, h1⟩
  simp [lowerCF, mcfLeak, ShiftKind.toJInstr, instrLeakCT, instrLeak, JInstr.dataArgs,
    JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing, zeroState, kOneState,
    JState.get] at this

/-- A loop whose runtime bound is the secret `k` is not constant time at the
    machine: its `trip` event carries the bound. -/
theorem secretBound_lowered_not_ct (N : Nat) (leafSpec : LeafSpec) :
    ¬ ConstantTime
      (fun js₁ js₂ : JState 64 => agreePub (fun r => r != "k") js₁ js₂ ∧
        Admissible N leafSpec id (fun _ => none) (.forRt "i" "c" "k" .skip) js₁ ∧
        Admissible N leafSpec id (fun _ => none) (.forRt "i" "c" "k" .skip) js₂)
      (fun js => mcfLeak .doitm js (lowerCF id id (.forRt "i" "c" "k" .skip))) := by
  intro h
  have hadm : ∀ js : JState 64, Admissible N leafSpec id (fun _ => none)
      (.forRt "i" "c" "k" .skip) js := fun js =>
    ⟨⟨(js.get "k").isLt, iterAll_of_forall _ _ _ (fun _ => trivial) _ _ _⟩,
      srcRun_exists N leafSpec _ rfl _⟩
  have := h zeroState kOneState ⟨zero_kOne_agree _ rfl, hadm _, hadm _⟩
  simp [lowerCF, mcfLeak, mcfExec, instrLeakCT, instrLeak, movImm, evalInstr, x86_MOV,
    JOperand.eval, JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing, zeroState, kOneState,
    JState.get, JState.setReg] at this

/-- A guarded loop on the secret scalar `k` is not constant time at the machine: from
    `k = 0` it tests the guard once, from `k = 1` it runs one iteration and tests the
    guard twice. -/
theorem secretWhile_lowered_not_ct (N : Nat) (leafSpec : LeafSpec) :
    ¬ ConstantTime
      (fun js₁ js₂ : JState 64 => agreePub (fun r => r != "k") js₁ js₂ ∧
        Admissible N leafSpec id (fun _ => none) (.whileNz "k" (.setLit "k" 0)) js₁ ∧
        Admissible N leafSpec id (fun _ => none) (.whileNz "k" (.setLit "k" 0)) js₂)
      (fun js => mcfLeak .doitm js (lowerCF id id (.whileNz "k" (.setLit "k" 0)))) := by
  intro h
  have hk0 : liftEnv id zeroState "k" = 0 := by simp [liftEnv, zeroState, JState.get]
  have hk1 : liftEnv id kOneState "k" = 1 := by simp [liftEnv, kOneState, JState.get]
  have hset : ∀ σ : Env, srcDen (.setLit "k" 0) σ "k" = 0 := fun σ => by
    simp [srcDen, setS]
  have h0 : Admissible N leafSpec id (fun _ => none) (.whileNz "k" (.setLit "k" 0)) zeroState :=
    ⟨⟨0, hk0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩,
      _, _, .whileFalse _ _ _ hk0⟩
  have h1 : Admissible N leafSpec id (fun _ => none) (.whileNz "k" (.setLit "k" 0)) kOneState :=
    ⟨⟨1, hset (liftEnv id kOneState), fun j hj => by
        obtain rfl : j = 0 := by omega
        simp only [Function.iterate_zero, id, hk1]
        exact ⟨one_ne_zero, by norm_num, trivial⟩⟩,
      _, _, .whileTrue _ _ _ _ _ 1 _ _ hk1 one_ne_zero (.scalarSet _ _ _)
        (.whileFalse _ _ _ (by simp [rsSetScalar]))⟩
  have := h zeroState kOneState ⟨zero_kOne_agree _ rfl, h0, h1⟩
  have hc0 : whileCount (fun s' => mcfExec s' (MCF.straight [movImm "k" 0]))
      (fun s' => s'.get "k" = 0) zeroState = 0 :=
    whileCount_eq _ _ _ 0 (by simp [zeroState, JState.get]) (fun j hj => absurd hj (by omega))
  have hc1 : whileCount (fun s' => mcfExec s' (MCF.straight [movImm "k" 0]))
      (fun s' => s'.get "k" = 0) kOneState = 1 := by
    refine whileCount_eq _ _ _ 1 ?_ fun j hj => ?_
    · simp [mcfExec, evalInstr_movImm, JState.get, JState.setReg]
    · obtain rfl : j = 0 := by omega
      simp [kOneState, JState.get]
  simp only [lowerCF, mcfLeak, id] at this
  rw [hc0, hc1] at this
  simp [whileLeak] at this

/-! ## 7. Recognition of the fragment and a decision for machine constant time -/

/-- The word expression of a scalar expression built from reads, literals, `+`, `&`,
    `^` and `*`, or `none`. -/
def WExpr.ofSExpr? : SExpr → Option WExpr
  | .SVar v => some (.var v)
  | .SLit n => some (.lit n)
  | .SAdd a b => return .bin .add (← WExpr.ofSExpr? a) (← WExpr.ofSExpr? b)
  | .SAnd a b => return .bin .and_ (← WExpr.ofSExpr? a) (← WExpr.ofSExpr? b)
  | .SXor a b => return .bin .xor_ (← WExpr.ofSExpr? a) (← WExpr.ofSExpr? b)
  | .SMul a b => return .bin .mul_ (← WExpr.ofSExpr? a) (← WExpr.ofSExpr? b)
  | _ => none

theorem WExpr.ofSExpr?_spec : ∀ (e : SExpr) (w : WExpr), WExpr.ofSExpr? e = some w →
    w.toSExpr = e := by
  intro e
  induction e with
  | SVar v => intro w h; simp only [WExpr.ofSExpr?, Option.some.injEq] at h; subst h; rfl
  | SLit n => intro w h; simp only [WExpr.ofSExpr?, Option.some.injEq] at h; subst h; rfl
  | SAdd a b iha ihb | SAnd a b iha ihb | SXor a b iha ihb | SMul a b iha ihb =>
    intro w h
    simp only [WExpr.ofSExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨wa, ha, wb, hb, rfl⟩ := h
    simp only [WExpr.toSExpr, arithNode, iha wa ha, ihb wb hb]
  | _ => intro w h; simp [WExpr.ofSExpr?] at h

/-- The machine names and leaf code the recogniser assigns: the counter of a loop at
    nesting depth `k` is `ctr k`, the discarded low word of `MULX` and the word
    register of a tower copy is `lo`, the temporaries of a word expression are
    `tmps`, and the owned code of a call of the leaf `f` into `dest` on `args` is
    `leaf f dest args` (a call with no code is not recognised). -/
structure CFNames where
  tmps : List String
  ctr : Nat → String
  lo : String
  leaf : String → Located → List Located → Option LeafCode

/-- The statement `dst := e`: a shift by a scalar count, the high word of a wide
    multiply, an unsigned comparison, a limb read, or a word expression. -/
def stmtOf? (nm : CFNames) (d : String) : SExpr → Option CFSrc
  | .SShr (.SVar a) (.SVar c) => some (.shift .shr d a c)
  | .SShl (.SVar a) (.SVar c) => some (.shift .shl d a c)
  | .SAsr (.SVar a) (.SVar c) => some (.shift .sar d a c)
  | .SMulHiU (.SVar a) (.SVar b) => some (.mulHi d a b nm.lo)
  | .SLt (.SVar a) (.SVar b) => some (.ltSet d a b)
  | .SLimb v i => some (.limbGet d v i)
  | e => (WExpr.ofSExpr? e).map fun w => .expr d w nm.tmps

theorem stmtOf?_spec (nm : CFNames) (d : String) (e : SExpr) (c : CFSrc)
    (h : stmtOf? nm d e = some c) : c.toLowCT = .RScalarSetExpr d e := by
  unfold stmtOf? at h
  split at h <;> simp only [Option.some.injEq, Option.map_eq_some_iff] at h
  · subst h; rfl
  · subst h; rfl
  · subst h; rfl
  · subst h; rfl
  · subst h; rfl
  · subst h; rfl
  · obtain ⟨w, hw, rfl⟩ := h
    simp only [CFSrc.toLowCT, WExpr.ofSExpr?_spec _ w hw]

/-- The recogniser of the fragment, at loop nesting depth `k`. -/
def toCFSrc? (nm : CFNames) : Nat → LowCT → Option CFSrc
  | _, .RSkip => some .skip
  | _, .RScalarSet d n => some (.setLit d n)
  | _, .RScalarSetExpr d e => stmtOf? nm d e
  | k, .RLetU64Zero x b => (toCFSrc? nm k b).map (.letU64 x)
  | _, .RSelect dst sel s0 s1 => some (.select dst sel s0 s1)
  | _, .RArrLoad dst src idx => some (.arrLoad dst src idx)
  | _, .RArrStore arr idx src => some (.arrStore arr idx src)
  | k, .RSeq a b => return .seq (← toCFSrc? nm k a) (← toCFSrc? nm k b)
  | k, .RIfNz g t e => return .ifNz g (← toCFSrc? nm k t) (← toCFSrc? nm k e)
  | k, .RFor x n b => (toCFSrc? nm (k + 1) b).map (.forLit x (nm.ctr k) n)
  | k, .RForRuntime x (.SVar bnd) b => (toCFSrc? nm (k + 1) b).map (.forRt x (nm.ctr k) bnd)
  | k, .RWhileNz g b => (toCFSrc? nm k b).map (.whileNz g)
  | k, .RLetZero x t b => (toCFSrc? nm k b).map (.letT x t)
  | _, .RCall f dest args => (nm.leaf f dest args).map (.call f dest args)
  | _, .RCopy dst src => some (.copy dst src nm.lo)
  | _, .RLimbStoreExpr loc idx e => (WExpr.ofSExpr? e).map fun w => .limbSet loc idx w nm.tmps
  | _, _ => none

/-- The recognised program embeds back to the program it was recognised from. -/
theorem toCFSrc?_spec (nm : CFNames) :
    ∀ (k : Nat) (c : LowCT) (cf : CFSrc), toCFSrc? nm k c = some cf → cf.toLowCT = c := by
  intro k c
  induction c generalizing k with
  | RSkip => intro cf h; simp only [toCFSrc?, Option.some.injEq] at h; subst h; rfl
  | RScalarSet d n => intro cf h; simp only [toCFSrc?, Option.some.injEq] at h; subst h; rfl
  | RScalarSetExpr d e => intro cf h; exact stmtOf?_spec nm d e cf h
  | RLetU64Zero x b ih =>
    intro cf h
    simp only [toCFSrc?, Option.map_eq_some_iff] at h
    obtain ⟨b', hb, rfl⟩ := h
    simp only [CFSrc.toLowCT, ih k b' hb]
  | RSelect dst sel s0 s1 =>
    intro cf h; simp only [toCFSrc?, Option.some.injEq] at h; subst h; rfl
  | RArrLoad dst src idx =>
    intro cf h; simp only [toCFSrc?, Option.some.injEq] at h; subst h; rfl
  | RArrStore arr idx src =>
    intro cf h; simp only [toCFSrc?, Option.some.injEq] at h; subst h; rfl
  | RSeq a b iha ihb =>
    intro cf h
    simp only [toCFSrc?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    simp only [CFSrc.toLowCT, iha k a' ha, ihb k b' hb]
  | RIfNz g t e iht ihe =>
    intro cf h
    simp only [toCFSrc?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨t', ht, e', he, rfl⟩ := h
    simp only [CFSrc.toLowCT, iht k t' ht, ihe k e' he]
  | RFor x n b ih =>
    intro cf h
    simp only [toCFSrc?, Option.map_eq_some_iff] at h
    obtain ⟨b', hb, rfl⟩ := h
    simp only [CFSrc.toLowCT, ih (k + 1) b' hb]
  | RForRuntime x bound b ih =>
    intro cf h
    cases bound with
    | SVar bnd =>
      simp only [toCFSrc?, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [CFSrc.toLowCT, ih (k + 1) b' hb]
    | _ => simp [toCFSrc?] at h
  | RWhileNz g b ih =>
    intro cf h
    simp only [toCFSrc?, Option.map_eq_some_iff] at h
    obtain ⟨b', hb, rfl⟩ := h
    simp only [CFSrc.toLowCT, ih k b' hb]
  | RLetZero x t b ih =>
    intro cf h
    simp only [toCFSrc?, Option.map_eq_some_iff] at h
    obtain ⟨b', hb, rfl⟩ := h
    simp only [CFSrc.toLowCT, ih k b' hb]
  | RCall f dest args =>
    intro cf h
    simp only [toCFSrc?, Option.map_eq_some_iff] at h
    obtain ⟨code, -, rfl⟩ := h
    rfl
  | RCopy dst src => intro cf h; simp only [toCFSrc?, Option.some.injEq] at h; subst h; rfl
  | RLimbStoreExpr loc idx e =>
    intro cf h
    simp only [toCFSrc?, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    simp only [CFSrc.toLowCT, WExpr.ofSExpr?_spec e w hw]
  | _ => intro cf h; simp [toCFSrc?] at h

/-- A register allocation: an injective map `ρ` of scalars to registers whose image
    is recognised by `inImg`, and a map `τ` of towers to registers. -/
structure RegAlloc where
  ρ : RegMap
  τ : RegMap
  inj : Function.Injective ρ
  inImg : String → Bool
  inImg_spec : ∀ v, inImg (ρ v) = true

theorem RegAlloc.ne_of_inImg (A : RegAlloc) {r : String} (h : A.inImg r = false) :
    ∀ v, A.ρ v ≠ r := fun v hv => by rw [← hv, A.inImg_spec] at h; cases h

/-- The register-allocation side conditions `CFSrc.RegWF` as a Boolean. -/
def regWfB (A : RegAlloc) : CFSrc → Bool
  | .skip | .setLit .. | .shift .. | .arrStore .. | .ltSet .. | .limbGet .. => true
  | .arith p => p.b != p.dst
  | .expr _ e ts => ts.all (fun t => !A.inImg t) && decide ts.Nodup && decide (e.depth ≤ ts.length)
  | .letU64 _ b | .whileNz _ b | .letT _ _ b => regWfB A b
  | .mulHi _ _ _ lo | .copy _ _ lo => !A.inImg lo
  | .select dst .. | .arrLoad dst .. => !A.inImg (A.τ dst.locVar)
  | .seq a b | .ifNz _ a b => regWfB A a && regWfB A b
  | .forLit _ ctr _ b | .forRt _ ctr _ b =>
      !A.inImg ctr && !((b.writes A.τ).contains ctr) && regWfB A b
  | .call _ _ _ code => code.clob.all (fun t => !A.inImg t)
  | .limbSet _ _ _ ts => ts.all (fun t => !A.inImg t)

theorem regWfB_spec (A : RegAlloc) : ∀ (c : CFSrc), regWfB A c = true → c.RegWF A.ρ A.τ
  | .skip, _ | .setLit .., _ | .shift .., _ | .arrStore .., _ | .ltSet .., _
  | .limbGet .., _ => trivial
  | .arith p, h => by simpa [regWfB, CFSrc.RegWF] using h
  | .expr _ e ts, h => by
    simp only [regWfB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at h
    exact ⟨fun v t ht => A.ne_of_inImg (h.1.1 t ht) v, h.1.2, h.2⟩
  | .letU64 _ b, h | .whileNz _ b, h | .letT _ _ b, h => regWfB_spec A b h
  | .mulHi _ _ _ lo, h | .copy _ _ lo, h => by
    simp only [regWfB, Bool.not_eq_true'] at h
    exact A.ne_of_inImg h
  | .select dst .., h | .arrLoad dst .., h => by
    simp only [regWfB, Bool.not_eq_true'] at h
    exact A.ne_of_inImg h
  | .seq a b, h | .ifNz _ a b, h => by
    simp only [regWfB, Bool.and_eq_true] at h
    exact ⟨regWfB_spec A a h.1, regWfB_spec A b h.2⟩
  | .forLit _ ctr _ b, h | .forRt _ ctr _ b, h => by
    simp only [regWfB, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨A.ne_of_inImg h.1.1, by simpa using h.1.2, regWfB_spec A b h.2⟩
  | .call _ _ _ code, h => by
    simp only [regWfB, List.all_eq_true, Bool.not_eq_true'] at h
    exact fun v t ht => A.ne_of_inImg (h t ht) v
  | .limbSet _ _ _ ts, h => by
    simp only [regWfB, List.all_eq_true, Bool.not_eq_true'] at h
    exact fun v t ht => A.ne_of_inImg (h t ht) v

/-- The scalar writes of a program: the destination, whether the write is a limb
    read, and the scalars the written value is computed from. -/
def CFSrc.flows : CFSrc → List (String × Bool × List String)
  | .arith p => [(p.dst, false, [p.a, p.b])]
  | .expr d e _ => [(d, false, e.vars)]
  | .shift _ d a c => [(d, false, [a, c])]
  | .mulHi d a b _ | .ltSet d a b => [(d, false, [a, b])]
  | .limbGet d _ _ => [(d, true, [])]
  | .letU64 _ b | .letT _ _ b | .forLit _ _ _ b | .forRt _ _ _ b | .whileNz _ b => b.flows
  | .seq a b | .ifNz _ a b => a.flows ++ b.flows
  | _ => []

/-- One propagation round: a destination written by a limb read or from a scalar of
    `O` is added to `O`. -/
def opqStep (fl : List (String × Bool × List String)) (O : List String) : List String :=
  fl.foldl (fun acc w =>
    if (w.2.1 || w.2.2.any acc.contains) && !acc.contains w.1 then w.1 :: acc else acc) O

/-- The opaque scalars of a program: the propagation of `opqStep` from limb reads,
    run once per scalar write and once more. -/
def opqOf (c : CFSrc) : String → Bool :=
  let fl := c.flows
  let O := (opqStep fl)^[fl.length + 1] []
  fun v => O.contains v

/-- The side conditions `CFSrc.WF` as a Boolean: `regWfB` and the taint condition
    for `opqOf c`. -/
def wfB (A : RegAlloc) (c : CFSrc) : Bool := regWfB A c && c.taint (opqOf c)

theorem wfB_spec (A : RegAlloc) (c : CFSrc) (h : wfB A c = true) : c.WF A.ρ A.τ := by
  simp only [wfB, Bool.and_eq_true] at h
  exact ⟨regWfB_spec A c h.1, _, h.2⟩

/-- A predicate on scalar names with one name updated. -/
def updB (B : String → Bool) (x : String) (b : Bool) : String → Bool :=
  fun y => if y == x then b else B y

/-- Whether a word expression is below `2^64` when the names `B` are: reads of `B`,
    literals below `2^64`, `&` with a bounded operand, `^` of bounded operands. -/
def WExpr.boundedB (B : String → Bool) : WExpr → Bool
  | .var v => B v
  | .lit n => decide (n < 2 ^ 64)
  | .bin .and_ a b => a.boundedB B || b.boundedB B
  | .bin .xor_ a b => a.boundedB B && b.boundedB B
  | .bin _ _ _ => false

/-- The names below `2^64` after `c`, starting from the names `B`, or `none` when a
    range condition of `c` is not established: a guard or index not known below
    `2^64`, a shift by a scalar count, or a loop. -/
def rangeB (B : String → Bool) : CFSrc → Option (String → Bool)
  | .skip => some B
  | .arith p => some (updB B p.dst false)
  | .setLit d n => some (updB B d (decide (n < 2 ^ 64)))
  | .expr d e _ => some (updB B d (e.boundedB B))
  | .letU64 x body => rangeB (updB B x true) body
  | .mulHi d .. => some (updB B d false)
  | .select .. => some B
  | .arrLoad _ _ idx | .arrStore _ idx _ => if B idx then some B else none
  | .seq a b => (rangeB B a).bind fun B' => rangeB B' b
  | .ifNz g t e =>
      if B g then
        match rangeB B t, rangeB B e with
        | some Bt, some Be => some fun y => Bt y && Be y
        | _, _ => none
      else none
  | .ltSet d a b => if B a && B b then some (updB B d true) else none
  | .call .. | .copy .. | .limbSet .. => some B
  | .letT _ _ body => rangeB B body
  | .limbGet d .. => some (updB B d true)
  | .shift .. | .forLit .. | .forRt .. | .whileNz .. => none

/-- The names `B` hold values below `2^64` in `σ`. -/
def BoundedBy (B : String → Bool) (σ : Env) : Prop := ∀ x, B x = true → σ x < 2 ^ 64

theorem BoundedBy.upd {B : String → Bool} {σ : Env} (h : BoundedBy B σ) (x : String)
    (b : Bool) (v : Nat) (hv : b = true → v < 2 ^ 64) : BoundedBy (updB B x b) (setS σ x v) := by
  intro y hy
  simp only [updB, setS] at hy ⊢
  split
  · rw [ite_eq_left (by assumption)] at hy; exact hv hy
  · rw [ite_eq_right (by assumption)] at hy; exact h y hy

theorem WExpr.boundedB_spec {B : String → Bool} {σ : Env} (h : BoundedBy B σ) :
    ∀ e : WExpr, e.boundedB B = true → e.toSExpr.eval σ < 2 ^ 64
  | .var v, hb => h v hb
  | .lit n, hb => by simpa [WExpr.boundedB, WExpr.toSExpr, SExpr.eval] using hb
  | .bin .and_ a b, hb => by
    simp only [WExpr.boundedB, Bool.or_eq_true] at hb
    simp only [WExpr.toSExpr, arithNode, SExpr.eval]
    rcases hb with ha | hb
    · exact lt_of_le_of_lt Nat.and_le_left (WExpr.boundedB_spec h a ha)
    · exact Nat.and_lt_two_pow _ (WExpr.boundedB_spec h b hb)
  | .bin .xor_ a b, hb => by
    simp only [WExpr.boundedB, Bool.and_eq_true] at hb
    simp only [WExpr.toSExpr, arithNode, SExpr.eval]
    exact Nat.xor_lt_two_pow (WExpr.boundedB_spec h a hb.1) (WExpr.boundedB_spec h b hb.2)
  | .bin .add _ _, hb | .bin .mul_ _ _, hb => by simp [WExpr.boundedB] at hb

/-- Soundness of `rangeB`: from a state bounded on `B`, the range conditions hold and
    the post-state is bounded on the returned names. -/
theorem rangeB_sound : ∀ (c : CFSrc) (B B' : String → Bool) (σ : Env), BoundedBy B σ →
    rangeB B c = some B' → InRange c σ ∧ BoundedBy B' (srcDen c σ)
  | .skip, B, B', σ, h, hr => by
    simp only [rangeB, Option.some.injEq] at hr; subst hr; exact ⟨trivial, h⟩
  | .arith p, B, B', σ, h, hr => by
    simp only [rangeB, Option.some.injEq] at hr; subst hr
    exact ⟨trivial, h.upd _ _ _ (by simp)⟩
  | .setLit d n, B, B', σ, h, hr => by
    simp only [rangeB, Option.some.injEq] at hr; subst hr
    exact ⟨trivial, h.upd _ _ _ (by simp)⟩
  | .expr d e _, B, B', σ, h, hr => by
    simp only [rangeB, Option.some.injEq] at hr; subst hr
    exact ⟨trivial, h.upd _ _ _ (WExpr.boundedB_spec h e)⟩
  | .letU64 x body, B, B', σ, h, hr =>
    rangeB_sound body _ B' _ (h.upd x true 0 (fun _ => by norm_num)) hr
  | .mulHi d .., B, B', σ, h, hr => by
    simp only [rangeB, Option.some.injEq] at hr; subst hr
    exact ⟨trivial, h.upd _ _ _ (by simp)⟩
  | .select .., B, B', σ, h, hr => by
    simp only [rangeB, Option.some.injEq] at hr; subst hr; exact ⟨trivial, h⟩
  | .arrLoad _ _ idx, B, B', σ, h, hr | .arrStore _ idx _, B, B', σ, h, hr => by
    simp only [rangeB] at hr
    split at hr
    · simp only [Option.some.injEq] at hr; subst hr; exact ⟨h idx (by assumption), h⟩
    · cases hr
  | .seq a b, B, B', σ, h, hr => by
    simp only [rangeB, Option.bind_eq_some_iff] at hr
    obtain ⟨Ba, ha, hb⟩ := hr
    obtain ⟨hia, hba⟩ := rangeB_sound a B Ba σ h ha
    obtain ⟨hib, hbb⟩ := rangeB_sound b Ba B' _ hba hb
    exact ⟨⟨hia, hib⟩, hbb⟩
  | .ifNz g t e, B, B', σ, h, hr => by
    simp only [rangeB] at hr
    split at hr
    · rename_i hg
      split at hr
      · rename_i Bt Be ht he
        simp only [Option.some.injEq] at hr; subst hr
        obtain ⟨hit, hbt⟩ := rangeB_sound t B Bt σ h ht
        obtain ⟨hie, hbe⟩ := rangeB_sound e B Be σ h he
        refine ⟨⟨h g hg, ?_⟩, ?_⟩
        · split <;> assumption
        · intro y hy
          simp only [Bool.and_eq_true] at hy
          simp only [srcDen]
          split
          · exact hbe y hy.2
          · exact hbt y hy.1
      · cases hr
    · cases hr
  | .ltSet d a b, B, B', σ, h, hr => by
    simp only [rangeB] at hr
    split at hr
    · rename_i hab
      simp only [Bool.and_eq_true] at hab
      simp only [Option.some.injEq] at hr; subst hr
      refine ⟨⟨h a hab.1, h b hab.2⟩, h.upd _ _ _ fun _ => ?_⟩
      split <;> norm_num
    · cases hr
  | .call .., B, B', σ, h, hr | .copy .., B, B', σ, h, hr | .limbSet .., B, B', σ, h, hr => by
    simp only [rangeB, Option.some.injEq] at hr; subst hr; exact ⟨trivial, h⟩
  | .letT _ _ body, B, B', σ, h, hr => rangeB_sound body B B' σ h hr
  | .limbGet d .., B, B', σ, h, hr => by
    simp only [rangeB, Option.some.injEq] at hr; subst hr
    exact ⟨trivial, h.upd _ _ _ fun _ => by norm_num⟩
  | .shift .., _, _, _, _, hr | .forLit .., _, _, _, _, hr | .forRt .., _, _, _, _, hr
  | .whileNz .., _, _, _, _, hr => by
    cases hr

theorem liftEnv_bounded (ρ : RegMap) (js : JState 64) :
    BoundedBy (fun _ => true) (liftEnv ρ js) := fun v _ => (js.get (ρ v)).isLt

section Routes

variable (N : Nat) (leafSpec : LeafSpec)

/-- **Source constant time to machine constant time, for a recognised program.** If
    `c` is recognised as `cf`, the register allocation satisfies the side conditions
    and `c` is constant time for `lt`, the lowering of `cf` is constant time for
    admissible machine states agreeing on the public registers. -/
theorem machine_ct_of_lowct (A : RegAlloc) (nm : CFNames) (lt : LevelTable) (pub : PubPred)
    (T : String → Option (Σ t : TowerType, RustVal t)) (c : LowCT) (cf : CFSrc)
    (hrec : toCFSrc? nm 0 c = some cf) (hwf : wfB A cf = true)
    (hpub : ∀ x, lt x = .Public → pub (A.ρ x) = true)
    (hsrc : LowCTConstantTime N leafSpec .owned lt c) :
    ConstantTime
      (fun js₁ js₂ : JState 64 => agreePub pub js₁ js₂ ∧
        Admissible N leafSpec A.ρ T cf js₁ ∧ Admissible N leafSpec A.ρ T cf js₂)
      (fun js => mcfLeak .doitm js (lowerCF A.ρ A.τ cf)) := by
  have hc := toCFSrc?_spec nm 0 c cf hrec
  subst hc
  exact lowct_to_machine_ct N leafSpec lt pub A.ρ A.τ T A.inj cf (wfB_spec A cf hwf) hpub hsrc

/-- **Machine constant time for every pair of public-agreeing states.** For a
    recognised program whose tower accesses are to names it binds (`towerOk`) and that
    passes `rangeB`, source constant time gives machine constant time of the lowering
    for all machine states agreeing on the public registers. -/
theorem machine_ct_of_lowct_closed (A : RegAlloc) (nm : CFNames) (lt : LevelTable)
    (pub : PubPred) (c : LowCT) (cf : CFSrc) (B' : String → Bool)
    (hrec : toCFSrc? nm 0 c = some cf) (hwf : wfB A cf = true) (htf : cf.towerOk = true)
    (hrange : rangeB (fun _ => true) cf = some B')
    (hpub : ∀ x, lt x = .Public → pub (A.ρ x) = true)
    (hsrc : LowCTConstantTime N leafSpec .owned lt c) :
    ConstantTime (fun js₁ js₂ : JState 64 => agreePub pub js₁ js₂)
      (fun js => mcfLeak .doitm js (lowerCF A.ρ A.τ cf)) := by
  have hc := toCFSrc?_spec nm 0 c cf hrec
  subst hc
  intro js₁ js₂ hag
  exact lowct_to_machine_ct_towerOk N leafSpec lt pub A.ρ A.τ A.inj cf (wfB_spec A cf hwf) htf
    hpub hsrc js₁ js₂
    ⟨hag, (rangeB_sound cf _ B' _ (liftEnv_bounded A.ρ js₁) hrange).1,
      (rangeB_sound cf _ B' _ (liftEnv_bounded A.ρ js₂) hrange).1⟩

/-- **Route through the level checker.** A recognised program accepted by
    `levelCheck` from `lt` lowers to machine code that is constant time for admissible
    machine states agreeing on the public registers. -/
theorem machine_ct_of_levelCheck (A : RegAlloc) (nm : CFNames) (lt lt' : LevelTable)
    (pub : PubPred) (T : String → Option (Σ t : TowerType, RustVal t)) (c : LowCT)
    (cf : CFSrc) (hchk : levelCheck .owned lt c = some lt') (hrec : toCFSrc? nm 0 c = some cf)
    (hwf : wfB A cf = true) (hpub : ∀ x, lt x = .Public → pub (A.ρ x) = true) :
    ConstantTime
      (fun js₁ js₂ : JState 64 => agreePub pub js₁ js₂ ∧
        Admissible N leafSpec A.ρ T cf js₁ ∧ Admissible N leafSpec A.ρ T cf js₂)
      (fun js => mcfLeak .doitm js (lowerCF A.ρ A.τ cf)) :=
  machine_ct_of_lowct N leafSpec A nm lt pub T c cf hrec hwf hpub
    (levelCheck_sound (N := N) (leafSpec := leafSpec) hchk).1

end Routes

/-- The recognised program when it satisfies the decided side conditions, accesses
    only towers it binds and passes `rangeB`. -/
def toCFSrcClosed? (A : RegAlloc) (nm : CFNames) (c : LowCT) : Option CFSrc :=
  (toCFSrc? nm 0 c).filter fun cf =>
    wfB A cf && cf.towerOk && (rangeB (fun _ => true) cf).isSome

theorem toCFSrcClosed?_spec {A : RegAlloc} {nm : CFNames} {c : LowCT} {cf : CFSrc}
    (h : toCFSrcClosed? A nm c = some cf) :
    toCFSrc? nm 0 c = some cf ∧ wfB A cf = true ∧ cf.towerOk = true ∧
      ∃ B', rangeB (fun _ => true) cf = some B' := by
  simp only [toCFSrcClosed?, Option.filter_eq_some_iff, Bool.and_eq_true,
    Option.isSome_iff_exists] at h
  exact ⟨h.1, h.2.1.1, h.2.1.2, h.2.2⟩

/-- **The decision.** `c` is accepted by `levelCheck` from `lt`, is recognised, and
    its recognised program satisfies the decided side conditions, accesses only
    towers it binds and passes `rangeB`. -/
def machineCTCheck (A : RegAlloc) (nm : CFNames) (lt : LevelTable) (c : LowCT) : Bool :=
  (levelCheck .owned lt c).isSome && (toCFSrcClosed? A nm c).isSome

/-- **Soundness of the decision.** An accepted program is recognised as a program
    whose lowering is constant time for every pair of machine states agreeing on the
    public registers. The leaf specification is arbitrary: the lowering of a leaf
    call is its owned code, whose trace does not depend on the state. -/
theorem machineCTCheck_sound (leafSpec : LeafSpec) (A : RegAlloc) (nm : CFNames)
    (lt : LevelTable) (pub : PubPred) (c : LowCT) (h : machineCTCheck A nm lt c = true)
    (hpub : ∀ x, lt x = .Public → pub (A.ρ x) = true) :
    ∃ cf, toCFSrc? nm 0 c = some cf ∧ cf.toLowCT = c ∧
      ConstantTime (fun js₁ js₂ : JState 64 => agreePub pub js₁ js₂)
        (fun js => mcfLeak .doitm js (lowerCF A.ρ A.τ cf)) := by
  simp only [machineCTCheck, Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨lt', hchk⟩, cf, hcf⟩ := h
  obtain ⟨hrec, hwf, htf, B', hr⟩ := toCFSrcClosed?_spec hcf
  exact ⟨cf, hrec, toCFSrc?_spec nm 0 c cf hrec,
    machine_ct_of_lowct_closed 0 leafSpec A nm lt pub c cf B' hrec hwf htf hr hpub
      (levelCheck_sound hchk).1⟩

/-- **The decision for admissible states.** `c` is accepted by `levelCheck` from
    `lt`, is recognised, and its recognised program satisfies the decided side
    conditions. It admits guarded loops, loops and tower accesses whose runs and
    range conditions are left to the machine states (`Admissible`). -/
def machineCTCheckAdm (A : RegAlloc) (nm : CFNames) (lt : LevelTable) (c : LowCT) : Bool :=
  (levelCheck .owned lt c).isSome && ((toCFSrc? nm 0 c).filter (wfB A)).isSome

/-- **Soundness of the decision for admissible states.** An accepted program is
    recognised as a program whose lowering is constant time for every pair of
    machine states agreeing on the public registers that are admissible for the
    tower heap `T`. -/
theorem machineCTCheckAdm_sound (N : Nat) (leafSpec : LeafSpec) (A : RegAlloc) (nm : CFNames)
    (lt : LevelTable) (pub : PubPred) (c : LowCT) (h : machineCTCheckAdm A nm lt c = true)
    (hpub : ∀ x, lt x = .Public → pub (A.ρ x) = true) :
    ∃ cf, toCFSrc? nm 0 c = some cf ∧ cf.toLowCT = c ∧
      ∀ T : String → Option (Σ t : TowerType, RustVal t),
      ConstantTime
        (fun js₁ js₂ : JState 64 => agreePub pub js₁ js₂ ∧
          Admissible N leafSpec A.ρ T cf js₁ ∧ Admissible N leafSpec A.ρ T cf js₂)
        (fun js => mcfLeak .doitm js (lowerCF A.ρ A.τ cf)) := by
  simp only [machineCTCheckAdm, Bool.and_eq_true, Option.isSome_iff_exists,
    Option.filter_eq_some_iff] at h
  obtain ⟨⟨lt', hchk⟩, cf, hrec, hwf⟩ := h
  exact ⟨cf, hrec, toCFSrc?_spec nm 0 c cf hrec, fun T =>
    machine_ct_of_levelCheck N leafSpec A nm lt lt' pub T c cf hchk hrec hwf hpub⟩

/-- The register of a name under the prefix `p`: `p` followed by the name. -/
def prefixed (p : Char) (v : String) : String := String.ofList (p :: v.toList)

theorem prefixed_toList (p : Char) (v : String) : (prefixed p v).toList = p :: v.toList := by
  simp [prefixed]

/-- Scalar `v` in register `s` followed by `v`; tower `v` in register `t` followed by
    `v`. -/
def stdAlloc : RegAlloc where
  ρ := prefixed 's'
  τ := prefixed 't'
  inj := fun a b h => by
    have := congrArg String.toList h
    simp only [prefixed_toList, List.cons.injEq, true_and] at this
    exact String.toList_inj.mp this
  inImg r := r.toList.head? == some 's'
  inImg_spec v := by simp [prefixed_toList]

/-- The complement of the word at `[a]` in `w` bits, stored to `[d]` through the
    register `t`: `MOV t, [a]; NOT t`, a zero extension from `w` bits when `w < 64`,
    and `MOV [d], t`. -/
def notBlk (d a t : String) (w : Nat) : List (JInstr 64) :=
  [.loadMem t a 0, .not_ t] ++ (if w < 64 then [.movzx t w t] else []) ++ [.storeMem d 0 (.reg t)]

/-- The owned code of the complement leaf `Not#w`: `notBlk`, writing only `t`, with
    the two address events of its load and store. -/
def notCode (d a t : String) (w : Nat) : LeafCode where
  blk := notBlk d a t w
  clob := [t]
  leak := [.addr a 0, .addr d 0]
  leak_eq s := by
    unfold notBlk
    split <;> simp [instrLeakCT, instrLeak, mleakToCT, JInstr.mnem, DoitRegime.leaksOperands,
      X86Mnem.timing]
  get_other s r hr := by
    simp only [List.mem_singleton] at hr
    unfold notBlk
    split <;> simp [evalInstr, JState.store, JState.get, JState.setReg, hr]

/-- The width of a complement leaf `Not#w`. -/
def notWidth? : String → Option Nat
  | "Not#8" => some 8
  | "Not#16" => some 16
  | "Not#32" => some 32
  | "Not#64" => some 64
  | "Not#size" => some 64
  | _ => none

/-- The leaf code of `stdNames`: a complement `Not#w` of one argument, through the
    register `t`, on the tower registers of `stdAlloc`. -/
def stdLeaf (t f : String) (dest : Located) : List Located → Option LeafCode
  | [a] => (notWidth? f).map fun w => notCode (prefixed 't' dest.locVar) (prefixed 't' a.locVar) t w
  | _ => none

/-- Eight temporaries, the loop counter `c` followed by the depth, the `MULX` low
    word `lo`, and the complement leaves through `lo`; none starts with `s`. -/
def stdNames : CFNames where
  tmps := ["w0", "w1", "w2", "w3", "w4", "w5", "w6", "w7"]
  ctr k := "c" ++ toString k
  lo := "lo"
  leaf := stdLeaf "lo"

/-- The public registers of `lt` under `stdAlloc`: `s` followed by a public name. -/
def stdPub (lt : LevelTable) : PubPred := fun r =>
  match r.toList with
  | 's' :: v => lt (String.ofList v) == .Public
  | _ => false

theorem stdPub_spec (lt : LevelTable) (x : String) (hx : lt x = .Public) :
    stdPub lt (stdAlloc.ρ x) = true := by
  simp [stdPub, stdAlloc, prefixed_toList, hx]
  rfl

/-- A branch on a scalar read from a tower limb fails the decided side conditions:
    the guard is opaque. -/
theorem limbGuard_rejected :
    wfB stdAlloc (.seq (.limbGet "g" "t" 0) (.ifNz "g" .skip .skip)) = false := by
  decide

end CatCrypt.Crypto.SecureCompilation.CT.LowCTMachine
