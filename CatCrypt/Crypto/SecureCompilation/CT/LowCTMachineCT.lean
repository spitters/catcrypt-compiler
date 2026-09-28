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
wide multiplies, variable shifts and runtime-bound loops to structured machine
blocks `MCF`, and the preservation of constant time from the source model of
`CT/LowCTLeakage.lean` (`RustExecLeak`, `LowCTConstantTime`) to the machine
model of `CT/Leakage.lean`.

* `MCF` is `MachineConstantTime.OwnedCF 64` with a loop `loopRt r` whose trip
  count is the value of register `r` at loop entry; `mcfExec` and `mcfLeak` are
  its semantics and leakage, the runtime loop emitting a `trip` event.
  `mcfExec_ofOwned` and `mcfLeak_ofOwned` state that on `OwnedCF` they are
  `cfExec` and `cfLeakCT`.
* `CFSrc` is the fragment: two-operand arithmetic (`ArithSrc`), literal
  assignments, word expressions (`WExpr`: reads, literals, `+`, `&`, `^`, `*`,
  lowered by `lowerW` through temporary registers), `RLetU64Zero`, variable shifts
  (`SShr`, `SShl`, `SAsr` by a scalar count), the high word of the unsigned
  wide multiply (`SMulHiU`), `RSelect`, `RArrLoad`, `RArrStore`, sequence,
  `RIfNz`, `RFor` with a literal trip count and `RForRuntime` with a scalar bound.
  `CFSrc.toLowCT` embeds it in `LowCT`.
* `lowerCF ρ τ` lowers it to `MCF`, with `ρ` the register of each scalar and `τ`
  the register of each tower variable: shifts to `SHRX`/`SHLX`/`SARX`, the wide
  multiply to `MULX`, the select to `MOV; TEST; CMOVNE`, array accesses to
  `loadMemIdx`/`storeMemIdx` at scale 8 over the base register `τ arr`.
* `srcDen` and `srcLeak` are the scalar post-state and the trace of the source;
  `srcRun_det` states that every run of `c.toLowCT` has this trace and scalar
  post-state. Tower values are not tracked: the leaf oracles of `LeafSpec` are
  abstract, and no trace event depends on a tower value.
* `lowerCF_leak` is the leak transformer: from matching states, the machine trace
  is the source trace mapped by `leakXf τ`, which sends the source element event
  `addr a i` to the machine address event `addr (τ a) (8 * i)` and fixes every
  other event, provided the scalar values the run tests, indexes, shifts by or
  loops to are in range (`InRange`).
* `lowct_to_machine_ct` derives machine `ConstantTime` from `LowCTConstantTime`
  for machine states agreeing on the public registers whose source images have a
  run and satisfy `InRange`; `lowct_to_machine_ct_towerFree` and
  `lowct_to_machine_ct_rangeFree` discharge the run and the range condition on
  the corresponding subfragments.
* `lowerShift_mnem`, `lowerMulHi_mnem` and `lowerArith_mnem` state that the
  lowering emits the mnemonic `sexprMnem` assigns to the source expression;
  `ShiftKind.x86_ofNat` is the denotation of the shifts.
* The negative controls `secretGuard_lowered_not_ct`, `secretIndex_lowered_not_ct`,
  `secretShift_lowered_not_ct` and `secretBound_lowered_not_ct` show that the
  lowering of a secret guard, index, `SARX` count or loop bound is not constant
  time under the preconditions of `lowct_to_machine_ct`.
* `toCFSrc? nm k c` recognises a `LowCT` program as a program of the fragment, with
  the names of loop counters, `MULX` low words and temporaries taken from `nm`;
  `toCFSrc?_spec` states that the recognised program embeds back to `c`. `wfB A`
  decides `CFSrc.WF` for a register allocation `A` whose image is recognised by a
  Boolean (`RegAlloc`); `rangeB` is a sufficient check of `InRange` for every state
  whose values are below `2^64` (`rangeB_sound`), rejecting shifts by a scalar count
  and loops.
* `machine_ct_of_lowct` and `machine_ct_of_lowct_closed` derive machine constant
  time of the lowering of a recognised program from `LowCTConstantTime`, the second
  for every pair of machine states agreeing on the public registers;
  `machine_ct_of_levelCheck` derives it from acceptance by `levelCheck`.
  `machineCTCheck` is a Boolean decision and `machineCTCheck_sound` its soundness.
* `stdAlloc`, `stdNames` and `stdPub lt` are a register allocation, a name supply
  outside its image, and the public registers of `lt` under it (`stdPub_spec`).
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

/-- The machine semantics of `MCF`. -/
def mcfExec : JState 64 → MCF → JState 64
  | s, .straight body => runBlock s body
  | s, .seq a b => mcfExec (mcfExec s a) b
  | s, .ifPub g t e => if s.get g = 0 then mcfExec s e else mcfExec s t
  | s, .loop n body => (fun s' => mcfExec s' body)^[n] s
  | s, .loopRt g body => (fun s' => mcfExec s' body)^[(s.get g).toNat] s

/-- The leakage of `MCF` under a regime: as `cfLeakCT`, and a runtime loop emits
    its trip count before its iterations. -/
def mcfLeak (r : DoitRegime) : JState 64 → MCF → List CTLeak
  | s, .straight body => blockLeakCT r s body
  | s, .seq a b => mcfLeak r s a ++ mcfLeak r (mcfExec s a) b
  | s, .ifPub g t e =>
      if s.get g = 0 then .branch false :: mcfLeak r s e else .branch true :: mcfLeak r s t
  | s, .loop n body => iterLeak (fun s' => mcfLeak r s' body) (fun s' => mcfExec s' body) n s
  | s, .loopRt g body =>
      .trip (s.get g).toNat ::
        iterLeak (fun s' => mcfLeak r s' body) (fun s' => mcfExec s' body) (s.get g).toNat s

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

/-- The source fragment. `ctr` names the machine counter register of a loop,
    `lo` the machine register receiving the discarded low word of `MULX`, and
    `tmps` the temporaries of a word expression. -/
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

/-- The machine registers outside the image of `ρ` that the lowering writes:
    loop counters, `MULX` low words, and the tower registers of select and load
    destinations. -/
def CFSrc.writes (τ : RegMap) : CFSrc → List String
  | .skip | .arith _ | .setLit .. | .shift .. | .arrStore .. => []
  | .expr _ _ ts => ts
  | .letU64 _ body => body.writes τ
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
    a loop counter is not written by the loop body. -/
def CFSrc.WF (ρ τ : RegMap) : CFSrc → Prop
  | .skip | .setLit .. | .shift .. | .arrStore .. => True
  | .arith p => p.b ≠ p.dst
  | .expr _ e ts => (∀ v, ∀ t ∈ ts, ρ v ≠ t) ∧ ts.Nodup ∧ e.depth ≤ ts.length
  | .letU64 _ body => body.WF ρ τ
  | .mulHi _ _ _ lo => ∀ v, ρ v ≠ lo
  | .select dst .. => ∀ v, ρ v ≠ τ dst.locVar
  | .arrLoad dst .. => ∀ v, ρ v ≠ τ dst.locVar
  | .seq a b => a.WF ρ τ ∧ b.WF ρ τ
  | .ifNz _ t e => t.WF ρ τ ∧ e.WF ρ τ
  | .forLit _ ctr _ body | .forRt _ ctr _ body =>
      (∀ v, ρ v ≠ ctr) ∧ ctr ∉ body.writes τ ∧ body.WF ρ τ

/-- Whether a program accesses no tower: no select and no array access. -/
def CFSrc.towerFree : CFSrc → Bool
  | .select .. | .arrLoad .. | .arrStore .. => false
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

/-- The scalar post-state of the source. -/
def srcDen : CFSrc → Env → Env
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

/-- The source trace under `LowCTLeakModel.owned`. -/
def srcLeak : CFSrc → Env → List CTLeak
  | .skip, _ | .arith _, _ | .setLit .., _ | .expr .., _ | .mulHi .., _ | .select .., _ => []
  | .letU64 x body, σ => srcLeak body (setS σ x 0)
  | .shift k _ a c, σ => k.leak (σ a) (σ c)
  | .arrLoad _ src idx, σ => [.addr src.locVar (σ idx)]
  | .arrStore arr idx _, σ => [.addr arr.locVar (σ idx)]
  | .seq a b, σ => srcLeak a σ ++ srcLeak b (srcDen a σ)
  | .ifNz g t e, σ =>
      if σ g = 0 then .branch false :: srcLeak e σ else .branch true :: srcLeak t σ
  | .forLit x _ n body, σ => iterTrace x (srcDen body) (srcLeak body) n 0 σ
  | .forRt x _ bnd body, σ =>
      .trip (σ bnd) :: iterTrace x (srcDen body) (srcLeak body) (σ bnd) 0 σ

/-- The range conditions of a run: guards, indices and loop bounds below `2^64`,
    shifted values below `2^64` and shift counts below `64`. -/
def InRange : CFSrc → Env → Prop
  | .skip, _ | .arith _, _ | .setLit .., _ | .expr .., _ | .mulHi .., _ | .select .., _ => True
  | .letU64 x body, σ => InRange body (setS σ x 0)
  | .shift _ _ a c, σ => σ a < 2 ^ 64 ∧ σ c < 64
  | .arrLoad _ _ idx, σ => σ idx < 2 ^ 64
  | .arrStore _ idx _, σ => σ idx < 2 ^ 64
  | .seq a b, σ => InRange a σ ∧ InRange b (srcDen a σ)
  | .ifNz g t e, σ => σ g < 2 ^ 64 ∧ (if σ g = 0 then InRange e σ else InRange t σ)
  | .forLit x _ n body, σ => iterAll x (srcDen body) (InRange body) n 0 σ
  | .forRt x _ bnd body, σ => σ bnd < 2 ^ 64 ∧ iterAll x (srcDen body) (InRange body) (σ bnd) 0 σ

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
  | .ifNz .., h, _ | .forRt .., h, _ => by simp [CFSrc.rangeFree] at h

theorem towerFree_of_rangeFree : ∀ (c : CFSrc), c.rangeFree = true → c.towerFree = true
  | .skip, _ | .arith _, _ | .setLit .., _ | .expr .., _ | .mulHi .., _ => rfl
  | .letU64 _ body, h => towerFree_of_rangeFree body h
  | .seq a b, h => by
    simp only [CFSrc.rangeFree, Bool.and_eq_true] at h
    simp only [CFSrc.towerFree, towerFree_of_rangeFree a h.1, towerFree_of_rangeFree b h.2,
      Bool.and_self]
  | .forLit _ _ _ body, h => towerFree_of_rangeFree body h
  | .shift .., h | .select .., h | .arrLoad .., h | .arrStore .., h
  | .ifNz .., h | .forRt .., h => by simp [CFSrc.rangeFree] at h

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

/-- Every run of `RFor x n body` has the iterated trace and scalar post-state,
    given that every run of `body` has the trace and post-state of the source. -/
theorem forRun_det (N : Nat) (leafSpec : LeafSpec) (x : String) (body : CFSrc)
    (hb : ∀ rs t rs', RustExecLeak N leafSpec .owned body.toLowCT rs t rs' →
      t = srcLeak body rs.rsScalar ∧ rs'.rsScalar = srcDen body rs.rsScalar) :
    ∀ (n : Nat) (rs : RustState) (t : List CTLeak) (rs' : RustState),
      RustExecLeak N leafSpec .owned (.RFor x n body.toLowCT) rs t rs' →
      t = iterTrace x (srcDen body) (srcLeak body) n 0 rs.rsScalar ∧
        rs'.rsScalar = iterDen x (srcDen body) n 0 rs.rsScalar := by
  intro n
  induction n with
  | zero => intro rs t rs' h; cases h; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro rs t rs' h
    cases h with
    | forSucc _ _ _ _ r1 _ t1 t2 h1 h2 =>
      obtain ⟨rfl, hr1⟩ := ih rs t1 r1 h1
      obtain ⟨rfl, hr'⟩ := hb _ t2 rs' h2
      rw [rsSetScalar_rsScalar, hr1] at hr' ⊢
      rw [iterDen_succ, iterTrace_succ, Nat.zero_add]
      exact ⟨rfl, hr'⟩

/-- Every run of `c.toLowCT` has the trace `srcLeak c` and the scalar post-state
    `srcDen c` of its scalar entry state. -/
theorem srcRun_det (N : Nat) (leafSpec : LeafSpec) :
    ∀ (c : CFSrc) (rs : RustState) (t : List CTLeak) (rs' : RustState),
      RustExecLeak N leafSpec .owned c.toLowCT rs t rs' →
      t = srcLeak c rs.rsScalar ∧ rs'.rsScalar = srcDen c rs.rsScalar
  | .skip, rs, t, rs', h => by cases h; exact ⟨rfl, rfl⟩
  | .arith p, rs, t, rs', h => by
    cases h
    refine ⟨sexprLeak_arith p rs, ?_⟩
    rw [rsSetScalar_rsScalar, SExpr.evalState_eq_eval rs _ (arith_limbFree p)]
    rfl
  | .setLit d n, rs, t, rs', h => by cases h; exact ⟨rfl, rfl⟩
  | .expr d e ts, rs, t, rs', h => by
    cases h
    refine ⟨WExpr.sexprLeak_nil rs e, ?_⟩
    rw [rsSetScalar_rsScalar, SExpr.evalState_eq_eval rs _ (WExpr.limbFree e)]
    rfl
  | .letU64 x body, rs, t, rs', h => by
    cases h with
    | letU64Zero _ _ _ _ _ hb => exact srcRun_det N leafSpec body _ t rs' hb
  | .shift k d a c, rs, t, rs', h => by
    cases h
    exact ⟨sexprLeak_shift k a c rs, by rw [rsSetScalar_rsScalar, evalState_shift]; rfl⟩
  | .mulHi d a b lo, rs, t, rs', h => by cases h; exact ⟨rfl, rfl⟩
  | .select dst sel s0 s1, rs, t, rs', h => by cases h <;> exact ⟨rfl, rfl⟩
  | .arrLoad dst src idx, rs, t, rs', h => by
    cases h with
    | arrLoad _ _ _ _ i _ _ hi _ _ => subst hi; exact ⟨rfl, rfl⟩
  | .arrStore arr idx src, rs, t, rs', h => by
    cases h with
    | arrStore _ _ _ _ i _ _ hi _ _ => subst hi; exact ⟨rfl, rfl⟩
  | .seq a b, rs, t, rs', h => by
    cases h with
    | seq _ _ _ r1 _ t1 t2 h1 h2 =>
      obtain ⟨rfl, hr1⟩ := srcRun_det N leafSpec a rs t1 r1 h1
      obtain ⟨rfl, hr'⟩ := srcRun_det N leafSpec b _ t2 rs' h2
      rw [hr1] at hr' ⊢
      exact ⟨rfl, hr'⟩
  | .ifNz g th el, rs, t, rs', h => by
    cases h with
    | ifTrue _ _ _ _ _ v tr hv hv0 hb =>
      obtain ⟨rfl, hr⟩ := srcRun_det N leafSpec th rs tr rs' hb
      have hz : ¬ rs.rsScalar g = 0 := hv ▸ hv0
      simp only [srcLeak, srcDen, if_neg hz]
      exact ⟨trivial, hr⟩
    | ifFalse _ _ _ _ _ tr hv hb =>
      obtain ⟨rfl, hr⟩ := srcRun_det N leafSpec el rs tr rs' hb
      simp only [srcLeak, srcDen, if_pos hv]
      exact ⟨trivial, hr⟩
  | .forLit x ctr n body, rs, t, rs', h =>
    forRun_det N leafSpec x body (srcRun_det N leafSpec body) n rs t rs' h
  | .forRt x ctr bnd body, rs, t, rs', h => by
    cases h with
    | forRuntime _ _ _ _ _ tr hr =>
      obtain ⟨rfl, hr'⟩ := forRun_det N leafSpec x body (srcRun_det N leafSpec body) _ rs tr rs' hr
      exact ⟨rfl, hr'⟩

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
  | .select .., h, _ | .arrLoad .., h, _ | .arrStore .., h, _ => by
    simp [CFSrc.towerFree] at h

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
  rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), Nat.mod_eq_of_lt hc,
    show min 64 c = c by omega, ← BitVec.toInt_sshiftRight, BitVec.ofInt_toInt]

theorem x86_SHRX_ofNat (a c : Nat) (ha : a < 2 ^ 64) (hc : c < 64) :
    x86_SHRX (BitVec.ofNat 64 a) (BitVec.ofNat 64 c) = BitVec.ofNat 64 (a >>> c) := by
  simp only [x86_SHRX, wshr, shiftCount, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), Nat.mod_eq_of_lt hc,
    show min 64 c = c by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) ha)]

theorem x86_SHLX_ofNat (a c : Nat) (hc : c < 64) :
    x86_SHLX (BitVec.ofNat 64 a) (BitVec.ofNat 64 c) = BitVec.ofNat 64 (a <<< c) := by
  simp only [x86_SHLX, wshl, shiftCount, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), Nat.mod_eq_of_lt hc,
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

/-! ### 4.3 Preservation of registers outside the image of `ρ` -/

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
  rw [evalInstr_add_imm_get, if_neg hc, hB, evalInstr_mov_reg, JState.get_setReg_other _ _ _ _ hx]

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
    rw [evalInstr_mulx_get, if_neg (fun h' => hr d h'.symm), if_neg h]
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

/-! ### 4.4 The simulation and the leak transformer -/

/-- The scalar state relation: register `ρ v` holds the truncation of `σ v`.
    `StateMatch ρ rs js` is `SMatch ρ rs.rsScalar js`. -/
def SMatch (ρ : RegMap) (σ : Env) (js : JState 64) : Prop :=
  ∀ v, js.get (ρ v) = BitVec.ofNat 64 (σ v)

/-- The leak transformer: a source element access `addr a i` is the machine
    access at byte offset `8 * i` from the base register `τ a`; every other event
    is unchanged. -/
def leakXf (τ : RegMap) : CTLeak → CTLeak
  | .addr a off => .addr (τ a) (8 * off)
  | e => e

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
theorem loop_sim (ρ τ : RegMap) (hρ : Function.Injective ρ) (x ctr : String) (body : CFSrc)
    (hctrρ : ∀ v, ρ v ≠ ctr)
    (ih : ∀ σ js, SMatch ρ σ js → InRange body σ →
      SMatch ρ (srcDen body σ) (mcfExec js (lowerCF ρ τ body)) ∧
        mcfLeak .doitm js (lowerCF ρ τ body) = (srcLeak body σ).map (leakXf τ))
    (hpres : ∀ s, (mcfExec s (lowerCF ρ τ body)).get ctr = s.get ctr) :
    ∀ (k i : Nat) (σ : Env) (js : JState 64), SMatch ρ σ js → js.get ctr = BitVec.ofNat 64 i →
      iterAll x (srcDen body) (InRange body) k i σ →
      SMatch ρ (iterDen x (srcDen body) k i σ)
          ((fun s => mcfExec s (loopBody ρ x ctr (lowerCF ρ τ body)))^[k] js) ∧
        iterLeak (fun s => mcfLeak .doitm s (loopBody ρ x ctr (lowerCF ρ τ body)))
            (fun s => mcfExec s (loopBody ρ x ctr (lowerCF ρ τ body))) k js =
          (iterTrace x (srcDen body) (srcLeak body) k i σ).map (leakXf τ) := by
  set B := loopBody ρ x ctr (lowerCF ρ τ body) with hB
  have hstep : ∀ (i : Nat) σ js, SMatch ρ σ js → js.get ctr = BitVec.ofNat 64 i →
      InRange body (setS σ x i) →
      SMatch ρ (srcDen body (setS σ x i)) (mcfExec js B) ∧
        (mcfExec js B).get ctr = BitVec.ofNat 64 (i + 1) ∧
        mcfLeak .doitm js B = (srcLeak body (setS σ x i)).map (leakXf τ) := by
    intro i σ js hm hc hinb
    have hm1 : SMatch ρ (setS σ x i) (evalInstr js (.mov (ρ x) (.reg ctr))) := by
      refine SMatch.setS ρ σ js hm x i _ ?_ ?_
      · rw [evalInstr_mov_reg, JState.get_setReg_same, hc]
      · intro u hu
        rw [evalInstr_mov_reg, JState.get_setReg_other _ _ _ _ (fun h => hu (hρ h))]
    have hc1 : (evalInstr js (.mov (ρ x) (.reg ctr))).get ctr = BitVec.ofNat 64 i := by
      rw [evalInstr_mov_reg, JState.get_setReg_other _ _ _ _ (fun h => hctrρ x h.symm), hc]
    obtain ⟨hmb, hlb⟩ := ih _ _ hm1 hinb
    refine ⟨?_, ?_, ?_⟩
    · rw [hB]
      simp only [loopBody, mcfExec, runBlock_cons, runBlock_nil]
      intro v
      rw [evalInstr_add_imm_get, if_neg (hctrρ v)]
      exact hmb v
    · rw [hB]
      simp only [loopBody, mcfExec, runBlock_cons, runBlock_nil]
      rw [evalInstr_add_imm_get, if_pos rfl, hpres, hc1]
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
    · rw [iterLeak, iterTrace, hl', hlk, List.map_append]

/-- The simulation and the leak transformer: from states related by `SMatch ρ`,
    the machine post-state of the lowering is related to the source post-state,
    and the machine trace is the source trace mapped by `leakXf τ`. -/
theorem lowerCF_sim (ρ τ : RegMap) (hρ : Function.Injective ρ) :
    ∀ (c : CFSrc), c.WF ρ τ → ∀ σ js, SMatch ρ σ js → InRange c σ →
      SMatch ρ (srcDen c σ) (mcfExec js (lowerCF ρ τ c)) ∧
        mcfLeak .doitm js (lowerCF ρ τ c) = (srcLeak c σ).map (leakXf τ)
  | .skip, _, σ, js, hm, _ => ⟨hm, rfl⟩
  | .arith p, hwf, σ, js, hm, _ => by
    refine ⟨?_, ?_⟩
    · exact lowerArith_denote ρ p { rsTower := fun _ => none, rsScalar := σ } js hρ hwf hm
    · rw [lowerCF, mcfLeak, blockLeakCT_lowerArith]; rfl
  | .setLit d n, _, σ, js, hm, _ => by
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]
      refine SMatch.setS ρ σ js hm d _ _ ?_ ?_
      · rw [evalInstr_movImm, JState.get_setReg_same]
      · intro u hu
        rw [evalInstr_movImm, JState.get_setReg_other _ _ _ _ (fun h => hu (hρ h))]
    · rfl
  | .expr d e ts, hwf, σ, js, hm, _ => by
    obtain ⟨hρt, hnd, hdep⟩ := hwf
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, srcDen]
      rw [runBlock_append, runBlock_cons, runBlock_nil]
      refine SMatch.setS ρ σ js hm d _ _ ?_ ?_
      · rw [evalInstr_mov_reg, JState.get_setReg_same]
        exact lowerW_val ρ σ e ts js (ρ d) hm hρt hnd hdep
      · intro u hu
        rw [evalInstr_mov_reg, JState.get_setReg_other _ _ _ _ (fun h => hu (hρ h)),
          lowerW_get_other ρ e ts js (ρ u) (fun h => hρt u _ h rfl)]
    · simp only [lowerCF, mcfLeak, srcLeak, List.map_nil]
      rw [blockLeakCT_append, blockLeakCT_lowerW]
      rfl
  | .letU64 x body, hwf, σ, js, hm, hin => by
    have hm0 : SMatch ρ (setS σ x 0) (evalInstr js (movImm (ρ x) 0)) := by
      refine SMatch.setS ρ σ js hm x 0 _ ?_ ?_
      · rw [evalInstr_movImm, JState.get_setReg_same]
      · intro u hu
        rw [evalInstr_movImm, JState.get_setReg_other _ _ _ _ (fun h => hu (hρ h))]
    obtain ⟨hmb, hlb⟩ := lowerCF_sim ρ τ hρ body hwf _ _ hm0 hin
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]; exact hmb
    · simp only [lowerCF, mcfLeak, mcfExec, runBlock_cons, runBlock_nil, srcLeak]
      rw [hlb]
      rfl
  | .shift k d a c, _, σ, js, hm, hin => by
    obtain ⟨ha, hc⟩ := hin
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]
      refine SMatch.setS ρ σ js hm d _ _ ?_ ?_
      · rw [evalInstr_shift, JState.get_setReg_same, hm a, hm c,
          ShiftKind.x86_ofNat k _ _ ha hc]
      · intro u hu
        rw [evalInstr_shift, JState.get_setReg_other _ _ _ _ (fun h => hu (hρ h))]
    · rw [lowerCF, mcfLeak, blockLeakCT_shift, toNat_of_match ρ σ js hm a ha,
        toNat_of_match ρ σ js hm c (by omega), srcLeak]
      cases k <;> rfl
  | .mulHi d a b lo, hwf, σ, js, hm, _ => by
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]
      refine SMatch.setS ρ σ js hm d _ _ ?_ ?_
      · rw [evalInstr_mulx_get, if_pos rfl]
        simp only [JOperand.eval]
        rw [hm a, hm b, x86_MULX_hi_ofNat]
      · intro u hu
        rw [evalInstr_mulx_get, if_neg (fun h => hu (hρ h)), if_neg (hwf u)]
    · rw [lowerCF, mcfLeak, blockLeakCT_mulx]; rfl
  | .select dst sel s0 s1, hwf, σ, js, hm, _ => by
    refine ⟨?_, ?_⟩
    · intro v
      simp only [lowerCF, mcfExec, srcDen]
      rw [lowerSelect_get ρ τ dst sel s0 s1 js _ (hwf v)]
      exact hm v
    · rw [lowerCF, mcfLeak, blockLeakCT_lowerSelect]; rfl
  | .arrLoad dst src idx, hwf, σ, js, hm, hin => by
    refine ⟨?_, ?_⟩
    · intro v
      simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen, evalInstr]
      rw [JState.get_setReg_other _ _ _ _ (hwf v)]
      exact hm v
    · simp only [lowerCF, mcfLeak, blockLeakCT_cons, blockLeakCT_nil, instrLeakCT, instrLeak,
        srcLeak, toNat_of_match ρ σ js hm idx hin]
      simp [JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing, mleakToCT, leakXf]
  | .arrStore arr idx src, _, σ, js, hm, hin => by
    refine ⟨?_, ?_⟩
    · intro v
      simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]
      simp only [evalInstr, JState.storeIdx, JState.store]
      exact hm v
    · simp only [lowerCF, mcfLeak, blockLeakCT_cons, blockLeakCT_nil, instrLeakCT, instrLeak,
        srcLeak, toNat_of_match ρ σ js hm idx hin]
      simp [JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing, mleakToCT, leakXf]
  | .seq a b, hwf, σ, js, hm, hin => by
    obtain ⟨hma, hla⟩ := lowerCF_sim ρ τ hρ a hwf.1 σ js hm hin.1
    obtain ⟨hmb, hlb⟩ := lowerCF_sim ρ τ hρ b hwf.2 _ _ hma hin.2
    refine ⟨hmb, ?_⟩
    rw [lowerCF, mcfLeak, hla, hlb, srcLeak, List.map_append]
  | .ifNz g t e, hwf, σ, js, hm, hin => by
    obtain ⟨hlt, hin'⟩ := hin
    have hg : js.get (ρ g) = 0 ↔ σ g = 0 := by
      rw [hm g]; exact ofNat_eq_zero_iff_of_lt _ hlt
    by_cases hz : σ g = 0
    · have hjz : js.get (ρ g) = 0 := hg.2 hz
      rw [if_pos hz] at hin'
      obtain ⟨hme, hle⟩ := lowerCF_sim ρ τ hρ e hwf.2 σ js hm hin'
      refine ⟨?_, ?_⟩
      · rw [lowerCF, mcfExec, if_pos hjz, srcDen, if_pos hz]; exact hme
      · rw [lowerCF, mcfLeak, if_pos hjz, srcLeak, if_pos hz, hle]; rfl
    · have hjz : ¬ js.get (ρ g) = 0 := fun h => hz (hg.1 h)
      rw [if_neg hz] at hin'
      obtain ⟨hmt, hlt'⟩ := lowerCF_sim ρ τ hρ t hwf.1 σ js hm hin'
      refine ⟨?_, ?_⟩
      · rw [lowerCF, mcfExec, if_neg hjz, srcDen, if_neg hz]; exact hmt
      · rw [lowerCF, mcfLeak, if_neg hjz, srcLeak, if_neg hz, hlt']; rfl
  | .forLit x ctr n body, hwf, σ, js, hm, hin => by
    obtain ⟨hctrρ, hctrb, hwfb⟩ := hwf
    have hloop := loop_sim ρ τ hρ x ctr body hctrρ (lowerCF_sim ρ τ hρ body hwfb)
      (lowerCF_preserves ρ τ ctr hctrρ body hctrb)
    have hm0 : SMatch ρ σ (evalInstr js (movImm ctr 0)) := by
      intro v
      rw [evalInstr_movImm, JState.get_setReg_other _ _ _ _ (hctrρ v)]
      exact hm v
    have hc0 : (evalInstr js (movImm ctr 0)).get ctr = BitVec.ofNat 64 0 := by
      rw [evalInstr_movImm, JState.get_setReg_same]
    obtain ⟨hmL, hlL⟩ := hloop n 0 σ _ hm0 hc0 hin
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]; exact hmL
    · simp only [lowerCF, mcfLeak, mcfExec, runBlock_cons, runBlock_nil, srcLeak]
      rw [hlL]
      simp [blockLeakCT, instrLeakCT, instrLeak, movImm, JInstr.mnem, DoitRegime.leaksOperands,
        X86Mnem.timing]
  | .forRt x ctr bnd body, hwf, σ, js, hm, hin => by
    obtain ⟨hctrρ, hctrb, hwfb⟩ := hwf
    obtain ⟨hbnd, hall⟩ := hin
    have hloop := loop_sim ρ τ hρ x ctr body hctrρ (lowerCF_sim ρ τ hρ body hwfb)
      (lowerCF_preserves ρ τ ctr hctrρ body hctrb)
    have hm0 : SMatch ρ σ (evalInstr js (movImm ctr 0)) := by
      intro v
      rw [evalInstr_movImm, JState.get_setReg_other _ _ _ _ (hctrρ v)]
      exact hm v
    have hc0 : (evalInstr js (movImm ctr 0)).get ctr = BitVec.ofNat 64 0 := by
      rw [evalInstr_movImm, JState.get_setReg_same]
    have hn : ((evalInstr js (movImm ctr 0)).get (ρ bnd)).toNat = σ bnd :=
      toNat_of_match ρ σ _ hm0 bnd hbnd
    obtain ⟨hmL, hlL⟩ := hloop (σ bnd) 0 σ _ hm0 hc0 hall
    refine ⟨?_, ?_⟩
    · simp only [lowerCF, mcfExec, runBlock_cons, runBlock_nil, srcDen]
      rw [hn]; exact hmL
    · simp only [lowerCF, mcfLeak, mcfExec, runBlock_cons, runBlock_nil, srcLeak]
      rw [hn, hlL]
      simp [blockLeakCT, instrLeakCT, instrLeak, movImm, JInstr.mnem, DoitRegime.leaksOperands,
        X86Mnem.timing, leakXf]

/-- The leak transformer: from states related by `SMatch ρ`, the machine trace of
    the lowering is the source trace mapped by `leakXf τ`. -/
theorem lowerCF_leak (ρ τ : RegMap) (hρ : Function.Injective ρ) (c : CFSrc) (hwf : c.WF ρ τ)
    (σ : Env) (js : JState 64) (hm : SMatch ρ σ js) (hin : InRange c σ) :
    mcfLeak .doitm js (lowerCF ρ τ c) = (srcLeak c σ).map (leakXf τ) :=
  (lowerCF_sim ρ τ hρ c hwf σ js hm hin).2

/-- The leak transformer for an arbitrary run: the machine trace is the trace `t`
    of any `RustExecLeak` run of the source program from a related state, mapped
    by `leakXf τ`. -/
theorem lowerCF_leak_of_run (N : Nat) (leafSpec : LeafSpec) (ρ τ : RegMap)
    (hρ : Function.Injective ρ) (c : CFSrc) (hwf : c.WF ρ τ)
    (rs rs' : RustState) (t : List CTLeak) (js : JState 64) (hm : StateMatch ρ rs js)
    (hin : InRange c rs.rsScalar) (hrun : RustExecLeak N leafSpec .owned c.toLowCT rs t rs') :
    mcfLeak .doitm js (lowerCF ρ τ c) = t.map (leakXf τ) := by
  rw [lowerCF_leak ρ τ hρ c hwf rs.rsScalar js hm hin, (srcRun_det N leafSpec c rs t rs' hrun).1]

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
  simp only
  rw [lowerCF_leak ρ τ hρ c hwf _ js₁ (liftEnv_match ρ js₁) h₁,
    lowerCF_leak ρ τ hρ c hwf _ js₂ (liftEnv_match ρ js₂) h₂]
  have e₁ : t₁ = srcLeak c (liftEnv ρ js₁) := (srcRun_det N leafSpec c _ t₁ r₁ run₁).1
  have e₂ : t₂ = srcLeak c (liftEnv ρ js₂) := (srcRun_det N leafSpec c _ t₂ r₂ run₂).1
  rw [← e₁, ← e₂, hsrc _ _ _ _ (liftState_pubEq ρ T lt pub hpub js₁ js₂ hag) ⟨_, run₁⟩ ⟨_, run₂⟩]

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

/-- The single arithmetic statement of `LowCTToJInstrCT.lowerArith_source_to_machine_CT`,
    with source constant time in the `CTP-1` model as the premise and machine
    constant time in the `CTP-1` model as the conclusion. -/
theorem lowerArith_source_to_machine_CT' (N : Nat) (leafSpec : LeafSpec) (lt : LevelTable)
    (pub : PubPred) (ρ : RegMap) (hρ : Function.Injective ρ) (p : ArithSrc) (hb : p.b ≠ p.dst)
    (hpub : ∀ x, lt x = .Public → pub (ρ x) = true)
    (hsrc : LowCTConstantTime N leafSpec .owned lt p.toLowCT) :
    MachineCT .doitm pub (lowerArith ρ p) := fun js₁ js₂ hag =>
  lowct_to_machine_ct_rangeFree N leafSpec lt pub ρ id hρ (.arith p) hb rfl hpub hsrc js₁ js₂ hag

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
    rw [dif_pos hl.symm]
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

/-- The machine names the recogniser assigns: the counter of a loop at nesting depth
    `k` is `ctr k`, the discarded low word of `MULX` is `lo`, and the temporaries of a
    word expression are `tmps`. -/
structure CFNames where
  tmps : List String
  ctr : Nat → String
  lo : String

/-- The statement `dst := e`: a shift by a scalar count, the high word of a wide
    multiply, or a word expression. -/
def stmtOf? (nm : CFNames) (d : String) : SExpr → Option CFSrc
  | .SShr (.SVar a) (.SVar c) => some (.shift .shr d a c)
  | .SShl (.SVar a) (.SVar c) => some (.shift .shl d a c)
  | .SAsr (.SVar a) (.SVar c) => some (.shift .sar d a c)
  | .SMulHiU (.SVar a) (.SVar b) => some (.mulHi d a b nm.lo)
  | e => (WExpr.ofSExpr? e).map fun w => .expr d w nm.tmps

theorem stmtOf?_spec (nm : CFNames) (d : String) (e : SExpr) (c : CFSrc)
    (h : stmtOf? nm d e = some c) : c.toLowCT = .RScalarSetExpr d e := by
  unfold stmtOf? at h
  split at h <;> simp only [Option.some.injEq, Option.map_eq_some_iff] at h
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

/-- The side conditions `CFSrc.WF` as a Boolean. -/
def wfB (A : RegAlloc) : CFSrc → Bool
  | .skip | .setLit .. | .shift .. | .arrStore .. => true
  | .arith p => p.b != p.dst
  | .expr _ e ts => ts.all (fun t => !A.inImg t) && decide ts.Nodup && decide (e.depth ≤ ts.length)
  | .letU64 _ b => wfB A b
  | .mulHi _ _ _ lo => !A.inImg lo
  | .select dst .. | .arrLoad dst .. => !A.inImg (A.τ dst.locVar)
  | .seq a b | .ifNz _ a b => wfB A a && wfB A b
  | .forLit _ ctr _ b | .forRt _ ctr _ b =>
      !A.inImg ctr && !((b.writes A.τ).contains ctr) && wfB A b

theorem wfB_spec (A : RegAlloc) : ∀ (c : CFSrc), wfB A c = true → c.WF A.ρ A.τ
  | .skip, _ | .setLit .., _ | .shift .., _ | .arrStore .., _ => trivial
  | .arith p, h => by simpa [wfB, CFSrc.WF] using h
  | .expr _ e ts, h => by
    simp only [wfB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    exact ⟨fun v t ht => A.ne_of_inImg (h.1.1 t ht) v, h.1.2, h.2⟩
  | .letU64 _ b, h => wfB_spec A b h
  | .mulHi _ _ _ lo, h => by
    simp only [wfB, Bool.not_eq_true'] at h
    exact A.ne_of_inImg h
  | .select dst .., h | .arrLoad dst .., h => by
    simp only [wfB, Bool.not_eq_true'] at h
    exact A.ne_of_inImg h
  | .seq a b, h | .ifNz _ a b, h => by
    simp only [wfB, Bool.and_eq_true] at h
    exact ⟨wfB_spec A a h.1, wfB_spec A b h.2⟩
  | .forLit _ ctr _ b, h | .forRt _ ctr _ b, h => by
    simp only [wfB, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨A.ne_of_inImg h.1.1, by simpa using h.1.2, wfB_spec A b h.2⟩

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
  | .shift .. | .forLit .. | .forRt .. => none

/-- The names `B` hold values below `2^64` in `σ`. -/
def BoundedBy (B : String → Bool) (σ : Env) : Prop := ∀ x, B x = true → σ x < 2 ^ 64

theorem BoundedBy.upd {B : String → Bool} {σ : Env} (h : BoundedBy B σ) (x : String)
    (b : Bool) (v : Nat) (hv : b = true → v < 2 ^ 64) : BoundedBy (updB B x b) (setS σ x v) := by
  intro y hy
  simp only [updB, setS] at hy ⊢
  split
  · rw [if_pos (by assumption)] at hy; exact hv hy
  · rw [if_neg (by assumption)] at hy; exact h y hy

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
  | .shift .., _, _, _, _, hr | .forLit .., _, _, _, _, hr | .forRt .., _, _, _, _, hr => by
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
    recognised program without tower access that passes `rangeB`, source constant
    time gives machine constant time of the lowering for all machine states agreeing
    on the public registers. -/
theorem machine_ct_of_lowct_closed (A : RegAlloc) (nm : CFNames) (lt : LevelTable)
    (pub : PubPred) (c : LowCT) (cf : CFSrc) (B' : String → Bool)
    (hrec : toCFSrc? nm 0 c = some cf) (hwf : wfB A cf = true) (htf : cf.towerFree = true)
    (hrange : rangeB (fun _ => true) cf = some B')
    (hpub : ∀ x, lt x = .Public → pub (A.ρ x) = true)
    (hsrc : LowCTConstantTime N leafSpec .owned lt c) :
    ConstantTime (fun js₁ js₂ : JState 64 => agreePub pub js₁ js₂)
      (fun js => mcfLeak .doitm js (lowerCF A.ρ A.τ cf)) := by
  have hc := toCFSrc?_spec nm 0 c cf hrec
  subst hc
  intro js₁ js₂ hag
  exact lowct_to_machine_ct_towerFree N leafSpec lt pub A.ρ A.τ A.inj cf (wfB_spec A cf hwf) htf
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

/-- The recognised program when it satisfies the decided side conditions, has no
    tower access and passes `rangeB`. -/
def toCFSrcClosed? (A : RegAlloc) (nm : CFNames) (c : LowCT) : Option CFSrc :=
  (toCFSrc? nm 0 c).filter fun cf =>
    wfB A cf && cf.towerFree && (rangeB (fun _ => true) cf).isSome

theorem toCFSrcClosed?_spec {A : RegAlloc} {nm : CFNames} {c : LowCT} {cf : CFSrc}
    (h : toCFSrcClosed? A nm c = some cf) :
    toCFSrc? nm 0 c = some cf ∧ wfB A cf = true ∧ cf.towerFree = true ∧
      ∃ B', rangeB (fun _ => true) cf = some B' := by
  simp only [toCFSrcClosed?, Option.filter_eq_some_iff, Bool.and_eq_true,
    Option.isSome_iff_exists] at h
  exact ⟨h.1, h.2.1.1, h.2.1.2, h.2.2⟩

/-- **The decision.** `c` is accepted by `levelCheck` from `lt`, is recognised, and
    its recognised program satisfies the decided side conditions, has no tower
    access and passes `rangeB`. -/
def machineCTCheck (A : RegAlloc) (nm : CFNames) (lt : LevelTable) (c : LowCT) : Bool :=
  (levelCheck .owned lt c).isSome && (toCFSrcClosed? A nm c).isSome

/-- **Soundness of the decision.** An accepted program is recognised as a program
    whose lowering is constant time for every pair of machine states agreeing on the
    public registers. The leaf specification is arbitrary: the program has no leaf
    call. -/
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

/-- Eight temporaries, the loop counter `c` followed by the depth, and the `MULX` low
    word `lo`; none starts with `s`. -/
def stdNames : CFNames where
  tmps := ["w0", "w1", "w2", "w3", "w4", "w5", "w6", "w7"]
  ctr k := "c" ++ toString k
  lo := "lo"

/-- The public registers of `lt` under `stdAlloc`: `s` followed by a public name. -/
def stdPub (lt : LevelTable) : PubPred := fun r =>
  match r.toList with
  | 's' :: v => lt (String.ofList v) == .Public
  | _ => false

theorem stdPub_spec (lt : LevelTable) (x : String) (hx : lt x = .Public) :
    stdPub lt (stdAlloc.ρ x) = true := by
  simp [stdPub, stdAlloc, prefixed_toList, hx]
  rfl

end CatCrypt.Crypto.SecureCompilation.CT.LowCTMachine
