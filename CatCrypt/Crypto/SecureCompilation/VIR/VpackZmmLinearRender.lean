/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmm
public import CatCrypt.Crypto.SecureCompilation.VIR.ComRange
public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel
public import CatCryptCore.Tactics.KatGuard
public import Std.Data.HashMap
public meta import CatCrypt.Crypto.SecureCompilation.VIR.RodataPool
public import CatCrypt.Crypto.SecureCompilation.VIR.RodataPool
public meta import CatCrypt.Crypto.Optimizer.GenericRegAlloc
public import CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-!
# Linear-time owned `%zmm` rendering of a large packed program

`VpackZmmAsmPrint.renderVpackZmmComAutoZmm` renders a `vpackZMM` `Com` through
`VsimdAsmPrint.vsimdAutoAllocZmm`, whose linear scan recomputes each value's last use
by scanning the block and looks registers up in an association list: quadratic in the
number of bindings. It pins every parameter to a register and has no arm for
constants.

This module renders a straight-line `Com jasminDialect` whose bindings are packed
operations on eight 64-bit lanes (`vpackZMM`) or sixteen 32-bit lanes (`vpackZMMd`),
the sixteen-lane high multiply `extCall "zmm_mulhi32x16"`, and 512-bit constants, in
time linear in the binding count, apart from the name lookups of `JasminPrint.VarMap`,
which cost the de Bruijn distance of the variable read. It also renders the lane-wise
widening of a scalar program read off the scalar program in one pass
(`renderLaneMapZmmFunction` for 64-bit words, `renderLaneMapZmmDFunction` for 32-bit
words). The last-use table and the register map are hash maps. Constants take no
register: each distinct value is one `.rodata` entry (an 8-byte word when its eight
64-bit lanes are equal, else 64 bytes), read as a memory operand of the operation that
uses it (`c(%rip){1to8}` or `{1to16}` for a broadcast), a shift by a broadcast constant
below the lane width uses the immediate-count form, and a constant first operand of a
non-commutative operation is resident in a register loaded at entry or loaded into the
scratch register `%zmm31`. The high multiply renders as `vpmuludq` on the even lanes and
on the odd lanes duplicated down by `vmovshdup`, the even high words merged by a
`vmovshdup` under the mask `%k2`, over the temporaries `%zmm28..30`; a low half
and a high half of the same product share one pair of `vpmuludq` (`fuseMulHiLo`). The
Montgomery step `mulhi(a, b) - mulhi((a·b)·mu, p)` with `mu·p ≡ 1 (mod 2^32)` stays in the
even/odd 64-bit products until one final merge (`fuseMontSub`, `montSubLines`): six
`vpmuludq`, two `vpsubq` and two `vmovshdup` (three when `b` is not a broadcast), with no
`vpmulld` and no low-half merge. A rotate written as two immediate shifts and a
disjunction renders as one `vprolq` / `vprold` (`fuseRol`); a three-input exclusive or
and the Keccak χ step `x ⊕ (¬y ∧ z)` render as one `vpternlogq` / `vpternlogd`
(`fuseTern`). Its destination takes the register of an operand read for the last time
there when there is one (`allocZmmLinear`), and is otherwise loaded from the first
operand by a `vmovdqa64`.

The function frame follows the two-pointer SysV ABI `f(out = %rdi, in = %rsi)`:
parameter `s` (head first) is loaded from `inOffset s(%rsi)`, and the `nOut` last
bindings are stored to `64·j(%rdi)` in binding order, the output convention of
`JasminLprogExport.outStoreSlots`.
When the parameters and live values fit in the registers, parameter `s` is pinned to
register `s` and loaded at entry (`allocZmmLinear`). Otherwise the allocation is
`GenericRegAlloc.nextUseAlloc` (`allocZmmSpill`): a parameter is loaded from the input
region before its first read and again after an eviction, and a live value evicted from
its register is stored to a slot of a stack frame of `stride`-byte slots, allocated by
`subq`/`addq` of `%rsp` around the body, and loaded back before its next read.
With `ymm` the same text is printed on the 256-bit registers, four 64-bit lanes per
value: register names (`vecReg`) and broadcast counts (`constOperand`) are taken from the
register mode `ZmmTextModel.Mode` the validator's machine model reads.

The fast selections (`vpmuludq` for a 64-bit multiply, an unsigned minimum for a
conditional add or subtract) are valid only on part of the lane range. The caller states
a bound on the inputs of the scalar program, and the verified analysis
`ComRange.rangeAnalysis` (`rangeAnalysis_sound`) bounds every binding from it; each
selection is taken only where those bounds meet the precondition of its selection lemma in
`RangeDomain` (`mul_eq_mul_setWidth32`, `condAdd_eq_umin`, `condAdd_sub_eq_umin`). The
renderer itself is not verified: that the text it prints computes those lemmas' left-hand
sides is the job of a translation validator.

## Main definitions

* `ZBind`, `collectZBinds`, `collectZBindsScalar`: the straight-line binding list.
* `csubToMinu`: the conditional add or subtract of a constant as an unsigned minimum.
* `fuseMulHiLo`, `fuseMontSub`: the fused high/low product and the fused Montgomery step.
* `RangeInfo`, `rangeInfoOf`: the range facts, taken from `ComRange.rangeAnalysis`.
* `allocZmmLinear`: the linear-scan allocation, failing when no register is free.
* `allocZmmSpill`: the allocation with spilling, through `GenericRegAlloc.nextUseAlloc`.
* `renderZmmLinearFunction`, `renderLaneMapZmmFunction`, `renderLaneMapZmmDFunction`:
  the owned AT&T function text.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmLinearRender

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (VarMap argName paramsAndMap)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode ternTable xor3B chiB)
open CatCrypt.Crypto.SecureCompilation.VIR.RodataPool (Pool qwordsLE leValue leValue_qwordsLE)

/-! ## 1. The binding list -/

/-- The lane width of a packed binding: eight 64-bit lanes or sixteen 32-bit lanes. -/
inductive LaneW where
  | q
  | d
deriving DecidableEq, BEq

/-- The number of bits of one lane. -/
def LaneW.bits : LaneW → Nat
  | .q => 64
  | .d => 32

/-- One binding of a straight-line packed program: a lane-wise operation, the
    sixteen-lane high multiply, a 512-bit constant, an unsigned lane-wise minimum, the
    fused products of the renderer's passes, or any other operation (which the renderer
    rejects). `montsub d a b mu p` is the sixteen-lane Montgomery difference
    `d = mulhi(a, b) - mulhi((a·b)·mu, p)` of the constants `mu`, `p`. `rol w d a n` is the
    lane-wise rotate of `a` left by `n`, and `tern w imm d a b c` the bitwise function of
    truth table `imm` (`ZmmTextModel.semTern`) of `a`, `b`, `c`. `shi w left d a n` is the
    lane-wise shift of `a` by the immediate `n`, left when `left` holds and logical right
    otherwise (`ZmmTextModel.semShImm`). -/
inductive ZBind where
  | pack (w : LaneW) (bop : JasminBinOp) (dst a b : String)
  | mulhi (dst a b : String)
  | const (dst : String) (v : Nat)
  | minu (w : LaneW) (dst a b : String)
  | deferred (dst a b : String)
  | mulhilo (hi lo a b : String)
  | montsub (dst a b mu p : String)
  | other (dst : String)
  | rol (w : LaneW) (dst a : String) (n : Nat)
  | tern (w : LaneW) (imm : Nat) (dst a b c : String)
  | shi (w : LaneW) (left : Bool) (dst a : String) (n : Nat)

/-- The name a binding defines. -/
def ZBind.dst : ZBind → String
  | .pack _ _ d _ _ => d
  | .mulhi d _ _ => d
  | .const d _ => d
  | .minu _ d _ _ => d
  | .deferred d _ _ => d
  | .mulhilo h _ _ _ => h
  | .montsub d _ _ _ _ => d
  | .other d => d
  | .rol _ d _ _ => d
  | .tern _ _ d _ _ _ => d
  | .shi _ _ d _ _ => d

/-- Whether a binding lies outside the renderer's fragment. -/
def ZBind.isOther : ZBind → Bool
  | .other _ => true
  | _ => false

/-- The names a binding reads. -/
def ZBind.srcs : ZBind → List String
  | .pack _ _ _ a b => [a, b]
  | .mulhi _ a b => [a, b]
  | .minu _ _ a b => [a, b]
  | .deferred _ a b => [a, b]
  | .mulhilo _ _ a b => [a, b]
  | .montsub _ a b _ _ => [a, b]
  | .rol _ _ a _ => [a]
  | .tern _ _ _ a b c => [a, b, c]
  | .shi _ _ _ a _ => [a]
  | _ => []

/-- The name of the sixteen-lane high-multiply leaf. -/
def mulhiLeafName : String := "zmm_mulhi32x16"

/-- The binding of expression `e` of a packed program defining `dst`. -/
def exprZBind {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (vm : VarMap Γ)
    (e : Expr jasminDialect Γ t) (dst : String) : ZBind :=
  match e.op with
  | .vpackZMM bop => .pack .q bop dst (argName vm e.args 0) (argName vm e.args 1)
  | .vpackZMMd bop => .pack .d bop dst (argName vm e.args 0) (argName vm e.args 1)
  | .extCall name _ _ =>
      if name = mulhiLeafName then .mulhi dst (argName vm e.args 0) (argName vm e.args 1)
      else .other dst
  | .regConst w n => if w = 512 then .const dst n else .other dst
  | _ => .other dst

/-- The eight-fold broadcast of a 64-bit word to 512 bits. -/
def bcast512 (w : Nat) : Nat :=
  (List.range 8).foldl (fun acc k => acc + (w % 2 ^ 64) * 2 ^ (64 * k)) 0

/-- The sixteen-fold broadcast of a 32-bit word to 512 bits. -/
def bcast512d (w : Nat) : Nat :=
  (List.range 16).foldl (fun acc k => acc + (w % 2 ^ 32) * 2 ^ (32 * k)) 0

/-- The binding the 64-bit lane map `LaneMapZmm.laneMapZmm` gives the scalar
    expression `e` defining `dst`: `regArith bop 64` is `vpackZMM bop`, `regConst 64 k`
    is the broadcast constant `constZmm k`, `shlImm 64 n` and `shrImm 64 n` with `n < 64`
    are the immediate shifts by `n`, and every other operation is outside the fragment. -/
def exprZBindScalar {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (vm : VarMap Γ)
    (e : Expr jasminDialect Γ t) (dst : String) : ZBind :=
  match e.op with
  | .regArith bop w =>
      if w = 64 then .pack .q bop dst (argName vm e.args 0) (argName vm e.args 1)
      else .other dst
  | .regConst w k =>
      if w = 64 then .const dst (KeccakThetaPiAbstractCom.constZmm k).toNat else .other dst
  | .shlImm w n =>
      if w = 64 ∧ n < 64 then .shi .q true dst (argName vm e.args 0) n else .other dst
  | .shrImm w n =>
      if w = 64 ∧ n < 64 then .shi .q false dst (argName vm e.args 0) n else .other dst
  | _ => .other dst

/-- The binding the 32-bit lane map `LaneMapZmmD` gives the scalar expression `e`
    defining `dst`: `regArith bop 32` is `vpackZMMd bop`, `mulhi 32` is the high-multiply
    leaf, `regConst 32 k` is the sixteen-fold broadcast of `k`, and every other operation
    is outside the fragment. -/
def exprZBindScalar32 {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (vm : VarMap Γ)
    (e : Expr jasminDialect Γ t) (dst : String) : ZBind :=
  match e.op with
  | .regArith bop w =>
      if w = 32 then .pack .d bop dst (argName vm e.args 0) (argName vm e.args 1)
      else .other dst
  | .mulhi w =>
      if w = 32 then .mulhi dst (argName vm e.args 0) (argName vm e.args 1) else .other dst
  | .regConst w k => if w = 32 then .const dst (bcast512d k) else .other dst
  | _ => .other dst

/-- The bindings of a straight-line `Com` in order under the binding map `f`, with fresh
    names `v{next}`, and the name of its return value. Tail-recursive in the
    accumulator. -/
def collectWith
    (f : ∀ {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}, VarMap Γ →
      Expr jasminDialect Γ t → String → ZBind)
    {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (vm : VarMap Γ)
    (next : Nat) (acc : Array ZBind) : Com jasminDialect Γ t → Array ZBind × String
  | .ret v => (acc, vm t v)
  | .var (t := tEx) e body =>
      let dst := "v" ++ toString next
      collectWith f (vm.extend (t := tEx) dst) (next + 1) (acc.push (f vm e dst)) body

/-- The bindings of a packed `Com`. -/
def collectZBinds {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (vm : VarMap Γ)
    (next : Nat) (acc : Array ZBind) (c : Com jasminDialect Γ t) : Array ZBind × String :=
  collectWith exprZBind vm next acc c

/-- The bindings of `LaneMapZmm.laneMapZmm c` read off the scalar 64-bit program `c` in
    one pass, without building the widened `Com`, with the names `collectZBinds` gives the
    widened program. -/
def collectZBindsScalar {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (vm : VarMap Γ)
    (next : Nat) (acc : Array ZBind) (c : Com jasminDialect Γ t) : Array ZBind × String :=
  collectWith exprZBindScalar vm next acc c

/-- The bindings of the 32-bit lane map of the scalar 32-bit program `c`, read off `c`
    in one pass. -/
def collectZBindsScalar32 {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (vm : VarMap Γ)
    (next : Nat) (acc : Array ZBind) (c : Com jasminDialect Γ t) : Array ZBind × String :=
  collectWith exprZBindScalar32 vm next acc c

/-! ## 2. Constants and allocation -/

/-- The pool entry of a 512-bit constant `v`, as the base-2 logarithm of its alignment
    and its words: one 8-byte word when its eight 64-bit lanes are equal (which covers
    every sixteen-lane broadcast, whose word repeats the 32-bit lane), else the eight
    words of the 64-byte value. -/
def constEntry (v : Nat) : Nat × List Nat :=
  if bcast512 v = v then (3, qwordsLE 1 v) else (6, qwordsLE 8 v)

theorem leValue_constEntry_of_ne (v : Nat) (h : bcast512 v ≠ v) :
    leValue (constEntry v).2 = v % 2 ^ 512 := by
  simp [constEntry, h, leValue_qwordsLE]

/-- The constants of a binding list: each constant binding's name mapped to the data
    label and value it reads, and the `.rodata` pool holding one entry (`constEntry`)
    per distinct value, labelled `.L<sym>_c<i>`. -/
def constTable (sym : String) (bs : Array ZBind) :
    Std.HashMap String (String × Nat) × Pool :=
  let (names, _, pool) := bs.foldl
    (fun (acc : Std.HashMap String (String × Nat) × Std.HashMap Nat String × Pool) b =>
      let (names, byVal, pool) := acc
      match b with
      | .const d v =>
        match byVal.get? v with
        | some lbl => (names.insert d (lbl, v), byVal, pool)
        | none =>
          let (pool, lbl) := pool.push (constEntry v).1 (constEntry v).2
          (names.insert d (lbl, v), byVal.insert v lbl, pool)
      | _ => acc)
    ({}, {}, Pool.empty (".L" ++ sym))
  (names, pool)

/-- The index of the last binding reading each name; the names in `live` are read at
    index `bs.size`, past the last binding. -/
def lastUses (bs : Array ZBind) (live : List String) : Std.HashMap String Nat :=
  let m := bs.zipIdx.foldl
    (fun m (b, i) => b.srcs.foldl (fun m s => m.insert s i) m) ({} : Std.HashMap String Nat)
  live.foldl (fun m s => m.insert s bs.size) m

/-- The vector register numbered `i` in mode `md`: `%zmm i` or `%ymm i`. -/
def vecReg (md : Mode) (i : Nat) : String :=
  (match md with | .zmm => "%zmm" | .ymm => "%ymm") ++ toString i

/-- The scratch register a constant operand is loaded into; never allocated. -/
def scratchReg (md : Mode) : String := vecReg md 31

/-- The temporaries of the high-multiply expansion; never allocated when the program
    contains a high multiply. -/
def mulhiTemps (md : Mode) : List String := [vecReg md 28, vecReg md 29, vecReg md 30]

/-- Linear-scan allocation of registers `0..30` of mode `md` less `reserved` over the
    non-constant values: parameter `i` is pinned to register `i`; at each binding the
    registers of the names it reads for the last time are released before its destination
    is assigned, and the destination's register is released at once when nothing reads
    it. The destination of a `vpternlog`, which overwrites its first operand, is the
    register of the first of its operands read for the last time there, when there is
    one (`bindLines` permutes the truth table to put that operand first); every other
    destination is the head of the free list. Constants take no register. Fails when a
    binding finds no free register. -/
def allocZmmLinear (md : Mode) (params : List String)
    (consts : Std.HashMap String (String × Nat))
    (bs : Array ZBind) (live : List String) (reserved : List String := []) :
    Except String (Std.HashMap String String) := do
  let lu := lastUses bs live
  let pinned : Std.HashMap String String :=
    params.zipIdx.foldl (fun m (p, i) => m.insert p (vecReg md i)) {}
  let pool : List String :=
    (((List.range 31).drop params.length).map (vecReg md)).filter
      (fun r => !reserved.contains r)
  let step (st : Std.HashMap String String × List String) (bi : ZBind × Nat) :
      Except String (Std.HashMap String String × List String) := do
    let (alloc, free) := st
    let (b, i) := bi
    if consts.contains b.dst then pure (alloc, free) else
    let dying := b.srcs.eraseDups.filter (fun s => lu.get? s == some i)
    let dyingRegs := dying.filterMap alloc.get?
    let free := free ++ dyingRegs
    let tied : Option String := match b with
      | .tern .. => dyingRegs.head?
      | _ => none
    let pick : Option (String × List String) := match tied, free with
      | some r, _ => some (r, free.erase r)
      | none, r :: rest => some (r, rest)
      | none, [] => none
    match pick with
    | none => throw s!"vpackZMM linear render: no free register at binding {i}"
    | some (r, rest) =>
      let alloc := alloc.insert b.dst r
      pure (alloc, if lu.contains b.dst then rest else rest ++ [r])
  let (alloc, _) ← bs.zipIdx.foldlM step (pinned, pool)
  pure alloc

open CatCrypt.Crypto.Optimizer.GenericRegAlloc (NUStep NUMove nextUseAlloc)

/-- The non-constant names a binding reads and the names it writes, as the register
    allocator sees them: a deferred low half is written by its `mulhilo`. -/
def bindRW (consts : Std.HashMap String (String × Nat)) : ZBind → List String × List String
  | .pack _ _ d a b => (([a, b].filter (!consts.contains ·)).eraseDups, [d])
  | .minu _ d a b => (([a, b].filter (!consts.contains ·)).eraseDups, [d])
  | .mulhi d a b => (([a, b].filter (!consts.contains ·)).eraseDups, [d])
  | .mulhilo h l a b => (([a, b].filter (!consts.contains ·)).eraseDups, [h, l])
  | .montsub d a b _ _ => (([a, b].filter (!consts.contains ·)).eraseDups, [d])
  | .rol _ d a _ => (([a].filter (!consts.contains ·)), [d])
  | .shi _ _ d a _ => (([a].filter (!consts.contains ·)), [d])
  | .tern _ _ d a b c => (([a, b, c].filter (!consts.contains ·)).eraseDups, [d])
  | _ => ([], [])

/-- Allocation with spilling of registers `0..30` of mode `md` less `reserved`, through
    `GenericRegAlloc.nextUseAlloc`. The steps are the bindings, then one step per output
    store reading that output; parameter `s` is value `s`, with its home at `inOffset s`
    of the input region, and a spill slot `k` is at `stride·k(%rsp)`. Returns, per step,
    the move lines before it and the register of each name it reads or writes, and the
    frame size in bytes. -/
def allocZmmSpill (md : Mode) (inOffset : Nat → Nat) (params : List String)
    (consts : Std.HashMap String (String × Nat)) (bs : Array ZBind) (outs : List String)
    (reserved : List String) :
    Except String (Array (List String × Std.HashMap String String) × Nat) := do
  let ids0 : Std.HashMap String Nat := params.zipIdx.foldl (fun m (p, i) => m.insert p i) {}
  let idOf (ids : Std.HashMap String Nat) (n : String) : Except String Nat :=
    match ids.get? n with
    | some i => pure i
    | none => throw s!"vpackZMM linear render: unallocated operand {n}"
  let (ids, names, steps) ← bs.foldlM
    (fun (acc : Std.HashMap String Nat × Array String × Array NUStep) b => do
      let (ids, names, steps) := acc
      let (rs, ws) := bindRW consts b
      let reads ← rs.mapM (idOf ids)
      let (ids, names, writes) := ws.foldl (fun (ids, names, wi) w =>
        (ids.insert w names.size, names.push w, wi ++ [names.size])) (ids, names, [])
      pure (ids, names, steps.push { reads, writes }))
    (ids0, params.toArray, #[])
  let outSteps ← outs.mapM (fun o =>
    if consts.contains o then pure ({ reads := [], writes := [] } : NUStep)
    else do pure { reads := [← idOf ids o], writes := [] })
  let pool := (List.range 31).filter (fun i => !reserved.contains (vecReg md i))
  let (out, nSlots) ← nextUseAlloc names.size pool (· < params.length)
    (steps ++ outSteps.toArray)
  let moveLine : NUMove → String
    | .store _ r s => "\tvmovdqu64 " ++ vecReg md r ++ ", " ++ toString (md.stride * s) ++ "(%rsp)"
    | .load _ r (some s) =>
      "\tvmovdqu64 " ++ toString (md.stride * s) ++ "(%rsp), " ++ vecReg md r
    | .load v r none => "\tvmovdqu64 " ++ toString (inOffset v) ++ "(%rsi), " ++ vecReg md r
  pure (out.map (fun a => (a.moves.map moveLine,
      a.regs.foldl (fun m (v, r) => m.insert (names.getD v "") (vecReg md r)) {})),
    md.stride * nSlots)

/-! ## 3. Rendering -/

/-- Whether a 512-bit value is the broadcast of one lane of width `w`. -/
def isBcast (w : LaneW) (v : Nat) : Bool :=
  match w with
  | .q => bcast512 v == v
  | .d => bcast512d v == v

/-- The memory operand of a constant read by a width-`w` operation in mode `md`: an
    embedded broadcast of its lane to the `md.act / w.bits` lanes of the register, or its
    value. -/
def constOperand (md : Mode) (w : LaneW) (c : String × Nat) : String :=
  if isBcast w c.2 then
    c.1 ++ "(%rip)" ++ "{1to" ++ toString (md.act / w.bits) ++ "}"
  else c.1 ++ "(%rip)"

/-- The line loading a constant read by a width-`w` operation into register `r`. -/
def constLoadTo (w : LaneW) (c : String × Nat) (r : String) : String :=
  if isBcast w c.2 then
    (match w with | .q => "\tvpbroadcastq " | .d => "\tvpbroadcastd ") ++ c.1 ++ "(%rip), " ++ r
  else "\tvmovdqu64 " ++ c.1 ++ "(%rip), " ++ r

/-- The line loading a constant into `scratchReg md`. -/
def constLoad (md : Mode) (w : LaneW) (c : String × Nat) : String :=
  constLoadTo w c (scratchReg md)

/-- The packed operations whose operands may be exchanged. -/
def bopCommutes : JasminBinOp → Bool
  | .add | .mul | .and | .or | .xor => true
  | _ => false

/-- The immediate-count shift mnemonic of `bop` at width `w`, for `shl` and `shr`. -/
def shiftImmMnemonic (w : LaneW) : JasminBinOp → Option String
  | .shl => some (match w with | .q => "vpsllq" | .d => "vpslld")
  | .shr => some (match w with | .q => "vpsrlq" | .d => "vpsrld")
  | _ => none

/-- The mnemonic of `bop` at width `w`: at 64 bits the packed operation of
    `VpackZmmAsmPrint`, except that a multiply is `vpmuludq` (the product of the low 32
    bits of each lane) when `mulU` holds, which equals `vpmullq` on operands below
    `2^32`; at 32 bits the dword operation. -/
def packMnemonic (w : LaneW) (mulU : Bool) (bop : JasminBinOp) : String :=
  match w, bop with
  | .q, .mul => if mulU then "vpmuludq" else VpackZmmAsmPrint.JasminBinOp.zmmAttMnemonic bop
  | .q, _ => VpackZmmAsmPrint.JasminBinOp.zmmAttMnemonic bop
  | .d, .add => "vpaddd"
  | .d, .sub => "vpsubd"
  | .d, .mul => "vpmulld"
  | .d, .and => "vpandd"
  | .d, .or => "vpord"
  | .d, .xor => "vpxord"
  | .d, .andn => "vpandnd"
  | .d, .shl => "vpsllvd"
  | .d, .shr => "vpsrlvd"

/-- The line `mn src2, src1, dst`. -/
def opLine (mn : String) (rd ra rb : String) : String :=
  "\t" ++ mn ++ " " ++ rb ++ ", " ++ ra ++ ", " ++ rd

/-- The even and odd 64-bit products of the sixteen-lane operands `ra`, `rb`: the even
    products (`vpmuludq`) into register 28, and the odd lanes duplicated down
    (`vmovshdup`) and multiplied into `odd`. When `rb` holds a sixteen-lane broadcast
    (`rbBcast`) its odd lanes equal its even lanes and it is used as it is. -/
def productLines (md : Mode) (odd ra rb : String) (rbBcast : Bool := false) : List String :=
  let t0 := vecReg md 28; let t1 := vecReg md 29; let t2 := vecReg md 30
  [ opLine "vpmuludq" t0 ra rb
  , "\tvmovshdup " ++ ra ++ ", " ++ t1 ]
  ++ (if rbBcast then [] else ["\tvmovshdup " ++ rb ++ ", " ++ t2]) ++
  [ opLine "vpmuludq" odd t1 (if rbBcast then rb else t2) ]

/-- The sixteen-lane high multiply of `ra` and `rb` into `rd`: the odd products
    (`productLines`) hold the odd lanes' high words in place, and the even products'
    high words are merged into the even lanes by `vmovshdup` under `%k2` (even lanes
    set). -/
def mulhiLines (md : Mode) (rd ra rb : String) (rbBcast : Bool := false) : List String :=
  productLines md rd ra rb rbBcast ++ ["\tvmovshdup " ++ vecReg md 28 ++ ", " ++ rd ++ "{%k2}"]

/-- The low and high halves of the sixteen-lane products of `ra` and `rb`, from one
    pair of `vpmuludq`: the high half as in `mulhiLines`, and the low half the even
    products' low words with the odd products' low words merged into the odd lanes by
    `vmovsldup` under `%k1` (odd lanes set). `rhi` and `rlo` are distinct. -/
def mulhiloLines (md : Mode) (rhi rlo ra rb : String) (rbBcast : Bool := false) :
    List String :=
  let t0 := vecReg md 28; let t1 := vecReg md 29
  productLines md t1 ra rb rbBcast ++
  [ "\tvmovdqa64 " ++ t1 ++ ", " ++ rhi
  , "\tvmovshdup " ++ t0 ++ ", " ++ rhi ++ "{%k2}"
  , "\tvmovsldup " ++ t1 ++ ", " ++ t0 ++ "{%k1}"
  , "\tvmovdqa64 " ++ t0 ++ ", " ++ rlo ]

/-- The Montgomery difference `mulhi(a, b) - mulhi((a·b)·mu, p)` of `ra` and `rb` into
    `rd`, kept in the even/odd 64-bit products until one merge: the even and odd products
    `x` (`productLines`), `q = x·mu` and `y = q·p` by `vpmuludq` on the low dwords (the
    constants as `{1to8}` memory operands), the 64-bit differences `x - y`, and the even
    differences' high words merged into the odd ones by `vmovshdup` under `%k2`. The high
    word of `x - y` is the difference of the high words when `mu·p ≡ 1 (mod 2^32)`, since
    then `x` and `y` have equal low words (`RangeDomain.extractLsb'_sub_of_setWidth_eq`). -/
def montSubLines (md : Mode) (rd ra rb : String) (rbBcast : Bool) (mu p : String × Nat) :
    List String :=
  let t0 := vecReg md 28; let t1 := vecReg md 29; let t2 := vecReg md 30
  let cm := mu.1 ++ "(%rip){1to" ++ toString (md.act / 64) ++ "}"
  let cp := p.1 ++ "(%rip){1to" ++ toString (md.act / 64) ++ "}"
  productLines md t1 ra rb rbBcast ++
  [ opLine "vpmuludq" t2 t0 cm, opLine "vpmuludq" t2 t2 cp, opLine "vpsubq" t0 t0 t2
  , opLine "vpmuludq" t2 t1 cm, opLine "vpmuludq" t2 t2 cp, opLine "vpsubq" rd t1 t2
  , "\tvmovshdup " ++ t0 ++ ", " ++ rd ++ "{%k2}" ]

/-- The instruction lines of binding `b` in mode `md`. A constant second operand is a
    memory operand; a constant first operand is exchanged with a register second operand
    when `bop` commutes, and otherwise read from its resident register or loaded into
    `scratchReg md`; a shift by a broadcast constant below the lane width uses the
    immediate form. Constant bindings emit nothing. -/
def bindLines (md : Mode) (consts : Std.HashMap String (String × Nat))
    (alloc : Std.HashMap String String) (narrow : Std.HashSet String := {})
    (resident : Std.HashMap String String := {}) :
    ZBind → Except String (List String)
  | .const _ _ => pure []
  | .deferred _ _ _ => pure []
  | .mulhilo h l a b =>
      match alloc.get? h, alloc.get? l, alloc.get? a, consts.get? b, alloc.get? b with
      | some rh, some rl, some ra, none, some rb => pure (mulhiloLines md rh rl ra rb)
      | some rh, some rl, some ra, some cb, _ =>
        match resident.get? cb.1 with
        | some r => pure (mulhiloLines md rh rl ra r (isBcast .d cb.2))
        | none => pure (constLoad md .d cb ::
            mulhiloLines md rh rl ra (scratchReg md) (isBcast .d cb.2))
      | _, _, _, _, _ => throw s!"vpackZMM linear render: unallocated operand at {h}"
  | .montsub d a b mu p =>
      match alloc.get? d, alloc.get? a, consts.get? mu, consts.get? p, consts.get? b,
        alloc.get? b with
      | some rd, some ra, some cm, some cp, none, some rb =>
        pure (montSubLines md rd ra rb false cm cp)
      | some rd, some ra, some cm, some cp, some cb, _ =>
        match resident.get? cb.1 with
        | some r => pure (montSubLines md rd ra r (isBcast .d cb.2) cm cp)
        | none => pure (constLoad md .d cb ::
            montSubLines md rd ra (scratchReg md) (isBcast .d cb.2) cm cp)
      | _, _, _, _, _, _ => throw s!"vpackZMM linear render: unallocated operand at {d}"
  | .other d => throw s!"vpackZMM linear render: binding {d} is not a packed op or constant"
  | .minu w d a b =>
      match alloc.get? d, alloc.get? a, alloc.get? b with
      | some rd, some ra, some rb =>
        pure [opLine (match w with | .q => "vpminuq" | .d => "vpminud") rd ra rb]
      | _, _, _ => throw s!"vpackZMM linear render: unallocated operand at {d}"
  | .rol w d a n =>
      match alloc.get? d, alloc.get? a with
      | some rd, some ra =>
        pure ["\t" ++ (match w with | .q => "vprolq" | .d => "vprold") ++ " $" ++ toString n
          ++ ", " ++ ra ++ ", " ++ rd]
      | _, _ => throw s!"vpackZMM linear render: unallocated operand at {d}"
  | .shi w left d a n =>
      let smn := (shiftImmMnemonic w (if left then .shl else .shr)).getD ""
      let line (src rd : String) : String :=
        "\t" ++ smn ++ " $" ++ toString n ++ ", " ++ src ++ ", " ++ rd
      match alloc.get? d, alloc.get? a, consts.get? a with
      | some rd, some ra, _ => pure [line ra rd]
      | some rd, none, some ca => pure [constLoad md w ca, line (scratchReg md) rd]
      | _, _, _ => throw s!"vpackZMM linear render: unallocated operand at {d}"
  | .tern w imm d a b c =>
      match alloc.get? d, alloc.get? a, alloc.get? b, alloc.get? c with
      | some rd, some ra, some rb, some rc =>
        let mn := match w with | .q => "vpternlogq" | .d => "vpternlogd"
        let line (i : Nat) (r3 r2 : String) : String :=
          "\t" ++ mn ++ " $" ++ toString i ++ ", " ++ r3 ++ ", " ++ r2 ++ ", " ++ rd
        let bit (x y z : Bool) : Bool := imm.testBit (4 * x.toNat + 2 * y.toNat + z.toNat)
        -- the destination is the first operand: keep it in the register of an operand
        -- the destination shares, with the truth table permuted to match
        if rd == ra then pure [line imm rc rb]
        else if rd == rb then pure [line (ternTable fun p q r => bit q p r).toNat rc ra]
        else if rd == rc then pure [line (ternTable fun p q r => bit q r p).toNat rb ra]
        else pure ["\tvmovdqa64 " ++ ra ++ ", " ++ rd, line imm rc rb]
      | _, _, _, _ => throw s!"vpackZMM linear render: unallocated operand at {d}"
  | .mulhi d a b => do
      let reg (n : String) : Except String String :=
        match alloc.get? n with
        | some r => pure r
        | none => throw s!"vpackZMM linear render: unallocated operand {n} at {d}"
      let rd ← reg d
      let constReg (c : String × Nat) : List String × String :=
        match resident.get? c.1 with
        | some r => ([], r)
        | none => ([constLoad md .d c], scratchReg md)
      match consts.get? a, consts.get? b with
      | none, none => pure (mulhiLines md rd (← reg a) (← reg b))
      | none, some cb =>
        let (ls, r) := constReg cb
        pure (ls ++ mulhiLines md rd (← reg a) r (isBcast .d cb.2))
      | some ca, none =>
        let (ls, r) := constReg ca
        pure (ls ++ mulhiLines md rd (← reg b) r (isBcast .d ca.2))
      | some ca, some cb =>
        pure (constLoad md .d ca :: constLoadTo .d cb (vecReg md 30) ::
          mulhiLines md rd (scratchReg md) (vecReg md 30))
  | .pack w bop d a b => do
      let reg (n : String) : Except String String :=
        match alloc.get? n with
        | some r => pure r
        | none => throw s!"vpackZMM linear render: unallocated operand {n} at {d}"
      let rd ← reg d
      let mn := packMnemonic w (narrow.contains d) bop
      let lane := 2 ^ w.bits
      let shiftImm (c : String × Nat) (src : String) : Option String :=
        match shiftImmMnemonic w bop with
        | some smn => if isBcast w c.2 ∧ c.2 % lane < w.bits then
            some ("\t" ++ smn ++ " $" ++ toString (c.2 % lane) ++ ", " ++ src ++ ", " ++ rd)
          else none
        | none => none
      match consts.get? a, consts.get? b with
      | none, none => pure [opLine mn rd (← reg a) (← reg b)]
      | none, some cb =>
        let ra ← reg a
        match shiftImm cb ra with
        | some line => pure [line]
        | none => pure [opLine mn rd ra (constOperand md w cb)]
      | some ca, none =>
        let rb ← reg b
        if bopCommutes bop then pure [opLine mn rd rb (constOperand md w ca)]
        else match resident.get? ca.1 with
          | some r => pure [opLine mn rd r rb]
          | none => pure [constLoad md w ca, opLine mn rd (scratchReg md) rb]
      | some ca, some cb =>
        match shiftImm cb (scratchReg md) with
        | some line => pure [constLoad md w ca, line]
        | none => pure [constLoad md w ca, opLine mn rd (scratchReg md) (constOperand md w cb)]

/-! ## 3b. Range facts

The fast selections read their range facts from the verified interval analysis
`ComRange.rangeAnalysis` (`ComRange.rangeAnalysis_sound`: inputs in their intervals imply
every binding in its interval). `rangeInfoOf` turns its per-binding intervals into the
name-keyed map of the binding list: parameter `s` gets `[0, inBound]`, binding `i` the
analysis's `i`-th interval (the scalar collectors name binding `i` `v{i}`, in the order
the analysis visits them). A 64-bit multiply renders as `vpmuludq` when both operand lanes
lie below `2^32` (`RangeDomain.mul_eq_mul_setWidth32`), and a conditional add or subtract
as an unsigned minimum when `RangeDomain.ivCondAdd?` accepts the range of its operand
(`RangeDomain.condAdd_eq_umin`, `condAdd_sub_eq_umin`). -/

open CatCrypt.Crypto.SecureCompilation.RangeDomain (Iv ivLane ivCondAdd?)

/-- The range facts of a binding list: an interval per name and the 64-bit multiplies
    whose operand lanes lie below `2^32`. -/
structure RangeInfo where
  iv : Std.HashMap String Iv := {}
  narrow : Std.HashSet String := {}

/-- The least and greatest lane of the 512-bit constant `v` at width `w`. -/
def constLaneIv (w : LaneW) (v : Nat) : Iv :=
  let lanes := (List.range (512 / w.bits)).map (fun k => (v / 2 ^ (w.bits * k)) % 2 ^ w.bits)
  (Int.ofNat (lanes.foldl min (2 ^ w.bits)), Int.ofNat (lanes.foldl max 0))

/-- The interval `i` for every variable of a context. -/
def ivsConst (i : Iv) : (Γ : Ctxt jasminDialect) → HVector (fun _ => Iv) Γ
  | [] => .nil
  | _ :: Γ => .cons i (ivsConst i Γ)

/-- The range facts of the binding list `bs` from the analysis intervals `arr` (binding
    `i` named `v{i}`) and the parameters `names` in `[0, inBound]`. -/
def rangeInfoOf (consts : Std.HashMap String (String × Nat)) (names : List String)
    (inBound : Nat) (arr : Array Iv) (bs : Array ZBind) : RangeInfo :=
  let iv0 : Std.HashMap String Iv :=
    names.foldl (fun m p => m.insert p (0, Int.ofNat inBound)) {}
  let iv := arr.zipIdx.foldl (fun m (i, k) => m.insert ("v" ++ toString k) i) iv0
  let get (w : LaneW) (n : String) : Iv :=
    match consts.get? n with
    | some c => constLaneIv w c.2
    | none => (iv.get? n).getD (0, 2 ^ w.bits - 1)
  let narrow := bs.foldl (fun s b =>
    match b with
    | .pack .q .mul d a b2 =>
      if (ivLane 64 (get .q a)).2 < 2 ^ 32 && (ivLane 64 (get .q b2)).2 < 2 ^ 32 then
        s.insert d else s
    | _ => s) {}
  { iv, narrow }

/-- The conditional add or subtract of a constant `C` that the BabyBear blocks emit,
    `r = d + ((0 - (d >> (L-1))) & C)` at lane width `L`, rewritten to an unsigned
    minimum when the three intermediate values have no other reader: to
    `r = minu(x, d)` when `d = x - C` and `d` has exactly the two readers, and otherwise
    to `u = d + C; r = minu(d, u)`. The two agree on every lane where `d` is below
    `2^(L-1)` or at least `2^L - C` and `C < 2^(L-1)`; on other lanes they differ, so the
    rewrite happens only where `ok w d c` holds, which the renderer takes from `RangeDomain.ivCondAdd?`
    on the range of `d`. -/
def csubToMinu (consts : Std.HashMap String (String × Nat))
    (ok : LaneW → String → Nat → Bool) (bs : Array ZBind) :
    Array ZBind := Id.run do
  let defs : Std.HashMap String Nat := bs.zipIdx.foldl (fun m (b, i) => m.insert b.dst i) {}
  let uses : Std.HashMap String Nat :=
    bs.foldl (fun m b => b.srcs.foldl (fun m s => m.insert s (m.getD s 0 + 1)) m) {}
  let constVal (n : String) : Option Nat := (consts.get? n).map (·.2)
  let defOf (n : String) : Option ZBind := (defs.get? n).bind (fun i => bs[i]?)
  let used (n : String) : Nat := uses.getD n 0
  -- the constant name and value and the removed names when `d + t` is the idiom at `w`
  let idiom (w : LaneW) (d t : String) : Option (String × Nat × List String) := do
    let .pack w1 .and _ t1 t2 ← defOf t | none
    let (m, cC) ← if (constVal t2).isSome then some (t1, t2)
      else if (constVal t1).isSome then some (t2, t1) else none
    let c ← constVal cC
    let .pack w2 .sub _ z s ← defOf m | none
    let .pack w3 .shr _ d2 k ← defOf s | none
    let signShift := match w with | .q => bcast512 63 | .d => bcast512d 31
    if w1 == w && w2 == w && w3 == w && constVal z == some 0 && d2 == d
        && constVal k == some signShift
        && used s == 1 && used m == 1 && used t == 1 then
      some (cC, c, [s, m, t])
    else none
  let mut rw : Std.HashMap String (List ZBind) := {}
  let mut removed : Std.HashSet String := {}
  for b in bs do
    match b with
    | .pack w .add r a b2 =>
      let hit := (idiom w a b2).map (fun h => (a, h)) <|> (idiom w b2 a).map (fun h => (b2, h))
      match hit with
      | some (d, cC, c, rem) =>
        if ok w d c then
          let direct : Option String := do
            let .pack w4 .sub _ x cC2 ← defOf d | none
            if w4 == w && constVal cC2 == some c && (constVal x).isNone && used d == 2 then
              some x else none
          match direct with
          | some x => rw := rw.insert r [.minu w r x d]
          | none => rw := rw.insert r [.pack w .add (r ++ "_u") d cC, .minu w r d (r ++ "_u")]
          removed := rem.foldl (fun s n => s.insert n) removed
      | none => pure ()
    | _ => pure ()
  return bs.foldl (fun acc b =>
    if removed.contains b.dst then acc
    else match rw.get? b.dst with
      | some bs' => acc ++ bs'.toArray
      | none => acc.push b) #[]

/-- The low word of a sixteen-lane broadcast constant, when the constant is one. -/
def bcastLowD (c : Option (String × Nat)) : Option Nat :=
  c.bind (fun c => if isBcast .d c.2 then some (c.2 % 2 ^ 32) else none)

/-- The first `n` non-constant bindings of `bs` from index `j` on, the constant bindings
    among them in order, and the index after the last binding read. -/
def takeSkipConst (bs : Array ZBind) (n j : Nat) : Array ZBind × Array ZBind × Nat :=
  Id.run do
  let mut picked : Array ZBind := #[]
  let mut skipped : Array ZBind := #[]
  let mut k := j
  while picked.size < n && k < bs.size do
    match bs[k]? with
    | some (.const d v) => skipped := skipped.push (.const d v)
    | some b => picked := picked.push b
    | none => pure ()
    k := k + 1
  return (picked, skipped, k)

/-- The Montgomery step of `FieldDescentBBMont32` as five bindings,
    `lo = a·b`, `hi = mulhi(a, b)`, `m = lo·mu`, `u = mulhi(m, p)`, `d = hi - u`,
    consecutive up to constant bindings between them (the descent's `mulBlockM` binds `mu`
    before `m` and `p` before `u`), with
    `mu` and `p` sixteen-lane broadcast constants whose low words satisfy
    `mu·p ≡ 1 (mod 2^32)`, at most one of `a`, `b` constant, `lo`, `hi`, `m`, `u` each read
    once (by the next binding of the step) and none of them in `keep`: the five are
    rewritten to the one binding `montsub d a b mu p` (`montSubLines`), preceded by the
    constant bindings between them. The value of `d` is unchanged. -/
def fuseMontSub (consts : Std.HashMap String (String × Nat)) (keep : Std.HashSet String)
    (bs : Array ZBind) : Array ZBind := Id.run do
  let uses : Std.HashMap String Nat :=
    bs.foldl (fun m b => b.srcs.foldl (fun m s => m.insert s (m.getD s 0 + 1)) m) {}
  let used (n : String) : Nat := uses.getD n 0
  let hit (lo a b hi a2 b2 m x y u x2 y2 h2 u2 : String) : Option (String × String) := do
    guard ((a2 == a && b2 == b) || (a2 == b && b2 == a))
    guard (!(consts.contains a && consts.contains b))
    guard (h2 == hi && u2 == u && lo != a && lo != b)
    let mu ← if x == lo then some y else if y == lo then some x else none
    let p ← if x2 == m then some y2 else if y2 == m then some x2 else none
    let vm ← bcastLowD (consts.get? mu)
    let vp ← bcastLowD (consts.get? p)
    guard (vm * vp % 2 ^ 32 == 1)
    guard (used lo == 1 && used hi == 1 && used m == 1 && used u == 1)
    guard (!([lo, hi, m, u].any keep.contains))
    pure (mu, p)
  let mut out : Array ZBind := #[]
  let mut i := 0
  while i < bs.size do
    match bs[i]? with
    | some (.pack .d .mul lo a b) =>
      let (nx, cs, k) : Array ZBind × Array ZBind × Nat := takeSkipConst bs 4 (i + 1)
      let fused : Option ZBind :=
        match (nx.toList : List ZBind) with
        | [.mulhi hi a2 b2, .pack .d .mul m x y, .mulhi u x2 y2, .pack .d .sub d h2 u2] =>
          (hit lo a b hi a2 b2 m x y u x2 y2 h2 u2).map fun (mu, p) =>
            -- a constant operand goes second
            let (a', b') := if consts.contains a then (b, a) else (a, b)
            .montsub d a' b' mu p
        | _ => none
      match fused with
      | some z =>
        out := (out ++ cs).push z
        i := k
      | none =>
        out := out.push (.pack .d .mul lo a b)
        i := i + 1
    | some z =>
      out := out.push z
      i := i + 1
    | none => i := i + 1
  return out

/-- The low half `lo = a·b` (`vpackZMMd .mul`) immediately followed by the high half
    `hi = mulhi(a, b)` of the same two operands, at most one of them constant, with `lo`
    read later: the
    pair is rewritten so that the high-half binding computes both halves from one pair of
    `vpmuludq` (`mulhilo`) and the low-half binding emits nothing (`deferred`), keeping
    its register. The values are unchanged. -/
def fuseMulHiLo (consts : Std.HashMap String (String × Nat)) (bs : Array ZBind) :
    Array ZBind := Id.run do
  let uses : Std.HashMap String Nat :=
    bs.foldl (fun m b => b.srcs.foldl (fun m s => m.insert s (m.getD s 0 + 1)) m) {}
  let mut out : Array ZBind := #[]
  let mut i := 0
  while i < bs.size do
    match bs[i]?, bs[i + 1]? with
    | some (.pack .d .mul lo a b), some (.mulhi hi a2 b2) =>
      if ((a2 == a && b2 == b) || (a2 == b && b2 == a))
          && !(consts.contains a && consts.contains b)
          && uses.getD lo 0 > 0 && lo != a && lo != b then
        -- a constant operand goes second
        let (x, y) := if consts.contains a then (b, a) else (a, b)
        out := (out.push (.deferred lo x y)).push (.mulhilo hi lo x y)
        i := i + 2
      else
        out := out.push (.pack .d .mul lo a b)
        i := i + 1
    | some x, _ =>
      out := out.push x
      i := i + 1
    | none, _ => i := i + 1
  return out

/-- The lane value of the constant `n` at width `w`, when `n` is a broadcast constant. -/
def bcastLane (consts : Std.HashMap String (String × Nat)) (w : LaneW) (n : String) :
    Option Nat :=
  (consts.get? n).bind (fun c => if isBcast w c.2 then some (c.2 % 2 ^ w.bits) else none)

/-- The rotate `d = (a << n) | (a >> (L - n))`, `0 < n < L`, at lane width `L`, with the
    shift counts broadcast constants or immediates, `a` not a constant and the two shifts each read once
    and outside `keep`: the three bindings are rewritten to `rol w d a n` (`vprolq`) at
    the position of `d`. The value of `d` is unchanged
    (`ZmmTextModel.rotateLeft_eq_or_shifts`). -/
def fuseRol (consts : Std.HashMap String (String × Nat)) (keep : Std.HashSet String)
    (bs : Array ZBind) : Array ZBind := Id.run do
  let defs : Std.HashMap String ZBind := bs.foldl (fun m b => m.insert b.dst b) {}
  let uses : Std.HashMap String Nat :=
    bs.foldl (fun m b => b.srcs.foldl (fun m s => m.insert s (m.getD s 0 + 1)) m) {}
  let used (n : String) : Nat := uses.getD n 0
  -- `x = a << n` and `y = a >> (L - n)`
  -- a shift by a broadcast constant or by an immediate: its source and count
  let shiftOf (w : LaneW) (left : Bool) (x : String) : Option (LaneW × String × Nat) :=
    match defs.get? x with
    | some (.pack w1 bop _ a k) =>
      if bop == (if left then .shl else .shr) then (bcastLane consts w k).map (w1, a, ·)
      else none
    | some (.shi w1 l _ a n) => if l == left then some (w1, a, n) else none
    | _ => none
  let hit (w : LaneW) (x y : String) : Option (String × Nat) := do
    let (w1, a, n) ← shiftOf w true x
    let (w2, a2, n2) ← shiftOf w false y
    guard (w1 == w && w2 == w && a == a2 && 0 < n && n < w.bits && n + n2 == w.bits)
    guard (!consts.contains a && x != y)
    guard (used x == 1 && used y == 1 && !keep.contains x && !keep.contains y)
    pure (a, n)
  let mut rw : Std.HashMap String ZBind := {}
  let mut removed : Std.HashSet String := {}
  for b in bs do
    match b with
    | .pack w .or d x y =>
      match hit w x y <|> hit w y x with
      | some (a, n) =>
        rw := rw.insert d (.rol w d a n)
        removed := (removed.insert x).insert y
      | none => pure ()
    | _ => pure ()
  return bs.filterMap (fun b => if removed.contains b.dst then none else some (rw.getD b.dst b))

/-- The three-input bitwise forms `vpternlog` computes in one instruction, on
    non-constant operands, the inner bindings each read once and outside `keep`:
    `d = x ⊕ ((y ⊕ 1…1) ∧ z)` (Keccak χ, the all-ones constant broadcast at the lane
    width) is rewritten to `tern w (ternTable chiB) d x y z`, and `d = (x ⊕ y) ⊕ z` to
    `tern w (ternTable xor3B) d x y z`, both at the position of `d`, the inner bindings
    removed. Operands commute. The value of `d` is unchanged
    (`ZmmTextModel.ternTerms_eval`). -/
def fuseTern (consts : Std.HashMap String (String × Nat)) (keep : Std.HashSet String)
    (bs : Array ZBind) : Array ZBind := Id.run do
  let uses : Std.HashMap String Nat :=
    bs.foldl (fun m b => b.srcs.foldl (fun m s => m.insert s (m.getD s 0 + 1)) m) {}
  let used (n : String) : Nat := uses.getD n 0
  let reg (n : String) : Bool := !consts.contains n
  let allOnes (w : LaneW) (n : String) : Bool := bcastLane consts w n == some (2 ^ w.bits - 1)
  let mut cur : Std.HashMap String ZBind := {}
  let mut removed : Std.HashSet String := {}
  let mut out : Array ZBind := #[]
  for b in bs do
    let free (n : String) : Bool := used n == 1 && !keep.contains n && !removed.contains n
    let fused : Option (ZBind × List String) :=
      match b with
      | .pack w .xor d p q =>
        let chiS (x u s z : String) : Option (ZBind × List String) := do
          let .pack w2 .xor _ s1 s2 ← cur.get? s | none
          let y ← if allOnes w s2 then some s1 else if allOnes w s1 then some s2 else none
          guard (w2 == w && reg x && reg y && reg z && free s && s != u)
          pure (.tern w (ternTable chiB).toNat d x y z, [u, s])
        let chi (x u : String) : Option (ZBind × List String) := do
          let .pack w1 .and _ u1 u2 ← cur.get? u | none
          guard (w1 == w && free u)
          chiS x u u1 u2 <|> chiS x u u2 u1
        let x3 (u z : String) : Option (ZBind × List String) := do
          let .pack w1 .xor _ x y ← cur.get? u | none
          guard (w1 == w && reg x && reg y && reg z && free u)
          pure (.tern w (ternTable xor3B).toNat d x y z, [u])
        chi p q <|> chi q p <|> x3 p q <|> x3 q p
      | _ => none
    match fused with
    | some (z, rem) =>
      removed := rem.foldl (fun s n => s.insert n) removed
      cur := cur.insert z.dst z
      out := out.push z
    | none =>
      cur := cur.insert b.dst b
      out := out.push b
  return out.filter (fun b => !removed.contains b.dst)

/-- The owned AT&T text of the function `sym(out = %rdi, in = %rsi)` over the parameter
    names `names` and bindings `bs`: parameter `s` loaded from `inOffset s(%rsi)`, the
    body, and the `nOut` last bindings stored to `64·j(%rdi)`. With `ranges = some (B, arr)`
    every input lane is at most `B` and `arr` holds the verified interval of each binding
    (`ComRange.rangeAnalysisArray`); a 64-bit multiply whose operands they show below
    `2^32` renders as `vpmuludq`, a conditional add or subtract they show in range as an
    unsigned minimum. Up to four
    constants read as the first operand of a non-commutative operation are resident,
    loaded once at entry into the highest registers the allocation and the high-multiply
    temporaries leave free. The registers are those of `allocZmmLinear` when every
    parameter has its own register outside the reserved ones and that allocation
    succeeds; otherwise those of `allocZmmSpill`, whose parameter loads, spills and
    reloads precede the binding or output store they serve and whose stack frame is
    allocated after the label and released before `vzeroupper`. With `ymm` the same
    instructions are printed on the 256-bit
    registers `%ymm0..31` (mode `Mode.ymm`: four 64-bit lanes, outputs 32 bytes apart,
    `{1to4}` broadcasts); every instruction the renderer emits for a 64-bit-lane program is
    lane-wise, so its lanes 0..3 are those of the 512-bit form. The 256-bit form of a
    program with 32-bit lanes or a high multiply is an error. -/
def renderZmmLinearBinds (sym : String) (inOffset : Nat → Nat) (nOut : Nat)
    (names : List String) (bs0 : Array ZBind) (ranges : Option (Nat × Array Iv) := none)
    (ymm : Bool := false) : Except String String := do
  let md : Mode := if ymm then .ymm else .zmm
  let outStride := md.stride
  let (consts, pool) := constTable sym bs0
  let info : RangeInfo := match ranges with
    | some (B, arr) => rangeInfoOf consts names B arr bs0
    | none => {}
  let csubOk (w : LaneW) (d : String) (c : Nat) : Bool :=
    match info.iv.get? d with
    | some i => (ivCondAdd? w.bits i (constLaneIv w c)).isSome
    | none => false
  let bs1 := csubToMinu consts csubOk bs0
  let keep : Std.HashSet String :=
    (bs1.toList.drop (bs1.size - nOut)).foldl (fun s b => s.insert b.dst) {}
  let bs := fuseTern consts keep (fuseRol consts keep
    (fuseMulHiLo consts (fuseMontSub consts keep bs1)))
  let outs := ((bs.toList.drop (bs.size - nOut)).map ZBind.dst)
  let hasMulhi := bs.any (fun b =>
    match b with
    | .mulhi _ _ _ => true | .mulhilo _ _ _ _ => true | .montsub _ _ _ _ _ => true
    | _ => false)
  let temps := if hasMulhi then mulhiTemps md else []
  let top := 30 - temps.length
  let firstConsts : List (LaneW × (String × Nat)) := (bs.toList.filterMap (fun b =>
    match b with
    | .pack w bop _ a _ => if bopCommutes bop then none else (consts.get? a).map (w, ·)
    | .mulhi _ a b => ((consts.get? b) <|> (consts.get? a)).map (LaneW.d, ·)
    | .mulhilo _ _ _ b => (consts.get? b).map (LaneW.d, ·)
    | .montsub _ _ b _ _ => (consts.get? b).map (LaneW.d, ·)
    | _ => none)).eraseDups.take 4
  let residentList : List ((LaneW × (String × Nat)) × String) :=
    firstConsts.zipIdx.map (fun (c, i) => (c, vecReg md (top - i)))
  let resident : Std.HashMap String String :=
    residentList.foldl (fun m (c, r) => m.insert c.2.1 r) {}
  let reserved := temps ++ residentList.map (·.2)
  let pinnedOK := names.length ≤ 31 &&
    (List.range names.length).all (fun i => !reserved.contains (vecReg md i))
  let alloc? := if pinnedOK then allocZmmLinear md names consts bs outs reserved
    else .error "parameters exceed the registers"
  let maskSetup := if hasMulhi then
    ["\tmovl $43690, %eax", "\tkmovw %eax, %k1", "\tmovl $21845, %eax", "\tkmovw %eax, %k2"]
    else []
  let residentLoads := residentList.map (fun (c, r) => constLoadTo c.1 c.2 r)
  let storeLines (alloc : Std.HashMap String String) (o : String) (j : Nat) :
      Except String (List String) :=
    match alloc.get? o, consts.get? o with
    | some r, _ => pure ["\tvmovdqu64 " ++ r ++ ", " ++ toString (outStride * j) ++ "(%rdi)"]
    | none, some c => pure ["\tvmovdqu64 " ++ c.1 ++ "(%rip), " ++ scratchReg md,
        "\tvmovdqu64 " ++ scratchReg md ++ ", " ++ toString (outStride * j) ++ "(%rdi)"]
    | none, none => throw s!"vpackZMM linear render: unallocated output {o}"
  let code : List String ← match alloc? with
    | .ok alloc => do
      let loads := names.zipIdx.map (fun (_, s) =>
        "\tvmovdqu64 " ++ toString (inOffset s) ++ "(%rsi), " ++ vecReg md s)
      let body ← bs.foldlM
        (fun (acc : Array String) b => do
          pure (acc ++ (← bindLines md consts alloc info.narrow resident b).toArray)) #[]
      let stores ← outs.zipIdx.mapM (fun (o, j) => storeLines alloc o j)
      pure (loads ++ maskSetup ++ residentLoads ++ body.toList ++ stores.flatten)
    | .error _ => do
      let (plan, frame) ← allocZmmSpill md inOffset names consts bs outs reserved
      let body ← bs.zipIdx.foldlM
        (fun (acc : Array String) (b, i) => do
          let (mv, alloc) := plan.getD i ([], {})
          pure (acc ++ mv.toArray ++
            (← bindLines md consts alloc info.narrow resident b).toArray)) #[]
      let stores ← outs.zipIdx.mapM (fun (o, j) => do
        let (mv, alloc) := plan.getD (bs.size + j) ([], {})
        pure (mv ++ (← storeLines alloc o j)))
      let (enter, leave) := if frame = 0 then ([], [])
        else (["\tsubq $" ++ toString frame ++ ", %rsp"], ["\taddq $" ++ toString frame ++ ", %rsp"])
      pure (enter ++ maskSetup ++ residentLoads ++ body.toList ++ stores.flatten ++ leave)
  let text : List String :=
    ["\t.text", "\t.globl " ++ sym, "\t.type " ++ sym ++ ", @function", sym ++ ":"]
      ++ code
      ++ ["\tvzeroupper", "\tret"]
      ++ ["\t.size " ++ sym ++ ", .-" ++ sym] ++ pool.sectionLines
      ++ ["\t.section .note.GNU-stack,\"\",@progbits"]
  let body := String.intercalate "\n" text ++ "\n"
  if ymm && (hasMulhi || bs.any (fun b =>
      match b with | .pack .d _ _ _ _ => true | .shi .d _ _ _ _ => true | _ => false))
  then throw "vpackZMM linear render: the 256-bit form covers 64-bit-lane programs only"
  pure body

/-- The owned function text of the packed program `com` (`renderZmmLinearBinds` over
    its bindings). -/
def renderZmmLinearFunction {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (sym : String) (inOffset : Nat → Nat) (nOut : Nat) (com : Com jasminDialect Γ t) :
    Except String String :=
  let (params, vm) := paramsAndMap Γ
  renderZmmLinearBinds sym inOffset nOut (params.map (fun p => p.var.var.vname))
    (collectZBinds vm 0 #[] com).1

/-- The owned function text of `LaneMapZmm.laneMapZmm c`, eight lanes of the scalar
    64-bit program `c` per ZMM register, rendered from `c` in one pass by
    `collectZBindsScalar` without building the widened `Com`. With `inBound = some B` the range
    facts come from `ComRange.rangeAnalysis` of `c` with every input in `[0, B]`. -/
def renderLaneMapZmmFunction {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (sym : String) (inOffset : Nat → Nat) (nOut : Nat) (c : Com jasminDialect Γ t)
    (inBound : Option Nat := none)
    (ymm : Bool := false) : Except String String :=
  let (params, vm) := paramsAndMap Γ
  renderZmmLinearBinds sym inOffset nOut (params.map (fun p => p.var.var.vname))
    (collectZBindsScalar vm 0 #[] c).1
    (inBound.map (fun B => (B, ComRange.rangeAnalysisArray (ivsConst (0, Int.ofNat B) Γ) c)))
    ymm

/-- The owned function text of the 32-bit lane map of `c`, sixteen lanes of the scalar
    32-bit program `c` per ZMM register, rendered from `c` in one pass by
    `collectZBindsScalar32`. -/
def renderLaneMapZmmDFunction {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (sym : String) (inOffset : Nat → Nat) (nOut : Nat) (c : Com jasminDialect Γ t)
    (inBound : Option Nat := none) :
    Except String String :=
  let (params, vm) := paramsAndMap Γ
  renderZmmLinearBinds sym inOffset nOut (params.map (fun p => p.var.var.vname))
    (collectZBindsScalar32 vm 0 #[] c).1
    (inBound.map (fun B => (B, ComRange.rangeAnalysisArray (ivsConst (0, Int.ofNat B) Γ) c)))

/-! ## 4. A static check -/

/- The butterfly `hi` slice (`prod := w ⊙ b`, `hi := a + prod` over `[w, a, b]`)
    renders with `w, a, b` in `%zmm0..2`, the product in `%zmm3` and the sum in
    `%zmm4`, released registers returning to the tail of the free list. A static
    check on the allocation and the frame. -/
open CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockCom (butterflyHiCom) in
#kat (renderZmmLinearFunction "bfly" (fun s => 64 * s) 1 butterflyHiCom).toOption.map
    (fun s => (s.splitOn "\n").take 9)
  == some ["\t.text", "\t.globl bfly", "\t.type bfly, @function", "bfly:",
    "\tvmovdqu64 0(%rsi), %zmm0", "\tvmovdqu64 64(%rsi), %zmm1",
    "\tvmovdqu64 128(%rsi), %zmm2", "\tvpmullq %zmm2, %zmm0, %zmm3",
    "\tvpaddq %zmm3, %zmm1, %zmm4"]

/-- A 64-bit-lane binding list with an immediate shift, a resident constant first operand
    of a subtract and a broadcast memory operand: `((a·b) >> 3)` subtracted from the
    broadcast `5`, plus `5`. -/
def ymmCheckBinds : Array ZBind := #[
  .const "v0" (bcast512 3), .const "v1" (bcast512 5),
  .pack .q .mul "v2" "a" "b", .pack .q .shr "v3" "v2" "v0",
  .pack .q .sub "v4" "v1" "v3", .pack .q .add "v5" "v4" "v1"]

/- The `%ymm` render of `ymmCheckBinds` is its `%zmm` render with every `%zmm` register
   name read as `%ymm` and every `{1to8}` broadcast as `{1to4}`. -/
#kat (renderZmmLinearBinds "g" (fun s => 32 * s) 1 ["a", "b"] ymmCheckBinds).toOption.isSome &&
  (renderZmmLinearBinds "g" (fun s => 32 * s) 1 ["a", "b"] ymmCheckBinds (ymm := true)).toOption
    == (renderZmmLinearBinds "g" (fun s => 32 * s) 1 ["a", "b"] ymmCheckBinds).toOption.map
      (fun s => (s.replace "%zmm" "%ymm").replace "{1to8}" "{1to4}")


end CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmLinearRender
