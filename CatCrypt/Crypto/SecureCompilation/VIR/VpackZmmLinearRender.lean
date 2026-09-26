/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmm
public import CatCryptCore.Tactics.KatGuard
public import Std.Data.HashMap

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
scratch register `%zmm31`. The high multiply renders as `vpmuludq` on the even and on
the odd lanes, combined by `vpblendmd` under the mask `%k1`, over the temporaries
`%zmm28..30`.

The function frame follows the two-pointer SysV ABI `f(out = %rdi, in = %rsi)`:
parameter `s` (head first) is loaded from `inOffset s(%rsi)`, and the `nOut` last
bindings are stored to `64·j(%rdi)` in binding order, the output convention of
`JasminLprogExport.outStoreSlots`.

## Main definitions

* `ZBind`, `collectZBinds`, `collectZBindsScalar`: the straight-line binding list.
* `csubToMinu`: the conditional add or subtract of a constant as an unsigned minimum.
* `allocZmmLinear`: the linear-scan allocation, failing when no register is free.
* `renderZmmLinearFunction`, `renderLaneMapZmmFunction`, `renderLaneMapZmmDFunction`:
  the owned AT&T function text.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmLinearRender

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (VarMap argName paramsAndMap)

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
    sixteen-lane high multiply, a 512-bit constant, an unsigned lane-wise minimum, or
    any other operation (which the renderer rejects). -/
inductive ZBind where
  | pack (w : LaneW) (bop : JasminBinOp) (dst a b : String)
  | mulhi (dst a b : String)
  | const (dst : String) (v : Nat)
  | minu (w : LaneW) (dst a b : String)
  | other (dst : String)

/-- The name a binding defines. -/
def ZBind.dst : ZBind → String
  | .pack _ _ d _ _ => d
  | .mulhi d _ _ => d
  | .const d _ => d
  | .minu _ d _ _ => d
  | .other d => d

/-- The names a binding reads. -/
def ZBind.srcs : ZBind → List String
  | .pack _ _ _ a b => [a, b]
  | .mulhi _ a b => [a, b]
  | .minu _ _ a b => [a, b]
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
    is the broadcast constant `constZmm k`, and every other operation is outside the
    fragment. -/
def exprZBindScalar {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (vm : VarMap Γ)
    (e : Expr jasminDialect Γ t) (dst : String) : ZBind :=
  match e.op with
  | .regArith bop w =>
      if w = 64 then .pack .q bop dst (argName vm e.args 0) (argName vm e.args 1)
      else .other dst
  | .regConst w k =>
      if w = 64 then .const dst (KeccakThetaPiAbstractCom.constZmm k).toNat else .other dst
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

/-- The constants of a binding list: each constant binding's name mapped to the data
    label and value it reads, one assembler-local (`.L`) label per distinct value, and
    the data entries in label order. -/
def constTable (sym : String) (bs : Array ZBind) :
    Std.HashMap String (String × Nat) × Array (String × Nat) :=
  let (names, _, data) := bs.foldl
    (fun (acc : Std.HashMap String (String × Nat) × Std.HashMap Nat String ×
        Array (String × Nat)) b =>
      let (names, byVal, data) := acc
      match b with
      | .const d v =>
        match byVal.get? v with
        | some lbl => (names.insert d (lbl, v), byVal, data)
        | none =>
          let lbl := ".L" ++ sym ++ "_c" ++ toString data.size
          (names.insert d (lbl, v), byVal.insert v lbl, data.push (lbl, v))
      | _ => acc)
    ({}, {}, #[])
  (names, data)

/-- The index of the last binding reading each name; the names in `live` are read at
    index `bs.size`, past the last binding. -/
def lastUses (bs : Array ZBind) (live : List String) : Std.HashMap String Nat :=
  let m := bs.zipIdx.foldl
    (fun m (b, i) => b.srcs.foldl (fun m s => m.insert s i) m) ({} : Std.HashMap String Nat)
  live.foldl (fun m s => m.insert s bs.size) m

/-- The `%zmm` register numbered `i`. -/
def zmmName (i : Nat) : String := "%zmm" ++ toString i

/-- The scratch register a constant operand is loaded into; never allocated. -/
def zmmScratch : String := "%zmm31"

/-- The temporaries of the high-multiply expansion; never allocated when the program
    contains a high multiply. -/
def mulhiTemps : List String := ["%zmm28", "%zmm29", "%zmm30"]

/-- Linear-scan allocation of `%zmm0..30` less `reserved` over the non-constant values:
    parameter `i` is pinned to `%zmm i`; at each binding the registers of the names it
    reads for the last time are released before its destination is assigned, and the
    destination's register is released at once when nothing reads it. Constants take no
    register. Fails when a binding finds no free register. -/
def allocZmmLinear (params : List String) (consts : Std.HashMap String (String × Nat))
    (bs : Array ZBind) (live : List String) (reserved : List String := []) :
    Except String (Std.HashMap String String) := do
  let lu := lastUses bs live
  let pinned : Std.HashMap String String :=
    params.zipIdx.foldl (fun m (p, i) => m.insert p (zmmName i)) {}
  let pool : List String :=
    (((List.range 31).drop params.length).map zmmName).filter (fun r => !reserved.contains r)
  let step (st : Std.HashMap String String × List String) (bi : ZBind × Nat) :
      Except String (Std.HashMap String String × List String) := do
    let (alloc, free) := st
    let (b, i) := bi
    if consts.contains b.dst then pure (alloc, free) else
    let dying := b.srcs.eraseDups.filter (fun s => lu.get? s == some i)
    let free := free ++ dying.filterMap alloc.get?
    match free with
    | [] => throw s!"vpackZMM linear render: no free register at binding {i}"
    | r :: rest =>
      let alloc := alloc.insert b.dst r
      pure (alloc, if lu.contains b.dst then rest else rest ++ [r])
  let (alloc, _) ← bs.zipIdx.foldlM step (pinned, pool)
  pure alloc

/-! ## 3. Rendering -/

/-- Whether a 512-bit value is the broadcast of one lane of width `w`. -/
def isBcast (w : LaneW) (v : Nat) : Bool :=
  match w with
  | .q => bcast512 v == v
  | .d => bcast512d v == v

/-- The `.rodata` lines of the constant labelled `lbl` with value `v`: one 8-byte word
    when its eight 64-bit lanes are equal (which covers every sixteen-lane broadcast,
    whose word repeats the 32-bit lane), else the 64-byte value. -/
def constData (lbl : String) (v : Nat) : List String :=
  if bcast512 v = v then
    ["\t.p2align 3", lbl ++ ":", "\t.quad " ++ toString (v % 2 ^ 64)]
  else
    ["\t.p2align 6", lbl ++ ":"]
      ++ (List.range 8).map (fun j => "\t.quad " ++ toString ((v / 2 ^ (64 * j)) % 2 ^ 64))

/-- The memory operand of a constant read by a width-`w` operation: an embedded
    broadcast of its lane, or its 64-byte value. -/
def constOperand (w : LaneW) (c : String × Nat) : String :=
  if isBcast w c.2 then
    c.1 ++ "(%rip)" ++ (match w with | .q => "{1to8}" | .d => "{1to16}")
  else c.1 ++ "(%rip)"

/-- The line loading a constant read by a width-`w` operation into register `r`. -/
def constLoadTo (w : LaneW) (c : String × Nat) (r : String) : String :=
  if isBcast w c.2 then
    (match w with | .q => "\tvpbroadcastq " | .d => "\tvpbroadcastd ") ++ c.1 ++ "(%rip), " ++ r
  else "\tvmovdqu64 " ++ c.1 ++ "(%rip), " ++ r

/-- The line loading a constant into `zmmScratch`. -/
def constLoad (w : LaneW) (c : String × Nat) : String := constLoadTo w c zmmScratch

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

/-- The sixteen-lane high multiply of `ra` and `rb` into `rd`: `vpmuludq` on the even
    lanes, the odd lanes shifted down and multiplied, the even high words shifted down,
    and the two blended under `%k1` (odd lanes set). When `rb` holds a sixteen-lane
    broadcast (`rbBcast`) its odd lanes equal its even lanes and it is not shifted. -/
def mulhiLines (rd ra rb : String) (rbBcast : Bool := false) : List String :=
  let t0 := "%zmm28"; let t1 := "%zmm29"; let t2 := "%zmm30"
  [ opLine "vpmuludq" t0 ra rb
  , "\tvpsrlq $32, " ++ ra ++ ", " ++ t1 ]
  ++ (if rbBcast then [] else ["\tvpsrlq $32, " ++ rb ++ ", " ++ t2]) ++
  [ opLine "vpmuludq" t1 t1 (if rbBcast then rb else t2)
  , "\tvpsrlq $32, " ++ t0 ++ ", " ++ t0
  , "\tvpblendmd " ++ t1 ++ ", " ++ t0 ++ ", " ++ rd ++ "{%k1}" ]

/-- The instruction lines of binding `b`. A constant second operand is a memory
    operand; a constant first operand is exchanged with a register second operand when
    `bop` commutes, and otherwise read from its resident register or loaded into
    `zmmScratch`; a shift by a broadcast constant below the lane width uses the
    immediate form. Constant bindings emit nothing. -/
def bindLines (consts : Std.HashMap String (String × Nat))
    (alloc : Std.HashMap String String) (mulU : Bool := false)
    (resident : Std.HashMap String String := {}) :
    ZBind → Except String (List String)
  | .const _ _ => pure []
  | .other d => throw s!"vpackZMM linear render: binding {d} is not a packed op or constant"
  | .minu w d a b =>
      match alloc.get? d, alloc.get? a, alloc.get? b with
      | some rd, some ra, some rb =>
        pure [opLine (match w with | .q => "vpminuq" | .d => "vpminud") rd ra rb]
      | _, _, _ => throw s!"vpackZMM linear render: unallocated operand at {d}"
  | .mulhi d a b => do
      let reg (n : String) : Except String String :=
        match alloc.get? n with
        | some r => pure r
        | none => throw s!"vpackZMM linear render: unallocated operand {n} at {d}"
      let rd ← reg d
      let constReg (c : String × Nat) : List String × String :=
        match resident.get? c.1 with
        | some r => ([], r)
        | none => ([constLoad .d c], zmmScratch)
      match consts.get? a, consts.get? b with
      | none, none => pure (mulhiLines rd (← reg a) (← reg b))
      | none, some cb =>
        let (ls, r) := constReg cb
        pure (ls ++ mulhiLines rd (← reg a) r (isBcast .d cb.2))
      | some ca, none =>
        let (ls, r) := constReg ca
        pure (ls ++ mulhiLines rd (← reg b) r (isBcast .d ca.2))
      | some ca, some cb =>
        pure (constLoad .d ca :: constLoadTo .d cb "%zmm30" :: mulhiLines rd zmmScratch "%zmm30")
  | .pack w bop d a b => do
      let reg (n : String) : Except String String :=
        match alloc.get? n with
        | some r => pure r
        | none => throw s!"vpackZMM linear render: unallocated operand {n} at {d}"
      let rd ← reg d
      let mn := packMnemonic w mulU bop
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
        | none => pure [opLine mn rd ra (constOperand w cb)]
      | some ca, none =>
        let rb ← reg b
        if bopCommutes bop then pure [opLine mn rd rb (constOperand w ca)]
        else match resident.get? ca.1 with
          | some r => pure [opLine mn rd r rb]
          | none => pure [constLoad w ca, opLine mn rd zmmScratch rb]
      | some ca, some cb =>
        match shiftImm cb zmmScratch with
        | some line => pure [constLoad w ca, line]
        | none => pure [constLoad w ca, opLine mn rd zmmScratch (constOperand w cb)]

/-- The conditional add or subtract of a constant `C` that the BabyBear blocks emit,
    `r = d + ((0 - (d >> (L-1))) & C)` at lane width `L`, rewritten to an unsigned
    minimum when the three intermediate values have no other reader: to
    `r = minu(x, d)` when `d = x - C` and `d` has exactly the two readers, and otherwise
    to `u = d + C; r = minu(d, u)`. The two agree on every lane where `d` is below
    `2^(L-1)` or at least `2^L - C` and `C < 2^(L-1)` (the ranges the blocks produce on
    reduced inputs); on other lanes they differ, so the caller asserts the range. -/
def csubToMinu (consts : Std.HashMap String (String × Nat)) (bs : Array ZBind) :
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

/-- The owned AT&T text of the function `sym(out = %rdi, in = %rsi)` over the parameter
    names `names` and bindings `bs`: parameter `s` loaded from `inOffset s(%rsi)`, the
    body, and the `nOut` last bindings stored to `64·j(%rdi)`. With `fieldRange` the caller
    asserts that every value a 64-bit multiply reads is below `2^32` and that the
    conditional adds and subtracts read values in the ranges `csubToMinu` states; 64-bit
    multiplies then render as `vpmuludq` and those idioms as unsigned minima. Up to four
    constants read as the first operand of a non-commutative operation are resident,
    loaded once at entry into the highest registers the allocation and the high-multiply
    temporaries leave free. -/
def renderZmmLinearBinds (sym : String) (inOffset : Nat → Nat) (nOut : Nat)
    (names : List String) (bs0 : Array ZBind) (fieldRange : Bool := false) :
    Except String String := do
  let (consts, data) := constTable sym bs0
  let bs := if fieldRange then csubToMinu consts bs0 else bs0
  let outs := ((bs.toList.drop (bs.size - nOut)).map ZBind.dst)
  let hasMulhi := bs.any (fun b => match b with | .mulhi _ _ _ => true | _ => false)
  let temps := if hasMulhi then mulhiTemps else []
  let top := 30 - temps.length
  let firstConsts : List (LaneW × (String × Nat)) := (bs.toList.filterMap (fun b =>
    match b with
    | .pack w bop _ a _ => if bopCommutes bop then none else (consts.get? a).map (w, ·)
    | .mulhi _ a b => ((consts.get? b) <|> (consts.get? a)).map (LaneW.d, ·)
    | _ => none)).eraseDups.take 4
  let residentList : List ((LaneW × (String × Nat)) × String) :=
    firstConsts.zipIdx.map (fun (c, i) => (c, zmmName (top - i)))
  let resident : Std.HashMap String String :=
    residentList.foldl (fun m (c, r) => m.insert c.2.1 r) {}
  let alloc ← allocZmmLinear names consts bs outs (temps ++ residentList.map (·.2))
  let loads := names.zipIdx.map (fun (_, s) =>
    "\tvmovdqu64 " ++ toString (inOffset s) ++ "(%rsi), " ++ zmmName s)
  let maskSetup := if hasMulhi then ["\tmovl $43690, %eax", "\tkmovw %eax, %k1"] else []
  let residentLoads := residentList.map (fun (c, r) => constLoadTo c.1 c.2 r)
  let body ← bs.foldlM
    (fun (acc : Array String) b => do
      pure (acc ++ (← bindLines consts alloc fieldRange resident b).toArray)) #[]
  let stores ← outs.zipIdx.mapM (fun (o, j) =>
    match alloc.get? o, consts.get? o with
    | some r, _ => pure ["\tvmovdqu64 " ++ r ++ ", " ++ toString (64 * j) ++ "(%rdi)"]
    | none, some c => pure ["\tvmovdqu64 " ++ c.1 ++ "(%rip), " ++ zmmScratch,
        "\tvmovdqu64 " ++ zmmScratch ++ ", " ++ toString (64 * j) ++ "(%rdi)"]
    | none, none => throw s!"vpackZMM linear render: unallocated output {o}")
  let text : List String :=
    ["\t.text", "\t.globl " ++ sym, "\t.type " ++ sym ++ ", @function", sym ++ ":"]
      ++ loads ++ maskSetup ++ residentLoads ++ body.toList ++ stores.flatten
      ++ ["\tvzeroupper", "\tret"]
      ++ ["\t.size " ++ sym ++ ", .-" ++ sym, "\t.section .rodata"]
      ++ (data.toList.flatMap (fun (lbl, v) => constData lbl v))
      ++ ["\t.section .note.GNU-stack,\"\",@progbits"]
  pure (String.intercalate "\n" text ++ "\n")

/-- The owned function text of the packed program `com` (`renderZmmLinearBinds` over
    its bindings). -/
def renderZmmLinearFunction {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (sym : String) (inOffset : Nat → Nat) (nOut : Nat) (com : Com jasminDialect Γ t)
    (fieldRange : Bool := false) :
    Except String String :=
  let (params, vm) := paramsAndMap Γ
  renderZmmLinearBinds sym inOffset nOut (params.map (fun p => p.var.var.vname))
    (collectZBinds vm 0 #[] com).1 fieldRange

/-- The owned function text of `LaneMapZmm.laneMapZmm c`, eight lanes of the scalar
    64-bit program `c` per ZMM register, rendered from `c` in one pass by
    `collectZBindsScalar` without building the widened `Com`. -/
def renderLaneMapZmmFunction {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (sym : String) (inOffset : Nat → Nat) (nOut : Nat) (c : Com jasminDialect Γ t)
    (fieldRange : Bool := false) :
    Except String String :=
  let (params, vm) := paramsAndMap Γ
  renderZmmLinearBinds sym inOffset nOut (params.map (fun p => p.var.var.vname))
    (collectZBindsScalar vm 0 #[] c).1 fieldRange

/-- The owned function text of the 32-bit lane map of `c`, sixteen lanes of the scalar
    32-bit program `c` per ZMM register, rendered from `c` in one pass by
    `collectZBindsScalar32`. -/
def renderLaneMapZmmDFunction {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (sym : String) (inOffset : Nat → Nat) (nOut : Nat) (c : Com jasminDialect Γ t)
    (fieldRange : Bool := false) :
    Except String String :=
  let (params, vm) := paramsAndMap Γ
  renderZmmLinearBinds sym inOffset nOut (params.map (fun p => p.var.var.vname))
    (collectZBindsScalar32 vm 0 #[] c).1 fieldRange

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

end CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmLinearRender
