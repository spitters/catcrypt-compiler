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
# Linear-time owned `%zmm` rendering of a large `vpackZMM` program

`VpackZmmAsmPrint.renderVpackZmmComAutoZmm` renders a `vpackZMM` `Com` through
`VsimdAsmPrint.vsimdAutoAllocZmm`, whose linear scan recomputes each value's last use
by scanning the block and looks registers up in an association list: quadratic in the
number of bindings. It pins every parameter to a register and has no arm for
constants.

This module renders a straight-line `Com jasminDialect` whose bindings are
`vpackZMM` operations and 512-bit constants (`regConst 512 n`, the image of a scalar
constant under a lane-wise widening) in time linear in the binding count, apart from
the name lookups of `JasminPrint.VarMap`, which cost the de Bruijn distance of the
variable read. The last-use table and the register map are hash maps. Constants take
no register: each distinct value is one `.rodata` entry (an 8-byte word when its eight
lanes are equal, else 64 bytes), read as a memory operand of the operation that uses
it (`c(%rip){1to8}` for a broadcast word), a shift by a broadcast constant below 64
uses the immediate-count form, and a constant first operand of a non-commutative
operation is loaded into the scratch register `%zmm31`.

The function frame follows the two-pointer SysV ABI `f(out = %rdi, in = %rsi)`:
parameter `s` (head first) is loaded from `inOffset s(%rsi)`, and the `nOut` last
bindings are stored to `64·j(%rdi)` in binding order, the output convention of
`JasminLprogExport.outStoreSlots`.

## Main definitions

* `ZBind`, `collectZBinds`: the straight-line binding list of a `Com`.
* `allocZmmLinear`: the linear-scan allocation over `%zmm0..30`, failing when more
  than 31 values are live.
* `renderZmmLinearFunction`: the owned AT&T function text.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmLinearRender

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (VarMap argName paramsAndMap)
open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint (renderVpackZmmInstr)

/-! ## 1. The binding list -/

/-- One binding of a straight-line packed program: a `vpackZMM` operation, a 512-bit
    constant, or any other operation (which the renderer rejects). -/
inductive ZBind where
  | pack (bop : JasminBinOp) (dst a b : String)
  | const (dst : String) (v : Nat)
  | minu (dst a b : String)
  | other (dst : String)

/-- The name a binding defines. -/
def ZBind.dst : ZBind → String
  | .pack _ d _ _ => d
  | .const d _ => d
  | .minu d _ _ => d
  | .other d => d

/-- The names a binding reads. -/
def ZBind.srcs : ZBind → List String
  | .pack _ _ a b => [a, b]
  | .minu _ a b => [a, b]
  | _ => []

/-- The binding of expression `e` defining `dst`. -/
def exprZBind {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (vm : VarMap Γ)
    (e : Expr jasminDialect Γ t) (dst : String) : ZBind :=
  match e.op with
  | .vpackZMM bop => .pack bop dst (argName vm e.args 0) (argName vm e.args 1)
  | .regConst w n => if w = 512 then .const dst n else .other dst
  | _ => .other dst

/-- The bindings of a straight-line `Com` in order, with fresh names `v{next}`, and
    the name of its return value. Tail-recursive in the accumulator. -/
def collectZBinds {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (vm : VarMap Γ)
    (next : Nat) (acc : Array ZBind) : Com jasminDialect Γ t → Array ZBind × String
  | .ret v => (acc, vm t v)
  | .var (t := tEx) e body =>
      let dst := "v" ++ toString next
      collectZBinds (vm.extend (t := tEx) dst) (next + 1) (acc.push (exprZBind vm e dst)) body

/-- The binding the lane map `LaneMapZmm.laneMapZmm` gives the scalar expression `e`
    defining `dst`: `regArith bop 64` is the packed `vpackZMM bop`, `regConst 64 k` is
    the broadcast constant `constZmm k`, and every other operation is outside the
    fragment. -/
def exprZBindScalar {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (vm : VarMap Γ)
    (e : Expr jasminDialect Γ t) (dst : String) : ZBind :=
  match e.op with
  | .regArith bop w =>
      if w = 64 then .pack bop dst (argName vm e.args 0) (argName vm e.args 1) else .other dst
  | .regConst w k =>
      if w = 64 then .const dst (KeccakThetaPiAbstractCom.constZmm k).toNat else .other dst
  | _ => .other dst

/-- The bindings of `LaneMapZmm.laneMapZmm c` read off the scalar program `c` in one
    pass, without building the widened `Com`: one binding per scalar binding, in order,
    with the names `collectZBinds` gives the widened program. Tail-recursive in the
    accumulator. -/
def collectZBindsScalar {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (vm : VarMap Γ)
    (next : Nat) (acc : Array ZBind) : Com jasminDialect Γ t → Array ZBind × String
  | .ret v => (acc, vm t v)
  | .var (t := tEx) e body =>
      let dst := "v" ++ toString next
      collectZBindsScalar (vm.extend (t := tEx) dst) (next + 1)
        (acc.push (exprZBindScalar vm e dst)) body

/-! ## 2. Linear-scan allocation -/


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

/-- The scratch register a constant first operand is loaded into; never allocated. -/
def zmmScratch : String := "%zmm31"

/-- Linear-scan allocation of `%zmm0..30` over the non-constant values: parameter `i` is
    pinned to `%zmm i`; at each binding the registers of the names it reads for the last
    time are released before its destination is assigned, and the destination's
    register is released at once when nothing reads it. Constants take no register.
    Fails when a binding finds no free register. -/
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
    | [] => throw s!"vpackZMM linear render: more than 31 live values at binding {i}"
    | r :: rest =>
      let alloc := alloc.insert b.dst r
      pure (alloc, if lu.contains b.dst then rest else rest ++ [r])
  let (alloc, _) ← bs.zipIdx.foldlM step (pinned, pool)
  pure alloc

/-! ## 3. Rendering -/

/-- The eight-fold broadcast of a 64-bit word to 512 bits. -/
def bcast512 (w : Nat) : Nat :=
  (List.range 8).foldl (fun acc k => acc + (w % 2 ^ 64) * 2 ^ (64 * k)) 0

/-- The `.rodata` lines of the constant labelled `lbl` with value `v`: one 8-byte word
    when its eight lanes are equal, else the 64-byte value. -/
def constData (lbl : String) (v : Nat) : List String :=
  if bcast512 v = v then
    ["\t.p2align 3", lbl ++ ":", "\t.quad " ++ toString (v % 2 ^ 64)]
  else
    ["\t.p2align 6", lbl ++ ":"]
      ++ (List.range 8).map (fun j => "\t.quad " ++ toString ((v / 2 ^ (64 * j)) % 2 ^ 64))

/-- The memory operand of a constant: an embedded broadcast of its 8-byte word, or its
    64-byte value. -/
def constOperand (c : String × Nat) : String :=
  if bcast512 c.2 = c.2 then c.1 ++ "(%rip){1to8}" else c.1 ++ "(%rip)"

/-- The line loading a constant into `zmmScratch`. -/
def constLoad (c : String × Nat) : String :=
  if bcast512 c.2 = c.2 then "\tvpbroadcastq " ++ c.1 ++ "(%rip), " ++ zmmScratch
  else "\tvmovdqu64 " ++ c.1 ++ "(%rip), " ++ zmmScratch

/-- The packed operations whose operands may be exchanged. -/
def bopCommutes : JasminBinOp → Bool
  | .add | .mul | .and | .or | .xor => true
  | _ => false

/-- The immediate-count shift mnemonic of `bop`, for `shl` and `shr`. -/
def shiftImmMnemonic : JasminBinOp → Option String
  | .shl => some "vpsllq"
  | .shr => some "vpsrlq"
  | _ => none

/-- The mnemonic of `bop`: the packed operation of `VpackZmmAsmPrint`, except that a
    multiply is `vpmuludq` (the product of the low 32 bits of each lane) when `mulU`
    holds, which equals `vpmullq` on operands below `2^32`. -/
def packMnemonic (mulU : Bool) (bop : JasminBinOp) : String :=
  match bop with
  | .mul => if mulU then "vpmuludq" else VpackZmmAsmPrint.JasminBinOp.zmmAttMnemonic bop
  | _ => VpackZmmAsmPrint.JasminBinOp.zmmAttMnemonic bop

/-- The line `mn src2, src1, dst`. -/
def opLine (mn : String) (rd ra rb : String) : String :=
  "\t" ++ mn ++ " " ++ rb ++ ", " ++ ra ++ ", " ++ rd

/-- The instruction lines of binding `b`. A constant second operand is a memory
    operand; a constant first operand is exchanged with a register second operand when
    `bop` commutes, and otherwise loaded into `zmmScratch`; a shift by a broadcast
    constant below 64 uses the immediate form. Constant bindings emit nothing. -/
def bindLines (consts : Std.HashMap String (String × Nat))
    (alloc : Std.HashMap String String) (mulU : Bool := false)
    (resident : Std.HashMap String String := {}) :
    ZBind → Except String (List String)
  | .const _ _ => pure []
  | .minu d a b =>
      match alloc.get? d, alloc.get? a, alloc.get? b with
      | some rd, some ra, some rb => pure ["\tvpminuq " ++ rb ++ ", " ++ ra ++ ", " ++ rd]
      | _, _, _ => throw s!"vpackZMM linear render: unallocated operand at {d}"
  | .other d => throw s!"vpackZMM linear render: binding {d} is not a vpackZMM op or constant"
  | .pack bop d a b => do
      let reg (n : String) : Except String String :=
        match alloc.get? n with
        | some r => pure r
        | none => throw s!"vpackZMM linear render: unallocated operand {n} at {d}"
      let rd ← reg d
      let shiftImm (c : String × Nat) (src : String) : Option String :=
        match shiftImmMnemonic bop with
        | some mn => if bcast512 c.2 = c.2 ∧ c.2 % 2 ^ 64 < 64 then
            some ("\t" ++ mn ++ " $" ++ toString (c.2 % 2 ^ 64) ++ ", " ++ src ++ ", " ++ rd)
          else none
        | none => none
      match consts.get? a, consts.get? b with
      | none, none => pure [opLine (packMnemonic mulU bop) rd (← reg a) (← reg b)]
      | none, some cb =>
        let ra ← reg a
        match shiftImm cb ra with
        | some line => pure [line]
        | none => pure [opLine (packMnemonic mulU bop) rd ra (constOperand cb)]
      | some ca, none =>
        let rb ← reg b
        if bopCommutes bop then pure [opLine (packMnemonic mulU bop) rd rb (constOperand ca)]
        else match resident.get? ca.1 with
          | some r => pure [opLine (packMnemonic mulU bop) rd r rb]
          | none => pure [constLoad ca, opLine (packMnemonic mulU bop) rd zmmScratch rb]
      | some ca, some cb =>
        match shiftImm cb zmmScratch with
        | some line => pure [constLoad ca, line]
        | none => pure [constLoad ca, opLine (packMnemonic mulU bop) rd zmmScratch (constOperand cb)]

/-- The conditional subtract `r = d + ((0 - (d >> 63)) & C)` with `d = x - C`, which the
    BabyBear blocks emit, rewritten to `r = minu(x, d)` (`vpminuq`), when the three
    intermediate values have no other reader and `d` has exactly the two. On a lane with
    `x < 2^63` and `C < 2^63` both compute `x - C` if `x ≥ C` and `x` otherwise; on other
    lanes they differ, so the caller asserts the range. -/
def csubToMinu (consts : Std.HashMap String (String × Nat)) (bs : Array ZBind) :
    Array ZBind := Id.run do
  let defs : Std.HashMap String Nat := bs.zipIdx.foldl (fun m (b, i) => m.insert b.dst i) {}
  let uses : Std.HashMap String Nat :=
    bs.foldl (fun m b => b.srcs.foldl (fun m s => m.insert s (m.getD s 0 + 1)) m) {}
  let constVal (n : String) : Option Nat := (consts.get? n).map (·.2)
  let defOf (n : String) : Option ZBind := (defs.get? n).bind (fun i => bs[i]?)
  let used (n : String) : Nat := uses.getD n 0
  -- `(x, d, removed)` when `d + t` is the idiom
  let idiom (d t : String) : Option (String × String × List String) := do
    let .pack .and _ t1 t2 ← defOf t | none
    let (m, cC) ← if (constVal t2).isSome then some (t1, t2)
      else if (constVal t1).isSome then some (t2, t1) else none
    let c ← constVal cC
    let .pack .sub _ z s ← defOf m | none
    let .pack .shr _ d2 c63 ← defOf s | none
    let .pack .sub _ x cC2 ← defOf d | none
    if constVal z == some 0 && d2 == d && constVal c63 == some (bcast512 63)
        && constVal cC2 == some c && (constVal x).isNone
        && used s == 1 && used m == 1 && used t == 1 && used d == 2 then
      some (x, d, [s, m, t])
    else none
  let mut rw : Std.HashMap String ZBind := {}
  let mut removed : Std.HashSet String := {}
  for b in bs do
    match b with
    | .pack .add r a b2 =>
      match idiom a b2 <|> idiom b2 a with
      | some (x, d, rem) =>
        rw := rw.insert r (.minu r x d)
        removed := rem.foldl (fun s n => s.insert n) removed
      | none => pure ()
    | _ => pure ()
  return bs.filterMap (fun b =>
    if removed.contains b.dst then none else some ((rw.get? b.dst).getD b))

/-- The owned AT&T text of the function `sym(out = %rdi, in = %rsi)` over the parameter
    names `names` and bindings `bs`: parameter `s` loaded from `inOffset s(%rsi)`, the
    body, and the `nOut` last bindings stored to `64·j(%rdi)`. With `fieldRange` the caller
    asserts that every value a multiply reads is below `2^32` and every conditional-subtract
    input below `2^63`; multiplies then render as `vpmuludq` and conditional subtracts as
    `vpminuq` (`csubToMinu`). Up to four constants read as the first operand of a
    non-commutative operation are resident: loaded once at entry into `%zmm30`, `%zmm29`,
    …, which the allocation leaves free. -/
def renderZmmLinearBinds (sym : String) (inOffset : Nat → Nat) (nOut : Nat)
    (names : List String) (bs0 : Array ZBind) (fieldRange : Bool := false) :
    Except String String := do
  let (consts, data) := constTable sym bs0
  let bs := if fieldRange then csubToMinu consts bs0 else bs0
  let outs := ((bs.toList.drop (bs.size - nOut)).map ZBind.dst)
  let firstConsts : List (String × Nat) := (bs.toList.filterMap (fun b =>
    match b with
    | .pack bop _ a _ => if bopCommutes bop then none else consts.get? a
    | _ => none)).eraseDups.take 4
  let residentList : List ((String × Nat) × String) :=
    firstConsts.zipIdx.map (fun (c, i) => (c, zmmName (30 - i)))
  let resident : Std.HashMap String String :=
    residentList.foldl (fun m (c, r) => m.insert c.1 r) {}
  let alloc ← allocZmmLinear names consts bs outs (residentList.map (·.2))
  let loads := names.zipIdx.map (fun (_, s) =>
    "\tvmovdqu64 " ++ toString (inOffset s) ++ "(%rsi), " ++ zmmName s)
  let residentLoads := residentList.map (fun (c, r) =>
    (if bcast512 c.2 = c.2 then "\tvpbroadcastq " else "\tvmovdqu64 ") ++ c.1 ++ "(%rip), " ++ r)
  let body ← bs.foldlM
    (fun (acc : Array String) b => do
      pure (acc ++ (← bindLines consts alloc fieldRange resident b).toArray)) #[]
  let stores ← outs.zipIdx.mapM (fun (o, j) =>
    match alloc.get? o, consts.get? o with
    | some r, _ => pure ["\tvmovdqu64 " ++ r ++ ", " ++ toString (64 * j) ++ "(%rdi)"]
    | none, some c => pure [constLoad c,
        "\tvmovdqu64 " ++ zmmScratch ++ ", " ++ toString (64 * j) ++ "(%rdi)"]
    | none, none => throw s!"vpackZMM linear render: unallocated output {o}")
  let text : List String :=
    ["\t.text", "\t.globl " ++ sym, "\t.type " ++ sym ++ ", @function", sym ++ ":"]
      ++ loads ++ residentLoads ++ body.toList ++ stores.flatten ++ ["\tvzeroupper", "\tret"]
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
    program `c` per ZMM register, rendered from `c` in one pass by
    `collectZBindsScalar` without building the widened `Com`. -/
def renderLaneMapZmmFunction {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (sym : String) (inOffset : Nat → Nat) (nOut : Nat) (c : Com jasminDialect Γ t)
    (fieldRange : Bool := false) :
    Except String String :=
  let (params, vm) := paramsAndMap Γ
  renderZmmLinearBinds sym inOffset nOut (params.map (fun p => p.var.var.vname))
    (collectZBindsScalar vm 0 #[] c).1 fieldRange

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
