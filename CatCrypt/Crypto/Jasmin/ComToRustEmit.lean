/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiReturnCom

/-!
# Straight-line `Com jasminDialect` to Rust source

A printer from a straight-line program `Com jasminDialect Γ t` (or a multi-result
`MultiReturnCom jasminDialect Γ ts`) to the text of a Rust
function in the style of fiat-crypto's Rust output: one `let xN: T = …;` per word binding,
the full product through `u128`, carries as `u64` values `0`/`1`, array cells kept as
locals and written to the output array at the end.

Each binding prints what its denotation in `JasminDialect.jasminDenote` computes:

| op | Rust right-hand side (`T` the container type of the width) |
|---|---|
| `regArith add/sub/mul w` | `a.wrapping_add(b)`, `a.wrapping_sub(b)`, `a.wrapping_mul(b)` |
| `regArith and/or/xor/andn w` | `a & b`, `a \| b`, `a ^ b`, `!a & b` |
| `regArith shl/shr w` | `a << k` / `a >> k` for a known `k < w`, `0` for `k ≥ w`, guarded otherwise |
| `mulhi w` (`w ≤ 64`) | `(((a as u128) * (b as u128)) >> w) as T` |
| `addCarryLo w` | `a.wrapping_add(b).wrapping_add(c as T)` |
| `addCarryHi w` (`w ≤ 64`) | `(((a as u128) + (b as u128) + (c as u128)) >> w) as u64` |
| `castW w w'` | `a as T'` |
| `regConst w n` | the literal `n mod 2^w` |
| `select w` | `(0T.wrapping_sub(c as T) & a) \| (!0T.wrapping_sub(c as T) & b)` |
| `cmp c w`, `cmpImm c w n` | `((a op b) as u64)` |
| `shrImm`, `shlImm`, `sarImm`, `rorImm` | the immediate shift or rotate |
| `stackLoad w n` | the cell `k mod n` for a known index `k`, an indexed array literal otherwise |
| `stackStore w n` | for a known index no line, the cell replaced; otherwise a `let mut` array |

A width `w` is carried in `u8`, `u16`, `u32`, `u64` or `u128` when it is one of those, in
`u64` when `w < 64` (so a `reg 1` carry is a `u64` holding `0` or `1`) and in `u128` when
`64 < w < 128`; a result whose width is narrower than its container is masked. Any other op,
and any width outside `1 ≤ w ≤ 128`, prints a `compile_error!` line naming it, so the printer
is total on the op table and on `Com`.

Variables are resolved by de Bruijn position to the name of their binding (`xN` for the
`N`-th word binding, the parameter name for a context entry). A stack array of the context
is a Rust parameter `&[T; n]`; the output array is a parameter `&mut [T; n]`.

Two optional printing rules (`EmitOpts`) change the text and not the value: the
sign-extension rule prints the sequence `castW w w'; shlImm w' (w' - w); sarImm w' (w' - w)`
as the one cast `((a as iw) as iw') as uw'`, and the hoisting rule prints each constant as a
`const` item declared once at the top of the function.

No theorem relates the printed text to the `Com` or to its denotation.

## Main definitions

* `RVal`: what a context position holds in the printed function.
* `emitCom`: the bindings of a `Com` as Rust lines.
* `emitFn`: a whole `#[inline] pub fn` from a `Com` and the names of its context.
* `emitMRCom`: the bindings of a `MultiReturnCom` as Rust lines.
* `EmitOpts`: the sign-extension and constant-hoisting printing rules.
* `emitFnInPlace`: a `pub fn` over one `&mut` array from a `MultiReturnCom` whose context
  and results are registers of one width.
* `emitFnInPlaceSeq`: one such `pub fn` computing a list of `MultiReturnCom`s in sequence.
* `emitFnParts`: one `pub fn` computing several array-result `Com`s over one context, each
  written to its slice of the output array.
* `fileHead`: the generated-file comment and module attributes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.ComToRustEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Widths and literals -/

/-- The width of the Rust unsigned type that carries a `w`-bit register. -/
def contBits (w : Nat) : Nat :=
  if w = 8 ∨ w = 16 ∨ w = 32 then w else if w ≤ 64 then 64 else 128

/-- The Rust unsigned type that carries a `w`-bit register. -/
def contTy (w : Nat) : String := s!"u{contBits w}"

/-- Whether the printer carries the width `w`. -/
def widthOk (w : Nat) : Bool := 0 < w && w ≤ 128

/-- Lowercase hexadecimal literal `0x…` of `n`. -/
def hexLit (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- The expression `e` reduced to `w` bits when `w` is narrower than its container. -/
def masked (w : Nat) (e : String) : String :=
  if w < contBits w then s!"({e}) & {hexLit (2 ^ w - 1)}" else e

/-- A `compile_error!` invocation with the message `msg`. -/
def compileError (msg : String) : String :=
  s!"compile_error!(\"ComToRustEmit: {msg}\")"

/-! ## 2. Values of the context -/

/-- What a context position holds in the printed function: a word (its Rust expression,
    its width and its value when it is a known constant), a stack array (the Rust
    expression of each cell), or an expression that is neither. -/
inductive RVal where
  | word (e : String) (w : Nat) (k : Option Nat)
  | arr (w : Nat) (cells : List String)
  | other (e : String)

/-- The Rust expression of a word value. -/
def RVal.expr : RVal → String
  | .word e _ _ => e
  | .arr _ _ => compileError "a stack array used as a word"
  | .other e => e

/-- The known constant value of a word, if any. -/
def RVal.const? : RVal → Option Nat
  | .word _ _ k => k
  | _ => none

/-- The de Bruijn position of a variable. -/
def varIdx {Γ : Ctxt jasminDialect} {t : JasminTy} : Ctxt.Var Γ t → Nat
  | .here => 0
  | .there v => varIdx v + 1

/-- The de Bruijn positions of an argument vector. -/
def argIdxs {Γ : Ctxt jasminDialect} :
    {ts : List JasminTy} → HVector (fun t => Ctxt.Var Γ t) ts → List Nat
  | [], .nil => []
  | _ :: _, .cons v vs => varIdx v :: argIdxs vs

/-- The name of an op outside the table, for its `compile_error!` line. -/
def opName : JasminOp → String
  | .regArith _ w => s!"regArith at width {w}"
  | .stackLoad w n => s!"stackLoad {w} {n}"
  | .stackStore w n => s!"stackStore {w} {n}"
  | .castW w w' => s!"castW {w} {w'}"
  | .extCall name _ _ => s!"extCall {name}"
  | .regConst w n => s!"regConst {w} {n}"
  | .vpackZMM _ => "vpackZMM"
  | .vpackZMMd _ => "vpackZMMd"
  | .vprordZMM n => s!"vprordZMM {n}"
  | .vpslldq n => s!"vpslldq {n}"
  | .vpsrldq n => s!"vpsrldq {n}"
  | .vsimd op => s!"vsimd {op.mnemonic}"
  | .mulhi w => s!"mulhi {w}"
  | .addCarryLo w => s!"addCarryLo {w}"
  | .addCarryHi w => s!"addCarryHi {w}"
  | .rorImm w n => s!"rorImm {w} {n}"
  | .shrImm w n => s!"shrImm {w} {n}"
  | .sarImm w n => s!"sarImm {w} {n}"
  | .shlImm w n => s!"shlImm {w} {n}"
  | .select w => s!"select {w}"
  | .callN name _ _ => s!"callN {name}"
  | .vymm _ => "vymm"
  | .cmp _ w => s!"cmp {w}"
  | .cmpImm _ w n => s!"cmpImm {w} {n}"

/-! ## 3. One binding -/

/-- The Rust right-hand side of `regArith bop w` on `a`, `b`, where `kb` is the value of
    `b` when it is a known constant. -/
def binRhs (bop : JasminBinOp) (w : Nat) (a b : String) (kb : Option Nat) : String :=
  let shift (sym : String) (mask : Bool) : String :=
    match kb with
    | some k => if k < w then (if mask then masked w s!"{a} {sym} {k}" else s!"{a} {sym} {k}")
                else "0"
    | none =>
      let body := if mask then masked w s!"{a} {sym} {b}" else s!"{a} {sym} {b}"
      s!"if {b} < {w} \{ {body} } else \{ 0 }"
  match bop with
  | .add => masked w s!"{a}.wrapping_add({b})"
  | .sub => masked w s!"{a}.wrapping_sub({b})"
  | .mul => masked w s!"{a}.wrapping_mul({b})"
  | .and => s!"{a} & {b}"
  | .or => s!"{a} | {b}"
  | .xor => s!"{a} ^ {b}"
  | .andn => s!"!{a} & {b}"
  | .shl => shift "<<" true
  | .shr => shift ">>" false

/-- The Rust comparison operator of a condition code. -/
def cmpSym : JasminCmp → String
  | .eq => "=="
  | .ne => "!="
  | .ult => "<"
  | .ule => "<="
  | .ugt => ">"
  | .uge => ">="

/-- Printing rules that change the text of a binding but not the value it computes.

    * `sx`: the sign-extension rule. A widening `castW w w'` and a following
      `shlImm w' (w' - w)` of its result print no line: each is the expression
      `(a as uw')`, resp. `((a as uw') << (w' - w))`, at its uses. A `sarImm w' (w' - w)` of
      that shifted value prints the one cast `((a as iw) as iw') as uw'`, the sign extension
      of the `w`-bit word `a` to `w'` bits, which is what the three ops compute together.
      `w` and `w'` are widths of Rust integer types.
    * `hoist`: a `regConst w n` prints no line; its value is a `const` item `Kw_HEX` declared
      once per width and value at the top of the function. -/
structure EmitOpts where
  sx : Bool := false
  hoist : Bool := false

/-- A value printed as an expression by the sign-extension rule: the expression `expr`, the
    source word `src` of width `w0` widened to `w`, and whether it is shifted left by
    `w - w0`. -/
structure SxPending where
  expr : String
  src : String
  w0 : Nat
  w : Nat
  shifted : Bool

/-- The printer's state: the values of the context (head at de Bruijn position `0`), the
    lines printed so far, the index of the next word binding, the printing rules, the
    hoisted constants (width, value) and the last value of the sign-extension rule. -/
structure PState where
  env : List RVal
  lines : Array String
  next : Nat
  opts : EmitOpts := {}
  consts : Array (Nat × Nat) := #[]
  sxLast : Option SxPending := none

/-- The name of the hoisted constant of value `k` at width `w`. -/
def constName (w k : Nat) : String :=
  s!"K{w}_{(String.ofList (Nat.toDigits 16 k)).toUpper}"

/-- The `const` items of the hoisted constants. -/
def PState.constLines (s : PState) : List String :=
  s.consts.toList.map fun (w, k) => s!"    const {constName w k}: {contTy w} = {hexLit k};"

/-- Whether `w` is the width of a Rust integer type of at most 64 bits. -/
def sxWidth (w : Nat) : Bool := contBits w == w && w ≤ 64

/-- The value at de Bruijn position `i`. -/
def PState.look (s : PState) (i : Nat) : RVal :=
  s.env.getD i (.other (compileError s!"unbound variable at position {i}"))

/-- Print `let xN: T = rhs;` for a `w`-bit word with known value `k`. -/
def PState.bindWord (s : PState) (w : Nat) (rhs : String) (k : Option Nat := none) :
    PState × RVal :=
  let name := s!"x{s.next}"
  ({ s with lines := s.lines.push s!"    let {name}: {contTy w} = {rhs};", next := s.next + 1 },
   .word name w k)

/-- Print the `compile_error!` line of an op outside the table. -/
def PState.unsupported (s : PState) (what : String) : PState × RVal :=
  let e := compileError s!"op outside the table: {what}"
  ({ s with lines := s.lines.push s!"    {e};" }, .other e)

/-- Print the binding of `op` applied to the context positions `args`. -/
def emitExpr (op : JasminOp) (args : List Nat) (s : PState) : PState × RVal :=
  let v (i : Nat) : RVal := s.look (args.getD i 0)
  let e (i : Nat) : String := (v i).expr
  if !(match op with
      | .regArith _ w | .stackLoad w _ | .stackStore w _ | .regConst w _ | .mulhi w
      | .addCarryLo w | .addCarryHi w | .rorImm w _ | .shrImm w _ | .sarImm w _
      | .shlImm w _ | .select w | .cmp _ w | .cmpImm _ w _ => widthOk w
      | .castW w w' => widthOk w && widthOk w'
      | _ => true) then
    s.unsupported (opName op)
  else
  match op with
  | .regArith bop w => s.bindWord w (binRhs bop w (e 0) (e 1) (v 1).const?)
  | .regConst w n =>
      let k := n % 2 ^ w
      if s.opts.hoist then
        let cs := if s.consts.contains (w, k) then s.consts else s.consts.push (w, k)
        ({ s with consts := cs }, .word (constName w k) w (some k))
      else s.bindWord w (hexLit k) (some k)
  | .mulhi w =>
      if w ≤ 64 then
        s.bindWord w s!"((({e 0} as u128) * ({e 1} as u128)) >> {w}) as {contTy w}"
      else s.unsupported (opName op)
  | .addCarryLo w =>
      let c := if contTy w = "u64" then e 2 else s!"({e 2} as {contTy w})"
      s.bindWord w (masked w s!"{e 0}.wrapping_add({e 1}).wrapping_add({c})")
  | .addCarryHi w =>
      if w ≤ 64 then
        s.bindWord 1 s!"((({e 0} as u128) + ({e 1} as u128) + ({e 2} as u128)) >> {w}) as u64"
      else s.unsupported (opName op)
  | .castW w w' =>
      let k := (v 0).const?.map (· % 2 ^ w')
      if s.opts.sx && sxWidth w && sxWidth w' && w < w' && k.isNone then
        let ex := s!"({e 0} as {contTy w'})"
        ({ s with sxLast := some { expr := ex, src := e 0, w0 := w, w := w', shifted := false } },
         .word ex w' none)
      else if contBits w = contBits w' then s.bindWord w' (masked w' (e 0)) k
      else s.bindWord w' (masked w' s!"{e 0} as {contTy w'}") k
  | .select w =>
      let c := if contTy w = "u64" then e 0 else s!"{e 0} as {contTy w}"
      let m := s!"0{contTy w}.wrapping_sub({c})"
      s.bindWord w s!"({m} & {e 1}) | (!{m} & {e 2})"
  | .cmp c _ => s.bindWord 1 s!"({e 0} {cmpSym c} {e 1}) as u64"
  | .cmpImm c w n => s.bindWord 1 s!"({e 0} {cmpSym c} {hexLit (n % 2 ^ w)}) as u64"
  | .shrImm w n => s.bindWord w (if n < w then s!"{e 0} >> {n}" else "0")
  | .shlImm w n =>
      let plain := s.bindWord w (if n < w then masked w s!"{e 0} << {n}" else "0")
      match s.sxLast with
      | some p =>
          if s.opts.sx && p.expr == e 0 && !p.shifted && p.w == w && n + p.w0 == w then
            let ex := s!"({p.expr} << {n})"
            ({ s with sxLast := some { p with expr := ex, shifted := true } }, .word ex w none)
          else plain
      | none => plain
  | .sarImm w n =>
      let sx? : Option SxPending := match s.sxLast with
        | some p =>
            if s.opts.sx && p.expr == e 0 && p.shifted && p.w == w && n + p.w0 == w then some p
            else none
        | none => none
      if let some p := sx? then
        s.bindWord w s!"(({p.src} as i{p.w0}) as i{w}) as {contTy w}"
      else if contBits w = w then
        s.bindWord w s!"(({e 0} as i{w}) >> {min n (w - 1)}) as {contTy w}"
      else s.unsupported (opName op)
  | .rorImm w n =>
      if contBits w = w then s.bindWord w s!"{e 0}.rotate_right({n % w})"
      else s.unsupported (opName op)
  | .stackLoad w n =>
      match v 0 with
      | .arr _ cells =>
          if n = 0 then s.bindWord w "0" (some 0)
          else match (v 1).const? with
            | some k => s.bindWord w (cells.getD (k % n) (compileError "cell out of range"))
            | none =>
                s.bindWord w
                  s!"[{", ".intercalate cells}][({e 1} % {n}) as usize]"
      | _ => s.unsupported (opName op)
  | .stackStore w n =>
      match v 0 with
      | .arr _ cells =>
          if n = 0 then (s, .arr w [])
          else match (v 1).const? with
            | some k => (s, .arr w (cells.set (k % n) (e 2)))
            | none =>
                let name := s!"x{s.next}"
                let l1 := s!"    let mut {name}: [{contTy w}; {n}] = [{", ".intercalate cells}];"
                let l2 := s!"    {name}[({e 1} % {n}) as usize] = {e 2};"
                ({ s with lines := (s.lines.push l1).push l2, next := s.next + 1 },
                 .arr w ((List.range n).map fun j => s!"{name}[{j}]"))
      | _ => s.unsupported (opName op)
  | _ => s.unsupported (opName op)

/-! ## 4. Programs and functions -/

/-- The lines of the bindings of `c` and the value it returns. -/
def emitCom : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t →
    PState → PState × RVal
  | _, _, .ret v, s => (s, s.look (varIdx v))
  | _, _, .var e body, s =>
      let (s', val) := emitExpr e.op (argIdxs e.args) s
      emitCom body { s' with env := val :: s'.env }

/-- The Rust parameter declaration of a context entry named `name`. -/
def paramDecl (name : String) (isMut : Bool) : JasminTy → String
  | .reg w => s!"{name}: {contTy w}"
  | .stackArr w n =>
      let ref := if isMut then "&mut " else "&"
      s!"{name}: {ref}[{contTy w}; {n}]"
  | .inlineInt => s!"{name}: u64"
  | .bool => s!"{name}: bool"

/-- The value of a context entry named `name`. -/
def paramVal (name : String) : JasminTy → RVal
  | .reg w => .word name w none
  | .stackArr w n => .arr w ((List.range n).map fun j => s!"{name}[{j}]")
  | _ => .other name

/-- An `#[inline] pub fn fname` computing `c`. The context entries are named by `names`
    (de Bruijn position `0` first). A result of type `stackArr w n` is written to the
    parameter `out : &mut [T; n]`, the first parameter; it is the context entry named `out`
    when there is one, and an added parameter otherwise. A result of type `reg w` is
    returned. -/
def emitFn {Γ : Ctxt jasminDialect} {t : JasminTy} (fname : String) (names : List String)
    (out : String) (c : Com jasminDialect Γ t) : String :=
  let params := names.zip Γ
  let env := params.map fun (nm, ty) => paramVal nm ty
  let (s, r) := emitCom c { env := env, lines := #[], next := 0 }
  let ins := params.filter (fun p => p.1 != out)
  let inDecls := ins.map fun (nm, ty) => paramDecl nm false ty
  let body := s.lines.toList
  let (sig, tail) : String × List String :=
    match t with
    | .stackArr w n =>
        let outDecl := paramDecl out true (.stackArr w n)
        let cells : List String := match r with
          | .arr _ cs => cs
          | _ => (List.range n).map fun _ => r.expr
        let readsOut := cells.any fun cell => cell.startsWith (out ++ "[")
        let writes :=
          if readsOut then
            [s!"    let r: [{contTy w}; {n}] = [{", ".intercalate cells}];", s!"    *{out} = r;"]
          else (List.range n).map fun j => s!"    {out}[{j}] = {cells.getD j "0"};"
        (s!"pub fn {fname}({", ".intercalate (outDecl :: inDecls)})", writes)
    | .reg w =>
        (s!"pub fn {fname}({", ".intercalate inDecls}) -> {contTy w}", [s!"    {r.expr}"])
    | _ =>
        (s!"pub fn {fname}({", ".intercalate inDecls})",
          [s!"    {compileError "result type outside the table"};"])
  "#[inline]\n" ++ sig ++ " {\n" ++ "\n".intercalate (body ++ tail) ++ "\n}\n"

/-! ## 5. Multi-result programs and programs in parts -/

/-- The lines of the bindings of the multi-result program `c` and the values it returns. -/
def emitMRCom : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    MultiReturnCom jasminDialect Γ ts → PState → PState × List RVal
  | _, _, .ret vs, s => (s, (argIdxs vs).map s.look)
  | _, _, .var e body, s =>
      let (s', val) := emitExpr e.op (argIdxs e.args) s
      emitMRCom body { s' with env := val :: s'.env }

/-- Whether a type is the register type of width `w`. -/
def isRegW (w : Nat) : JasminTy → Bool
  | .reg w' => w' == w
  | _ => false

/-- An `#[inline] pub fn fname(arr: &mut [T; n])` computing `c` in place: the context entry at
    de Bruijn position `j` is the cell `arr[j]`, and the `j`-th returned word is written to
    `arr[j]` after every binding. The context and the results are `n` registers of width
    `w`; any other shape prints a `compile_error!` line. `opts` selects the printing rules. -/
def emitFnInPlace {Γ : Ctxt jasminDialect} {ts : List JasminTy} (fname arr : String) (w : Nat)
    (c : MultiReturnCom jasminDialect Γ ts) (opts : EmitOpts := {}) : String :=
  let n := Γ.length
  let env := (List.range n).map fun j => RVal.word s!"{arr}[{j}]" w none
  let (s, rs) := emitMRCom c { env := env, lines := #[], next := 0, opts := opts }
  let tail :=
    if Γ.all (isRegW w) && ts.all (isRegW w) && ts.length == n then
      [s!"    let r: [{contTy w}; {n}] = [{", ".intercalate (rs.map RVal.expr)}];",
        s!"    *{arr} = r;"]
    else
      [s!"    {compileError "an in-place program needs n registers of one width in and out"};"]
  "#[inline]\n" ++ s!"pub fn {fname}({arr}: &mut [{contTy w}; {n}])" ++ " {\n" ++
    "\n".intercalate (s.constLines ++ s.lines.toList ++ tail) ++ "\n}\n"

/-- An `#[inline] pub fn fname(arr: &mut [T; n])` computing the programs `cs` one after the
    other in one body: the context entry at de Bruijn position `j` of the first program is
    the cell `arr[j]`, that of each later program is the `j`-th result of the program before
    it, and the `j`-th result of the last program is written to `arr[j]` after every binding.
    Word bindings are numbered across the programs. The context and the results are `n`
    registers of width `w`; any other shape prints a `compile_error!` line. `opts` selects
    the printing rules. -/
def emitFnInPlaceSeq {Γ : Ctxt jasminDialect} {ts : List JasminTy} (fname arr : String)
    (w : Nat) (cs : List (MultiReturnCom jasminDialect Γ ts)) (opts : EmitOpts := {}) :
    String :=
  let n := Γ.length
  let env := (List.range n).map fun j => RVal.word s!"{arr}[{j}]" w none
  let (s, rs) := cs.foldl
    (fun (acc : PState × List RVal) (c : MultiReturnCom jasminDialect Γ ts) =>
      emitMRCom c { acc.1 with env := acc.2 })
    ({ env := [], lines := #[], next := 0, opts := opts }, env)
  let tail :=
    if Γ.all (isRegW w) && ts.all (isRegW w) && ts.length == n then
      [s!"    let r: [{contTy w}; {n}] = [{", ".intercalate (rs.map RVal.expr)}];",
        s!"    *{arr} = r;"]
    else
      [s!"    {compileError "an in-place program needs n registers of one width in and out"};"]
  "#[inline]\n" ++ s!"pub fn {fname}({arr}: &mut [{contTy w}; {n}])" ++ " {\n" ++
    "\n".intercalate (s.constLines ++ s.lines.toList ++ tail) ++ "\n}\n"

/-- The `m` cell expressions of an array value; a word value fills every cell. -/
def RVal.cellsN (r : RVal) (m : Nat) : List String :=
  match r with
  | .arr _ cs => cs
  | _ => (List.range m).map fun _ => r.expr

/-- An `#[inline] pub fn fname(out: &mut [T; m * k], params)` computing the `k` programs `cs`
    over one context, each with result `stackArr w m`, one after the other in one body; the
    result of part `i` is written to `out[m * i]`, …, `out[m * i + m - 1]` after every
    binding. `env i` gives the values of the context for part `i` (de Bruijn position `0`
    first); word bindings are numbered across the parts. -/
def emitFnParts {Γ : Ctxt jasminDialect} (fname out : String) (params : List String)
    (env : Nat → List RVal) (w m : Nat) (cs : List (Com jasminDialect Γ (.stackArr w m))) :
    String :=
  let (s, cells) := cs.zipIdx.foldl
    (fun (acc : PState × List String) (ci : Com jasminDialect Γ (.stackArr w m) × Nat) =>
      let (s', r) := emitCom ci.1 { acc.1 with env := env ci.2 }
      (s', acc.2 ++ r.cellsN m))
    ({ env := [], lines := #[], next := 0 }, [])
  let k := m * cs.length
  let writes :=
    if cells.any fun cell => cell.startsWith (out ++ "[") then
      [s!"    let r: [{contTy w}; {k}] = [{", ".intercalate cells}];", s!"    *{out} = r;"]
    else (List.range k).map fun j => s!"    {out}[{j}] = {cells.getD j "0"};"
  "#[inline]\n" ++
    s!"pub fn {fname}({", ".intercalate (s!"{out}: &mut [{contTy w}; {k}]" :: params)})" ++
    " {\n" ++ "\n".intercalate (s.lines.toList ++ writes) ++ "\n}\n"

/-- The head of a generated Rust module file: the comment lines `comment` (each prefixed by
    `// `) and the inner attributes that silence the lints straight-line code trips. -/
def fileHead (comment : List String) : String :=
  "\n".intercalate (comment.map fun l => "// " ++ l) ++ "\n\n" ++
  "#![allow(unused)]\n#![allow(unused_parens)]\n#![allow(non_snake_case)]\n" ++
  "#![allow(clippy::all)]\n\n"

end CatCrypt.Crypto.Jasmin.ComToRustEmit
