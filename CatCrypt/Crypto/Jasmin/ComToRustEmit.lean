/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiReturnCom
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin

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
`const` item declared once at the top of the function. Under the rule `EmitOpts.inPlace` an
in-place function writes each output cell as soon as no later line reads its old value
(`inPlaceWrites`).

A third printing rule, `EmitOpts.v128`, holds each `reg 128` word in the Rust type `V` and
prints the 128-bit vector ops. Under the backend `simd`, `V` is `__m128i` and the ops are the
`core::arch::x86_64` intrinsics; under `portable`, `V` is `u128` and the ops are `u128`
arithmetic and the helper functions of `v128Prelude .portable`:

| op | `simd` | `portable` |
|---|---|---|
| `vsimd (.clmul imm)` | `_mm_clmulepi64_si128(a, b, imm)` | `clmul_u128(a, b, imm)`, bit-serial over 64 bits |
| `vsimd (.bitwise .xor/.and/.or/.andn)` | `_mm_xor_si128`, `_mm_and_si128`, `_mm_or_si128`, `_mm_andnot_si128` | `a ^ b`, `a & b`, `a \| b`, `!a & b` |
| `vpslldq k`, `vpsrldq k` | `_mm_slli_si128(a, k)`, `_mm_srli_si128(a, k)` | `a << 8k`, `a >> 8k` |
| `vsimd (.affineqb imm)` | `_mm_gf2p8affine_epi64_epi8(a, m, imm)` | `gf2p8affine_u128(a, m, imm)` |
| `vsimd .vpshufb` | `_mm_shuffle_epi8(a, idx)` | `shuffle_epi8_u128(a, idx)` |
| `regConst 128 n` | `v_const(n)`, a `u128` literal through `_mm_set_epi64x` | `v_const(n)`, the literal |
| `stackLoad 128 n` | the cell, or `arr[(i % n) as usize]` for an array parameter | the same |

Any other op on a 128-bit word prints a `compile_error!` line under this rule.

`emitNF` prints a structured program `NFProg jasminDialect`: bindings as `emitCom`, a counted
loop as a Rust `for` over its trip index with its carried values in `let mut` locals.

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
* `V128Backend`, `emitV128`: the two printings of the 128-bit vector ops.
* `emitNF`: the lines of an `NFProg jasminDialect`, a counted loop as a Rust `for`.
* `emitFnV128`: a Rust function over 128-bit values under one backend.
* `v128Prelude`: the type `V` and the helper functions of a backend's module.
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

/-- `acc` plus the de Bruijn position of a variable, by tail recursion. -/
def varIdxAux {Γ : Ctxt jasminDialect} {t : JasminTy} (acc : Nat) : Ctxt.Var Γ t → Nat
  | .here => acc
  | .there v => varIdxAux (acc + 1) v

/-- The de Bruijn position of a variable. -/
def varIdx {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t) : Nat :=
  varIdxAux 0 v

/-- `varIdxAux acc v` is `acc` plus the position of `v`. -/
theorem varIdxAux_eq {Γ : Ctxt jasminDialect} {t : JasminTy} (acc : Nat)
    (v : Ctxt.Var Γ t) : varIdxAux acc v = acc + varIdx v := by
  induction v generalizing acc with
  | here => rfl
  | there v ih =>
    rw [varIdx, varIdxAux, varIdxAux, ih, ih 1]
    omega

/-- The position of `.here` is `0`. -/
theorem varIdx_here {Γ : Ctxt jasminDialect} {t : JasminTy} :
    varIdx (Ctxt.Var.here : Ctxt.Var (t :: Γ) t) = 0 := rfl

/-- The position of `.there v` is one more than that of `v`. -/
theorem varIdx_there {Γ : Ctxt jasminDialect} {t s : JasminTy} (v : Ctxt.Var Γ t) :
    varIdx (Ctxt.Var.there v : Ctxt.Var (s :: Γ) t) = varIdx v + 1 := by
  rw [varIdx, varIdxAux, varIdxAux_eq]
  omega

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
  | .stackZero w n => s!"stackZero {w} {n}"
  | .stackStoreImm w n i => s!"stackStoreImm {w} {n} {i}"

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

/-- The two printings of a `reg 128` word: `simd` holds it in an `__m128i` and prints the
    vector ops as `core::arch::x86_64` intrinsics; `portable` holds it in a `u128` and prints
    them as `u128` arithmetic and the helper functions of `v128Prelude .portable`. -/
inductive V128Backend where
  | simd
  | portable
  deriving DecidableEq, Repr

/-- Printing rules that change the text of a binding but not the value it computes.

    * `sx`: the sign-extension rule. A widening `castW w w'` and a following
      `shlImm w' (w' - w)` of its result print no line: each is the expression
      `(a as uw')`, resp. `((a as uw') << (w' - w))`, at its uses. A `sarImm w' (w' - w)` of
      that shifted value prints the one cast `((a as iw) as iw') as uw'`, the sign extension
      of the `w`-bit word `a` to `w'` bits, which is what the three ops compute together.
      `w` and `w'` are widths of Rust integer types.
    * `hoist`: a `regConst w n` prints no line; its value is a `const` item `Kw_HEX` declared
      once per width and value at the top of the function.
    * `v128`: under `some b`, a `reg 128` word has the Rust type `V` and the 128-bit vector
      ops print as `emitV128 b`.
    * `inPlace`: `emitFnInPlace`, `emitFnInPlaceSeq` and `emitFnParts` write each output cell
      `a[j]` by the schedule `inPlaceWrites`: right after the first line from which its value
      is bound and no later line reads the old `a[j]`, instead of after the last line. -/
structure EmitOpts where
  sx : Bool := false
  hoist : Bool := false
  v128 : Option V128Backend := none
  inPlace : Bool := false

/-- A value printed as an expression by the sign-extension rule: the expression `expr`, the
    source word `src` of width `w0` widened to `w`, and whether it is shifted left by
    `w - w0`. -/
structure SxPending where
  expr : String
  src : String
  w0 : Nat
  w : Nat
  shifted : Bool

/-- The values of a context, indexed by level: `vals[0]` is the oldest entry and the last
    entry is at de Bruijn position `0`. -/
structure REnv where
  vals : Array RVal := #[]

/-- The context whose entries are `l`, head at de Bruijn position `0`. -/
def REnv.ofList (l : List RVal) : REnv := ⟨l.reverse.toArray⟩

/-- A list of values, head at de Bruijn position `0`, is a context. -/
instance : Coe (List RVal) REnv := ⟨REnv.ofList⟩

/-- The context extended by `v` at de Bruijn position `0`. -/
def REnv.push (e : REnv) (v : RVal) : REnv := ⟨e.vals.push v⟩

/-- The context extended by the values `l`, head at de Bruijn position `0`: the context of
    `l ++ es`, where `es` lists `e` head first. -/
def REnv.pushList (e : REnv) (l : List RVal) : REnv := ⟨e.vals ++ l.reverse.toArray⟩

/-- The value at de Bruijn position `i`. -/
def REnv.get? (e : REnv) (i : Nat) : Option RVal :=
  if i < e.vals.size then e.vals[e.vals.size - 1 - i]? else none

/-- Extending the context of `m` by `v` gives the context of `v :: m`. -/
theorem REnv.push_ofList (m : List RVal) (v : RVal) :
    (REnv.ofList m).push v = REnv.ofList (v :: m) := by
  simp [REnv.push, REnv.ofList]

/-- Extending the context of `m` by `l` gives the context of `l ++ m`. -/
theorem REnv.pushList_ofList (m l : List RVal) :
    (REnv.ofList m).pushList l = REnv.ofList (l ++ m) := by
  simp [REnv.pushList, REnv.ofList]

/-- The value at de Bruijn position `i` of the context of `l` is `l[i]?`. -/
theorem REnv.get?_ofList (l : List RVal) (i : Nat) : (REnv.ofList l).get? i = l[i]? := by
  unfold REnv.get? REnv.ofList
  split
  · grind
  · simp_all

/-- The printer's state: the values of the context, the lines printed so far, the index of
    the next word binding, the printing rules, the hoisted constants (width, value) and the
    last value of the sign-extension rule. -/
structure PState where
  env : REnv
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
  match s.env.get? i with
  | some v => v
  | none => .other (compileError s!"unbound variable at position {i}")

/-- The Rust type of a `w`-bit word: `V` for `w = 128` under the rule `v128`, `contTy w`
    otherwise. -/
def PState.tyOf (s : PState) (w : Nat) : String :=
  if s.opts.v128.isSome && w == 128 then "V" else contTy w

/-- Print `let xN: T = rhs;` for a `w`-bit word with known value `k`. -/
def PState.bindWord (s : PState) (w : Nat) (rhs : String) (k : Option Nat := none) :
    PState × RVal :=
  let name := s!"x{s.next}"
  ({ s with lines := s.lines.push s!"    let {name}: {s.tyOf w} = {rhs};", next := s.next + 1 },
   .word name w k)

/-- Print the `compile_error!` line of an op outside the table. -/
def PState.unsupported (s : PState) (what : String) : PState × RVal :=
  let e := compileError s!"op outside the table: {what}"
  ({ s with lines := s.lines.push s!"    {e};" }, .other e)

/-- Print the binding of `op` applied to the context positions `args` by the table of words
    of at most 128 bits. -/
def emitExprScalar (op : JasminOp) (args : List Nat) (s : PState) : PState × RVal :=
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

/-- Whether `op` reads or writes a 128-bit word. -/
def touches128 : JasminOp → Bool
  | .regArith _ w | .regConst w _ | .mulhi w | .addCarryLo w | .addCarryHi w | .rorImm w _
  | .shrImm w _ | .sarImm w _ | .shlImm w _ | .select w | .cmp _ w | .cmpImm _ w _
  | .stackLoad w _ | .stackStore w _ => w == 128
  | .castW w w' => w == 128 || w' == 128
  | .vpslldq _ | .vpsrldq _ | .vsimd _ => true
  | _ => false

/-- The array name `a` when `cells` are exactly `a[0]`, …, `a[n-1]`. -/
def arrBase (cells : List String) : Option String :=
  match cells.head? with
  | some c0 =>
      let a := String.ofList (c0.toList.take (c0.length - 3))
      if cells == (List.range cells.length).map (fun j => s!"{a}[{j}]") then some a else none
  | none => none

/-- The binding of `op` applied to the context positions `args` under the backend `b` of the
    rule `v128`, or `none` when `op` touches no 128-bit word. An op on a 128-bit word outside
    the vector table prints a `compile_error!` line. -/
def emitV128 (b : V128Backend) (op : JasminOp) (args : List Nat) (s : PState) :
    Option (PState × RVal) :=
  let v (i : Nat) : RVal := s.look (args.getD i 0)
  let e (i : Nat) : String := (v i).expr
  let simd := b == .simd
  let bind (rhs : String) : Option (PState × RVal) := some (s.bindWord 128 rhs)
  let bin (intr sym : String) : Option (PState × RVal) :=
    bind (if simd then s!"{intr}({e 0}, {e 1})" else s!"{e 0} {sym} {e 1}")
  if !touches128 op then none else
  match op with
  | .vsimd (.clmul imm) =>
      bind (if simd then s!"_mm_clmulepi64_si128({e 0}, {e 1}, {hexLit (imm % 256)})"
        else s!"clmul_u128({e 0}, {e 1}, {hexLit (imm % 256)})")
  | .vsimd (.bitwise .xor) => bin "_mm_xor_si128" "^"
  | .vsimd (.bitwise .and) => bin "_mm_and_si128" "&"
  | .vsimd (.bitwise .or) => bin "_mm_or_si128" "|"
  | .vsimd (.bitwise .andn) =>
      bind (if simd then s!"_mm_andnot_si128({e 0}, {e 1})" else s!"!{e 0} & {e 1}")
  | .vsimd (.affineqb imm) =>
      bind (if simd then s!"_mm_gf2p8affine_epi64_epi8({e 0}, {e 1}, {imm.toNat})"
        else s!"gf2p8affine_u128({e 0}, {e 1}, {imm.toNat})")
  | .vsimd .vpshufb =>
      bind (if simd then s!"_mm_shuffle_epi8({e 0}, {e 1})"
        else s!"shuffle_epi8_u128({e 0}, {e 1})")
  | .vpslldq n =>
      bind (if n < 16 then (if simd then s!"_mm_slli_si128({e 0}, {n})" else s!"{e 0} << {8 * n}")
        else (if simd then "_mm_setzero_si128()" else "0"))
  | .vpsrldq n =>
      bind (if n < 16 then (if simd then s!"_mm_srli_si128({e 0}, {n})" else s!"{e 0} >> {8 * n}")
        else (if simd then "_mm_setzero_si128()" else "0"))
  | .regConst 128 n =>
      let k := n % 2 ^ 128
      some (s.bindWord 128 s!"v_const({hexLit k})" (some k))
  | .stackLoad 128 n =>
      match v 0 with
      | .arr _ cells =>
          if n = 0 then some (s.bindWord 128 "v_const(0x0)" (some 0))
          else match (v 1).const? with
            | some k => bind (cells.getD (k % n) (compileError "cell out of range"))
            | none =>
                let idx := s!"({e 1} % {n}) as usize"
                match arrBase cells with
                | some a => bind s!"{a}[{idx}]"
                | none => bind s!"[{", ".intercalate cells}][{idx}]"
      | _ => some (s.unsupported (opName op))
  | _ => some (s.unsupported (opName op))

/-- Print the binding of `op` applied to the context positions `args`: by `emitV128` under
    the rule `v128` when `op` touches a 128-bit word, by `emitExprScalar` otherwise. -/
def emitExpr (op : JasminOp) (args : List Nat) (s : PState) : PState × RVal :=
  match s.opts.v128.bind (fun b => emitV128 b op args s) with
  | some r => r
  | none => emitExprScalar op args s

/-! ## 4. Programs and functions -/

/-- The lines of the bindings of `c` and the value it returns. -/
def emitCom : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t →
    PState → PState × RVal
  | _, _, .ret v, s => (s, s.look (varIdx v))
  | _, _, .var e body, s =>
      let (s', val) := emitExpr e.op (argIdxs e.args) s
      emitCom body { s' with env := s'.env.push val }

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
      emitMRCom body { s' with env := s'.env.push val }

/-- Whether a type is the register type of width `w`. -/
def isRegW (w : Nat) : JasminTy → Bool
  | .reg w' => w' == w
  | _ => false

/-! ### In-place writes -/

/-- Whether `c` can occur in a Rust identifier. -/
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The index `k` when the text `t` starts with `[k]`, `k` a decimal literal. -/
def litIndex? (t : String) : Option Nat :=
  match t.toList with
  | '[' :: cs =>
      let ds := cs.takeWhile Char.isDigit
      if !ds.isEmpty && (cs.drop ds.length).head? == some ']' then (String.ofList ds).toNat?
      else none
  | _ => none

/-- The reads of the array `arr` in the text `t`: whether `t` names `arr` other than as a
    cell `arr[k]` at a literal index `k` (a cell at a computed index, or the whole array),
    and the literal indices `k` of the cells `arr[k]` it names. An occurrence of `arr`
    counts when neither neighbouring character can extend an identifier. -/
def cellReads (arr t : String) : Bool × List Nat :=
  let ps := (t.splitOn arr).toArray
  let isId (o : Option Char) : Bool := o.any isIdentChar
  (List.range (ps.size - 1)).foldl (fun (acc : Bool × List Nat) k =>
    let prev := ps[k]!
    let next := ps[k + 1]!
    let pc : Option Char :=
      if prev.isEmpty then (if k = 0 then none else arr.toList.getLast?) else prev.toList.getLast?
    let nc : Option Char :=
      if next.isEmpty then (if k + 2 = ps.size then none else arr.toList.head?)
      else next.toList.head?
    if isId pc || isId nc then acc
    else match litIndex? next with
      | some j => (acc.1, j :: acc.2)
      | none => (true, acc.2))
    (false, [])

/-- The indices `N` of the binding names `xN` occurring in the text `t`, each delimited by
    characters that cannot extend an identifier. -/
def bindingRefs (t : String) : List Nat :=
  let digit (c : Char) : Nat := c.toNat - '0'.toNat
  let st := t.toList.foldl (fun (st : Char × Nat × Nat × List Nat) c =>
    let (p, mode, v, acc) := st
    match mode with
    | 2 => if c.isDigit then (c, 2, 10 * v + digit c, acc)
           else if isIdentChar c then (c, 0, 0, acc) else (c, 0, 0, v :: acc)
    | 1 => if c.isDigit then (c, 2, digit c, acc) else (c, 0, 0, acc)
    | _ => if c == 'x' && !isIdentChar p then (c, 1, 0, acc) else (c, 0, 0, acc))
    (' ', 0, 0, [])
  if st.2.1 = 2 then st.2.2.1 :: st.2.2.2 else st.2.2.2

/-- The index `N` of the binding a printed line assigns: a line `let xN: …`,
    `let mut xN: …` or `xN[…] = …`. -/
def assignedBinding? (line : String) : Option Nat :=
  let cs := line.toList.dropWhile (· == ' ')
  let cs := if cs.take 4 == "let ".toList then cs.drop 4 else cs
  let cs := if cs.take 4 == "mut ".toList then cs.drop 4 else cs
  match cs with
  | 'x' :: ds =>
      let dg := ds.takeWhile Char.isDigit
      match ds.drop dg.length with
      | c :: _ => if !dg.isEmpty && (c == ':' || c == '[') then (String.ofList dg).toNat? else none
      | [] => none
  | _ => none

/-- The writes of the outputs `outs` (cell index `j`, Rust expression `e`) to the array `arr`
    of `n` cells of type `ty`, placed among the printed lines `lines`: the writes to print
    after the `p`-th line (`p = 0`: before the first line), and the lines to print after the
    last one.

    An output `e = arr[j]` prints nothing. An output whose expression reads a cell of `arr`
    is deferred, and so is every output to a cell some deferred expression reads (to every
    cell when one reads `arr` at a computed index). Each other output `j` prints
    `arr[j] = e;` after line `p`, the least position at or after the last line reading
    `arr[j]` (or reading `arr` at a computed index) and the last line assigning a binding
    `xN` that `e` names. The deferred outputs are bound together in the array `r` after the
    last line and then written.

    The schedule keeps every value: a line after position `p` reads no cell `arr[j]` written
    at `p`, the expression `e` names cells of no array and only bindings assigned by then,
    and the deferred expressions read only cells written after them or not at all. The
    reads are found in the text: an occurrence of `arr` delimited as an identifier, followed
    by `[k]` for a literal `k` or by anything else, which counts as a read of every cell. -/
def inPlaceWrites (arr ty : String) (n : Nat) (lines : Array String)
    (outs : List (Nat × String)) : Array (List String) × List String :=
  let (rd, dyn, defs) := lines.toList.zipIdx.foldl
    (fun (acc : Array Nat × Nat × Array Nat) (li : String × Nat) =>
      let (rd, dyn, defs) := acc
      let pos := li.2 + 1
      let (d, ks) := cellReads arr li.1
      let rd := ks.foldl (fun r k => if k < r.size then r.set! k pos else r) rd
      let defs := match assignedBinding? li.1 with
        | some m =>
            (if m < defs.size then defs else defs ++ Array.replicate (m + 1 - defs.size) 0).set!
              m pos
        | none => defs
      (rd, if d then pos else dyn, defs))
    (Array.replicate n 0, 0, #[])
  let outs := outs.filter fun (j, e) => e != s!"{arr}[{j}]"
  let readsArr (e : String) : Bool := let (d, ks) := cellReads arr e; d || !ks.isEmpty
  let (dAll, dKs) := (outs.filter fun (_, e) => readsArr e).foldl
    (fun (acc : Bool × List Nat) (o : Nat × String) =>
      let (d, ks) := cellReads arr o.2
      (acc.1 || d, ks ++ acc.2))
    (false, [])
  let deferred (o : Nat × String) : Bool := readsArr o.2 || dAll || dKs.contains o.1
  let slots := (outs.filter fun o => !deferred o).foldl
    (fun (sl : Array (List String)) (o : Nat × String) =>
      let p := max (max (rd.getD o.1 0) dyn)
        ((bindingRefs o.2).foldl (fun m b => max m (defs.getD b 0)) 0)
      sl.modify p (· ++ [s!"    {arr}[{o.1}] = {o.2};"]))
    (Array.replicate (lines.size + 1) [])
  let late := outs.filter deferred
  let tail :=
    if late.isEmpty then []
    else s!"    let r: [{ty}; {late.length}] = [{", ".intercalate (late.map (·.2))}];" ::
      late.zipIdx.map fun (o, i) => s!"    {arr}[{o.1}] = r[{i}];"
  (slots, tail)

/-- The lines `lines` with the writes `slots[p]` after the `p`-th line (`slots[0]` before the
    first line). -/
def interleaveWrites (lines : Array String) (slots : Array (List String)) : List String :=
  slots.getD 0 [] ++ lines.toList.zipIdx.flatMap fun (l, i) => l :: slots.getD (i + 1) []

/-- The body of an in-place function over `arr : &mut [T; n]`, `T` the container of width `w`,
    after the printed lines `lines` with results `rs`: under the rule `inPlace` the writes of
    `inPlaceWrites` placed among the lines, otherwise the lines followed by `*arr = r` for the
    array `r` of the results. `ok` is the shape check; when it fails the body ends in a
    `compile_error!` line. -/
def inPlaceBody (arr : String) (w n : Nat) (ok : Bool) (opts : EmitOpts) (lines : Array String)
    (rs : List RVal) : List String :=
  if !ok then
    lines.toList ++
      [s!"    {compileError "an in-place program needs n registers of one width in and out"};"]
  else if opts.inPlace then
    let (slots, tail) :=
      inPlaceWrites arr (contTy w) n lines (rs.zipIdx.map fun (r, j) => (j, r.expr))
    interleaveWrites lines slots ++ tail
  else
    lines.toList ++
      [s!"    let r: [{contTy w}; {n}] = [{", ".intercalate (rs.map RVal.expr)}];",
        s!"    *{arr} = r;"]

/-- An `#[inline] pub fn fname(arr: &mut [T; n])` computing `c` in place: the context entry at
    de Bruijn position `j` is the cell `arr[j]`, and the `j`-th returned word is written to
    `arr[j]`, after every binding or by the rule `inPlace`. The context and the results are
    `n` registers of width `w`; any other shape prints a `compile_error!` line. `opts`
    selects the printing rules. -/
def emitFnInPlace {Γ : Ctxt jasminDialect} {ts : List JasminTy} (fname arr : String) (w : Nat)
    (c : MultiReturnCom jasminDialect Γ ts) (opts : EmitOpts := {}) : String :=
  let n := Γ.length
  let env := (List.range n).map fun j => RVal.word s!"{arr}[{j}]" w none
  let (s, rs) := emitMRCom c { env := env, lines := #[], next := 0, opts := opts }
  let ok := Γ.all (isRegW w) && ts.all (isRegW w) && ts.length == n
  "#[inline]\n" ++ s!"pub fn {fname}({arr}: &mut [{contTy w}; {n}])" ++ " {\n" ++
    "\n".intercalate (s.constLines ++ inPlaceBody arr w n ok opts s.lines rs) ++ "\n}\n"

/-- An `#[inline] pub fn fname(arr: &mut [T; n])` computing the programs `cs` one after the
    other in one body: the context entry at de Bruijn position `j` of the first program is
    the cell `arr[j]`, that of each later program is the `j`-th result of the program before
    it, and the `j`-th result of the last program is written to `arr[j]`, after every binding
    or by the rule `inPlace`. Word bindings are numbered across the programs. The context and
    the results are `n` registers of width `w`; any other shape prints a `compile_error!`
    line. `opts` selects the printing rules. -/
def emitFnInPlaceSeq {Γ : Ctxt jasminDialect} {ts : List JasminTy} (fname arr : String)
    (w : Nat) (cs : List (MultiReturnCom jasminDialect Γ ts)) (opts : EmitOpts := {}) :
    String :=
  let n := Γ.length
  let env := (List.range n).map fun j => RVal.word s!"{arr}[{j}]" w none
  let (s, rs) := cs.foldl
    (fun (acc : PState × List RVal) (c : MultiReturnCom jasminDialect Γ ts) =>
      emitMRCom c { acc.1 with env := acc.2 })
    ({ env := {}, lines := #[], next := 0, opts := opts }, env)
  let ok := Γ.all (isRegW w) && ts.all (isRegW w) && ts.length == n
  "#[inline]\n" ++ s!"pub fn {fname}({arr}: &mut [{contTy w}; {n}])" ++ " {\n" ++
    "\n".intercalate (s.constLines ++ inPlaceBody arr w n ok opts s.lines rs) ++ "\n}\n"

/-- The `m` cell expressions of an array value; a word value fills every cell. -/
def RVal.cellsN (r : RVal) (m : Nat) : List String :=
  match r with
  | .arr _ cs => cs
  | _ => (List.range m).map fun _ => r.expr

/-- An `#[inline] pub fn fname(out: &mut [T; m * k], params)` computing the `k` programs `cs`
    over one context, each with result `stackArr w m`, one after the other in one body; the
    result of part `i` is written to `out[m * i]`, …, `out[m * i + m - 1]`, after every
    binding or, under the rule `inPlace`, cell by cell as `inPlaceWrites` places it among
    the lines of all parts. `env i` gives the values of the context for part `i` (de Bruijn
    position `0` first); word bindings are numbered across the parts. `opts` selects the
    printing rules. -/
def emitFnParts {Γ : Ctxt jasminDialect} (fname out : String) (params : List String)
    (env : Nat → List RVal) (w m : Nat) (cs : List (Com jasminDialect Γ (.stackArr w m)))
    (opts : EmitOpts := {}) : String :=
  let (s, cells) := cs.zipIdx.foldl
    (fun (acc : PState × List String) (ci : Com jasminDialect Γ (.stackArr w m) × Nat) =>
      let (s', r) := emitCom ci.1 { acc.1 with env := env ci.2 }
      (s', acc.2 ++ r.cellsN m))
    ({ env := {}, lines := #[], next := 0, opts := opts }, [])
  let k := m * cs.length
  let body :=
    if opts.inPlace then
      let (slots, tail) :=
        inPlaceWrites out (contTy w) k s.lines (cells.zipIdx.map fun (e, j) => (j, e))
      interleaveWrites s.lines slots ++ tail
    else if cells.any fun cell => cell.startsWith (out ++ "[") then
      s.lines.toList ++
        [s!"    let r: [{contTy w}; {k}] = [{", ".intercalate cells}];", s!"    *{out} = r;"]
    else s.lines.toList ++ (List.range k).map fun j => s!"    {out}[{j}] = {cells.getD j "0"};"
  "#[inline]\n" ++
    s!"pub fn {fname}({", ".intercalate (s!"{out}: &mut [{contTy w}; {k}]" :: params)})" ++
    " {\n" ++ "\n".intercalate (s.constLines ++ body) ++ "\n}\n"

/-- The head of a generated Rust module file: the comment lines `comment` (each prefixed by
    `// `) and the inner attributes that silence the lints straight-line code trips. -/
def fileHead (comment : List String) : String :=
  "\n".intercalate (comment.map fun l => "// " ++ l) ++ "\n\n" ++
  "#![allow(unused)]\n#![allow(unused_parens)]\n#![allow(non_snake_case)]\n" ++
  "#![allow(clippy::all)]\n\n"

/-! ## 6. Structured programs and 128-bit vector functions -/

/-- The Rust type of a carried value of type `t`. -/
def PState.tyOfTy (s : PState) : JasminTy → String
  | .reg w => s.tyOf w
  | _ => compileError "a carried value that is not a register"

/-- The lines of the structured program `c` and the values it returns. A binding prints as
    in `emitCom`. A counted loop `forLoop count inits body k` prints its carried values as
    `let mut` locals initialised from `inits`, then `for i in 0u64..count` with a block
    holding the lines of `body` and the assignments of its results to the carried locals,
    then the lines of `k`, which sees the carried locals. A branch or an exit-flag loop
    prints a `compile_error!` line. -/
def emitNF : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts →
    PState → PState × List RVal
  | _, _, .ret vs, s => (s, (argIdxs vs).map s.look)
  | _, _, .var e k, s =>
      let (s', val) := emitExpr e.op (argIdxs e.args) s
      emitNF k { s' with env := s'.env.push val }
  | _, _, .forLoop (cs := cs) count inits body k, s =>
      let base := s.next
      let names := (List.range cs.length).map fun j => s!"x{base + j}"
      let idx := s!"x{base + cs.length}"
      let decls := (names.zip (cs.zip (argIdxs inits))).map fun (nm, t, i) =>
        s!"    let mut {nm}: {s.tyOfTy t} = {(s.look i).expr};"
      let carried := (names.zip cs).map fun (nm, t) => paramVal nm t
      let env0 : REnv := (s.env.push (RVal.word idx 64 none)).pushList carried
      let s0 : PState :=
        { s with lines := #[], next := base + cs.length + 1, env := env0, sxLast := none }
      let (sb, rs) := emitNF body s0
      let assigns := (names.zip rs).map fun (nm, r) => s!"    {nm} = {r.expr};"
      let block := (sb.lines.toList ++ assigns).map ("    " ++ ·)
      let head := s!"    for {idx} in 0u64..{(s.look (varIdx count)).expr} \{"
      let lines := (s.lines ++ decls.toArray).push head ++ block.toArray |>.push "    }"
      emitNF k { sb with lines := lines, env := s.env.pushList carried, sxLast := none }
  | _, _, .ifThenElse .., s => ((s.unsupported "ifThenElse").1, [])
  | _, _, .whileLoop .., s => ((s.unsupported "whileLoop").1, [])
  | _, _, .call .., s => ((s.unsupported "call").1, [])

/-- A Rust function `fname(params)` under the backend `b` of the rule `v128`: the lines `pre`,
    then the lines of `body` run from the context values `env` (de Bruijn position `0`
    first), then the lines `post rs` of its results `rs`. Under `simd` it is a
    `pub unsafe fn` behind `#[target_feature(enable = "features")]`; under `portable` an
    `#[inline] pub fn`. -/
def emitFnV128 (b : V128Backend) (features fname : String) (params pre : List String)
    (env : List RVal) (post : List RVal → List String)
    (body : PState → PState × List RVal) : String :=
  let (s, rs) := body { env := env, lines := #[], next := 0, opts := { v128 := some b } }
  let head := match b with
    | .simd => s!"#[target_feature(enable = \"{features}\")]\npub unsafe fn "
    | .portable => "#[inline]\npub fn "
  head ++ s!"{fname}({", ".intercalate params})" ++ " {\n" ++
    "\n".intercalate (pre ++ s.lines.toList ++ post rs) ++ "\n}\n"

/-- The items a module printed under the backend `b` relies on: the type `V` of a 128-bit
    word, `v_const` (a `u128` literal as a `V`), `load_v` and `store_v` (a `V` from and to
    `[u64; 2]`, word `0` the low 64 bits), and under `portable` the helper functions
    `clmul_u128` (the carry-less product of the `imm`-selected 64-bit halves, bit-serial over
    64 bits), `gf2p8affine_u128` and `shuffle_epi8_u128` (the byte-wise affine transform and
    the byte shuffle of `JasminDialect.gf2p8affineqbW` and `vpshufbW`). -/
def v128Prelude : V128Backend → String
  | .simd =>
    "use core::arch::x86_64::*;\n\n" ++
    "pub type V = __m128i;\n\n" ++
    "#[inline(always)]\n" ++
    "fn v_const(k: u128) -> V {\n" ++
    "    unsafe { _mm_set_epi64x((k >> 64) as u64 as i64, k as u64 as i64) }\n}\n\n" ++
    "#[inline(always)]\n" ++
    "fn load_v(a: &[u64; 2]) -> V {\n" ++
    "    unsafe { _mm_set_epi64x(a[1] as i64, a[0] as i64) }\n}\n\n" ++
    "#[inline(always)]\n" ++
    "fn store_v(out: &mut [u64; 2], x: V) {\n" ++
    "    *out = unsafe { core::mem::transmute::<V, [u64; 2]>(x) };\n}\n\n"
  | .portable =>
    "pub type V = u128;\n\n" ++
    "#[inline(always)]\n" ++
    "fn v_const(k: u128) -> V {\n    k\n}\n\n" ++
    "#[inline(always)]\n" ++
    "fn load_v(a: &[u64; 2]) -> V {\n    (a[0] as u128) | ((a[1] as u128) << 64)\n}\n\n" ++
    "#[inline(always)]\n" ++
    "fn store_v(out: &mut [u64; 2], x: V) {\n" ++
    "    out[0] = x as u64;\n    out[1] = (x >> 64) as u64;\n}\n\n" ++
    "#[inline(always)]\n" ++
    "fn clmul_u128(a: u128, b: u128, imm: u32) -> u128 {\n" ++
    "    let x: u64 = if imm & 0x01 != 0 { (a >> 64) as u64 } else { a as u64 };\n" ++
    "    let y: u128 = if imm & 0x10 != 0 { b >> 64 } else { (b as u64) as u128 };\n" ++
    "    let mut r: u128 = 0;\n" ++
    "    for i in 0..64u32 {\n" ++
    "        let m: u128 = 0u128.wrapping_sub(((x >> i) & 1) as u128);\n" ++
    "        r ^= (y << i) & m;\n    }\n    r\n}\n\n" ++
    "#[inline(always)]\n" ++
    "fn gf2p8affine_u128(x: u128, a: u128, imm: u8) -> u128 {\n" ++
    "    let mut r: u128 = 0;\n" ++
    "    for k in 0..16u32 {\n" ++
    "        let xb: u8 = (x >> (8 * k)) as u8;\n" ++
    "        let q: u64 = (a >> (64 * (k / 8))) as u64;\n" ++
    "        let mut ob: u8 = 0;\n" ++
    "        for j in 0..8u32 {\n" ++
    "            let row: u8 = (q >> (8 * (7 - j))) as u8;\n" ++
    "            let bit: u8 = ((row & xb).count_ones() as u8 & 1) ^ ((imm >> j) & 1);\n" ++
    "            ob |= bit << j;\n        }\n" ++
    "        r |= (ob as u128) << (8 * k);\n    }\n    r\n}\n\n" ++
    "#[inline(always)]\n" ++
    "fn shuffle_epi8_u128(a: u128, idx: u128) -> u128 {\n" ++
    "    let mut r: u128 = 0;\n" ++
    "    for i in 0..16u32 {\n" ++
    "        let c: u8 = (idx >> (8 * i)) as u8;\n" ++
    "        let byte: u8 = if c & 0x80 != 0 { 0 } else { (a >> (8 * ((c & 0x0f) as u32))) as u8 };\n" ++
    "        r |= (byte as u128) << (8 * i);\n    }\n    r\n}\n\n"

end CatCrypt.Crypto.Jasmin.ComToRustEmit
