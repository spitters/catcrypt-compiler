/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminAST
import CatCrypt.Crypto.Jasmin.Passes.DeadCode

/-!
# Jasmin surface-syntax emitter for SSA u64 programs

Produces a `.jazz` source string that `jasminc -arch x86-64` accepts,
tailored to the SSA subset produced by our `S2NBignumSSA` ports. The
existing `LowCTToJasmin.ppJasminProg` has two blocking bugs for our
programs — every binary op prints as literal `" op "`, and
`Papp1 (Oword_of_int)` immediates dump their raw AST — so this module
provides a new printer rather than patching the old one.

## x86 2-operand form

x86's arithmetic is mostly 2-operand (destructive). `jasminc`'s register
allocator rejects `x = y OP z` when `x ≠ y`, so for each binary-op
`Cassgn` we emit a two-instruction sequence:

```
x = y;
x OP= z;
```

The Jasmin compiler's register allocator elides the initial `movq`
whenever it can reuse the source register.

## Supported instruction shapes

| Jasmin `InstrR`                                | Emitted                        |
|------------------------------------------------|--------------------------------|
| `Cassgn x _ _ (Pconst k)`                      | `x = k;`                       |
| `Cassgn x _ _ (Papp1 (Oword_of_int _) (Pconst k))` | `x = k;`                   |
| `Cassgn x _ _ (Pvar y)`                        | `x = y;`                       |
| `Cassgn x _ _ (Papp1 (Olnot _) (Pvar y))`      | `x = y; x = !x;`               |
| `Cassgn x _ _ (Papp2 op (Pvar y) (Pvar z))`    | `x = y; x OP= z;`              |
| `Cassgn x _ _ (Papp2 op (Pvar y) (Pconst k))`  | `x = y; x OP= k;`              |

Any other shape produces `none`, and `emitFunDecl` propagates failure.
-/

namespace CatCrypt.Crypto.Jasmin.Emit

open CatCrypt.Crypto.Jasmin

set_option autoImplicit false

/-! ## Operator dispatch -/

/-- Bit-width of a word size, for Jasmin cast syntax `(NNu) e`. -/
def wsizeBits : WSize → Nat
  | .U8 => 8 | .U16 => 16 | .U32 => 32
  | .U64 => 64 | .U128 => 128 | .U256 => 256 | .U512 => 512

/-- The Jasmin memory-access / declaration token for a word size: `u8`/`u16`/
    `u32`/`u64`/…. Used for `reg uNN` declarations and `[:uNN base + k]`
    memory operands. -/
def wsizeTok : WSize → String
  | .U8 => "u8" | .U16 => "u16" | .U32 => "u32"
  | .U64 => "u64" | .U128 => "u128" | .U256 => "u256" | .U512 => "u512"

/-- Binary-op syntax. Supported at `U32` and `U64` (the two GPR limb widths the
    mpn kernels use); other widths return `none`. The width is carried in the
    AST `SOp2` and consumed by the surrounding declarations, so the emitted
    operator token (`+`, `&`, `<<`, …) is width-independent. -/
def binOpStr : SOp2 → Option String
  | .Oadd  .U64 => some "+"
  | .Osub  .U64 => some "-"
  | .Omul  .U64 => some "*"
  | .Olxor .U64 => some "^"
  | .Oland .U64 => some "&"
  | .Olor  .U64 => some "|"
  | .Olsl  .U64 => some "<<"
  | .Olsr  .U64 => some ">>"
  -- Signed-arith extension (#257): arithmetic (sign-preserving) shift right.
  -- Jasmin surface token `>>s`; compound form `>>s=` (cf. the plonky3 /
  -- poseidon2 / mlkem signed-Montgomery leaves).
  | .Oasr  .U64 => some ">>s"
  | .Oadd  .U32 => some "+"
  | .Osub  .U32 => some "-"
  | .Omul  .U32 => some "*"
  | .Olxor .U32 => some "^"
  | .Oland .U32 => some "&"
  | .Olor  .U32 => some "|"
  | .Olsl  .U32 => some "<<"
  | .Olsr  .U32 => some ">>"
  | .Oasr  .U32 => some ">>s"
  | _ => none

/-- Jasmin infix operator for a built-in binop *function name* — the strings
    that `LowCTToJasmin.toJasminCmd` lowers `RCall <op> dst [a, b]` into
    via the `Ccall` arm. `jasminc` does not have callable functions named
    `Add` / `Sub` / `BitXor` / …, so when the emitter sees a `Ccall` to one
    of these names with exactly two `Pvar` operands it must rewrite into a
    Jasmin infix `dst = a OP b;` (Two-operand form: `dst = a; dst OP= b;`).
    Returns `none` for leaf-function names (`poly_add`, `mat_vec_mul`,
    …), which fall through to the regular function-call emit. This mirrors
    the `RustEmitJazz.jasminBinOp` rewrite that lives in the deprecated
    Rust-shaped path; the AST-direct path now recognises the same set. -/
def binOpNameStr (f : String) : Option String :=
  match f with
  | "Add" | "add" | "wrapping_add" => some "+"
  | "Sub" | "sub" | "wrapping_sub" => some "-"
  | "Mul" | "mul" | "wrapping_mul" => some "*"
  | "Shl" | "Shl#32" | "Shl#16" | "Shl#64" => some "<<"
  | "Shr" | "Shr#32" | "Shr#16" | "Shr#64" => some ">>"
  | "BitAnd" | "BitAnd#32" | "BitAnd#16" | "BitAnd#64" => some "&"
  | "BitOr"  | "BitOr#32"  | "BitOr#16"  | "BitOr#64"  => some "|"
  | "BitXor" | "BitXor#32" | "BitXor#16" | "BitXor#64" => some "^"
  | _ => none

/-! ## Body analysis -/

/-- Names appearing as LHS of any `Cassgn (.Lvar _) …` or
    `Copn` lvals (ignoring `Lnone` flag-discards). Recurses into
    `Cfor`, `Cwhile`, and `Cif` bodies so nested local assignments are
    collected — without the `Cif` recursion, variables written only inside
    one branch arm would be missing from the `reg uNN …;` declaration line,
    causing jasminc to reject the emitted `.jazz`.
    `Ccall` lvals also count — the callee may write into named registers. -/
partial def lhsNames : List InstrR → List String
  | [] => []
  | .Cassgn (.Lvar x) _ _ _ :: rest => x.var.vname :: lhsNames rest
  | .Copn lvs _ _ _ :: rest =>
      let names := lvs.filterMap (fun | .Lvar x => some x.var.vname | _ => none)
      names ++ lhsNames rest
  | .Ccall _ lvs _ _ :: rest =>
      let names := lvs.filterMap (fun | .Lvar x => some x.var.vname | _ => none)
      names ++ lhsNames rest
  | .Cfor _ _ body :: rest => lhsNames body ++ lhsNames rest
  | .Cwhile cbefore _ cafter :: rest =>
      lhsNames cbefore ++ lhsNames cafter ++ lhsNames rest
  | .Cif _ th el :: rest =>
      lhsNames th ++ lhsNames el ++ lhsNames rest
  | _ :: rest => lhsNames rest

/-- Scalar LHS names that **must** be declared `reg` (not `stack`) under the
    `spillScalars` path: jasminc's linearization (`check_rexpr`) rejects a
    `stack` destination for an assignment whose RHS is a dynamic-index array
    load `arr[i]`, a width cast `(NNu) e`, or a memory load `[:uNN …]`.
    Keeping these few destinations in registers (while the bulk of cold
    scalars spill to the stack) lets large kernels both fit the GPR budget
    and pass linearization. Recurses into loop / branch bodies. -/
partial def regForcedNames : List InstrR → List String
  | [] => []
  | .Cassgn lv _ _ rhs :: rest =>
      -- A statement that jasminc cannot lower with a `stack` operand
      -- (`check_rexpr`): a dynamic-index store/read `arr[i]`, a cast
      -- `(NNu) e`, a memory load `[:uNN …]`, or a *nested* arithmetic
      -- expression (the multi-op `RScalarSetExpr` form).  For every such
      -- statement, force-reg the destination AND every scalar operand
      -- (jasminc allows at most one memory operand per instruction, so a
      -- nested expression's leaves must all be registers).
      let lvIdx := match lv with
        | .Laset .AAscale _ _ idx => exprVars idx
        | _ => []
      let isHard := match rhs with
        | .Pget _ _ _ _ => true
        | .Papp1 (.Ozeroext _ _) _ => true
        | .Pload _ _ _ => true
        -- Any two-operand binop must land in a register: x86 ALU/shift
        -- instructions allow at most one memory operand, so the compact
        -- `x = a; x OP= b;` form needs `x` (and at least one of a/b) in a
        -- register — a `stack OP= stack` is two memory operands, which the
        -- assembler rejects.  Forcing the binop destination + operands to
        -- reg (they are short-lived arithmetic temps, freely re-allocated)
        -- leaves only copies / array-store sources / counters on the stack.
        | .Papp2 _ _ _ => true
        | _ => rhsIsNested rhs
      let lvName := match lv with
        | .Lvar x => if isHard then [x.var.vname] else []
        | _ => []
      -- jasminc allows ONE memory operand per instruction, so we force the
      -- binop/cast/load *destination* to a register; the operands may stay
      -- on the stack (`reg OP= mem` is fine).  The only operands that must
      -- additionally be reg are array *index* expressions (a stack-indexed
      -- `arr[stack_i]` is not a legal address mode here) — those are
      -- collected by `rhsIndexVars` (and `lvIdx` for the store side).
      -- #262: a binop with a *constant* operand (e.g. `0 - x`, `2 - x`) lowers
      -- to a form jasminc's asmgen cannot encode with the variable operand in
      -- memory (`reg = imm OP mem` is not a legal addressing mode — it raises
      -- `asmgen: (compile_arg) not compatible asm_arg`).  Force the `Pvar`
      -- operand of any const-bearing binop to a register so the op becomes
      -- `reg = imm OP reg`.
      let constBinopOperand : List String := match rhs with
        | .Papp2 _ (.Pconst _) (.Pvar gv) => [gv.gv.var.vname]
        | .Papp2 _ (.Pvar gv) (.Pconst _) => [gv.gv.var.vname]
        | _ => []
      let operandNames := rhsIndexVars rhs ++ constBinopOperand
      lvName ++ lvIdx ++ operandNames ++ regForcedNames rest
  | .Copn lvs _ _ es :: rest =>
      -- #262: an asm intrinsic (`#IMUL` / `#MULX` / `#ADC` / `#CMOV` …) has
      -- implicit register outputs (e.g. RDX:RAX for the widening multiply) and
      -- register operands.  jasminc's `forced_registers` pass (regalloc.ml)
      -- asserts that every such operand is an `Lvar`/`Pvar` allocated to a
      -- *register* — a `stack` slot fails the assertion.  Under `spillScalars`
      -- these would otherwise be spilled, so we force-reg every `Lvar` output
      -- and `Pvar` input of any `Copn`.
      let lvN : LVal → List String
        | .Lvar x => [x.var.vname]
        | .Laset .AAscale _ _ idx => exprVars idx
        | _ => []
      let esN : PExpr → List String
        | .Pvar gv => [gv.gv.var.vname]
        | e => exprVars e
      lvs.flatMap lvN ++ es.flatMap esN ++ regForcedNames rest
  | .Cfor _ _ body :: rest => regForcedNames body ++ regForcedNames rest
  | .Cwhile cb _ ca :: rest => regForcedNames cb ++ regForcedNames ca ++ regForcedNames rest
  | .Cif _ th el :: rest => regForcedNames th ++ regForcedNames el ++ regForcedNames rest
  | _ :: rest => regForcedNames rest
where
  /-- All scalar `Pvar` names appearing in an expression, including the
      index expression of any `Pget` array read (the index must be a reg). -/
  exprVars : PExpr → List String
    | .Pvar gv => [gv.gv.var.vname]
    | .Papp1 _ e => exprVars e
    | .Papp2 _ a b => exprVars a ++ exprVars b
    | .Pget _ _ _ idx => exprVars idx
    | _ => []
  /-- Index vars of any dynamic-index `Pget` read anywhere in an RHS. -/
  rhsIndexVars : PExpr → List String
    | .Pget .AAscale _ _ idx => exprVars idx
    | .Papp1 _ e => rhsIndexVars e
    | .Papp2 _ a b => rhsIndexVars a ++ rhsIndexVars b
    | _ => []
  /-- `true` iff the RHS is a *nested* arithmetic expression whose operands
      are not all atomic (`Pvar`/`Pconst`).  Such a RHS does not lower to a
      `stack` destination in one jasmin statement (`check_rexpr`). -/
  rhsIsNested : PExpr → Bool
    | .Papp2 _ a b => !(isAtom a) || !(isAtom b)
    | _ => false
  isAtom : PExpr → Bool
    | .Pvar _ => true
    | .Pconst _ => true
    | .Papp1 (.Oword_of_int _) (.Pconst _) => true
    | _ => false

/-- Deduplicate while preserving first-occurrence order. -/
def dedup : List String → List String :=
  let rec go (seen acc : List String) : List String → List String
    | [] => acc.reverse
    | x :: xs => if seen.contains x then go seen acc xs
                 else go (x :: seen) (x :: acc) xs
  go [] []

/-- **E1.5 (arithmetic-expression renderer, 2026-05-30).** Render a `PExpr`
    as a parenthesised Jasmin arithmetic expression.  This is the
    expression-position counterpart of `emitInstr` (which only handles a
    fixed set of flat `Cassgn` shapes): it recurses through the nested
    arithmetic produced by `LowCTToJasmin.sexprToPExpr` (the `RScalarSetExpr`
    lowering) and through dynamic-index `Pget` reads (the `RArrLoad`
    lowering).

    Supported subset:
    * `Pvar x`              → `x`
    * `Pconst k`            → `k` (integer literal — Jasmin's surface accepts
      unsuffixed literals in expression position)
    * `Papp1 (Oword_of_int) (Pconst k)` → `k` (the boxed-literal idiom)
    * `Papp1 (Ozeroext w) e`  → `(<bits>u) <e>` (width cast)
    * `Papp2 op a b`        → `(<a> <op> <b>)` for the arithmetic/bitwise/shift
      `SOp2`s in `binOpStr`, plus unsigned `<` (`Olt Uextend`)
    * `Pget AAscale ws arr idx` → `arr[<idx>]` (dynamic array read, `idx` may
      itself be an arithmetic expression)

    Anything else returns `none`, so an unexpected shape fails emission
    conservatively rather than producing malformed jazz. -/
partial def ppArithExpr : PExpr → Option String
  | .Pvar gv => some gv.gv.var.vname
  | .Pconst k => some (toString k)
  | .Papp1 (.Oword_of_int _) (.Pconst k) => some (toString k)
  | .Papp1 (.Ozeroext wso _) e => do
      let es ← ppArithExpr e
      some ("(" ++ toString (wsizeBits wso) ++ "u) " ++ es)
  | .Papp2 op a b => do
      let opS ← (match op with
        | .Olt _ _ => some "<"
        | _ => binOpStr op)
      let as ← ppArithExpr a
      let bs ← ppArithExpr b
      some ("(" ++ as ++ " " ++ opS ++ " " ++ bs ++ ")")
  | .Pget .AAscale _ arr idx => do
      let is ← ppArithExpr idx
      some (arr.gv.var.vname ++ "[" ++ is ++ "]")
  | _ => none

/-! ## Instruction emitter -/

/-- Render one instruction as a (possibly 2-line) Jasmin statement.

    **Extension 3A (`Cfor`):** `Cfor v {.UpTo, lo, hi} body` is emitted as
    `for i = lo to hi { <body> }` using Jasmin's compile-time `inline int`
    loop — jasminc fully unrolls it. The loop variable name is taken from
    `v` in the AST (conventionally `i`).

    Nested loops and multi-statement bodies are handled by recursing
    through `emitInstr` on each body instruction. If any body instruction
    is unsupported, the whole emission fails. -/
partial def emitInstr (ind : String) : InstrR → Option String
  -- `Parr_init n` zero-initializes an n-byte array. At the Jasmin
  -- source level, `reg` declarations are uninitialized by convention
  -- and parameter regs are initialized by the caller. So we emit a
  -- comment marker rather than an explicit zero (which Jasmin doesn't
  -- have a clean syntax for at the `reg u64` level). This keeps the
  -- emit going for protocols like K3 Lizard that declare locals via
  -- `rc_let` (added 2026-05-01).
  | .Cassgn (.Lvar x) _ _ (.Parr_init _) =>
      some (ind ++ "// " ++ x.var.vname ++ " : zero-init array (omitted)")
  | .Cassgn (.Lvar x) _ _ (.Pconst z) =>
      some (ind ++ x.var.vname ++ " = " ++ toString z ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Papp1 (.Oword_of_int _) (.Pconst z)) =>
      some (ind ++ x.var.vname ++ " = " ++ toString z ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Pvar y) =>
      some (ind ++ x.var.vname ++ " = " ++ y.gv.var.vname ++ ";")
  -- Memory load: `x = [:uNN base + k];`  (Extension 2B: memory support,
  -- constant offset). `jasminc` parses this as a scaled `uNN` load at
  -- `base + k` bytes (despite the name, `k` here is a byte offset). The
  -- access width `ws` is carried in the `Pload`; `u64` and `u32` both
  -- emit; the *byte* offset `k` already encodes the per-limb stride
  -- (8 for u64, 4 for u32) chosen by the kernel `FunDecl`.
  | .Cassgn (.Lvar x) _ _ (.Pload ws base (.Pconst k)) =>
      some (ind ++ x.var.vname ++ " = [:" ++ wsizeTok ws ++ " " ++ base.var.vname ++
            " + " ++ toString k ++ "];")
  -- Memory store: `[:uNN base + k] = src;`.
  | .Cassgn (.Lmem ws base (.Pconst k)) _ _ (.Pvar src) =>
      some (ind ++ "[:" ++ wsizeTok ws ++ " " ++ base.var.vname ++ " + " ++ toString k ++
            "] = " ++ src.gv.var.vname ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Papp1 (.Olnot _) (.Pvar y)) =>
      let xn := x.var.vname
      let yn := y.gv.var.vname
      some (ind ++ xn ++ " = " ++ yn ++ ";\n" ++
            ind ++ xn ++ " = !" ++ xn ++ ";")
  -- Zero-extend a narrower word into a wider one: `x = (NNu) y;`.
  -- Used by the open-coded carry materialization, where a one-byte
  -- `#SETcc` result is widened into the u64 carry register (the x86
  -- `movzx` idiom). `jasminc` accepts `(64u) src` for the widening cast.
  | .Cassgn (.Lvar x) _ _ (.Papp1 (.Ozeroext wso _) (.Pvar y)) =>
      some (ind ++ x.var.vname ++ " = (" ++ toString (wsizeBits wso) ++ "u) " ++
            y.gv.var.vname ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Papp2 op (.Pvar y) (.Pvar z)) =>
      match binOpStr op with
      | none =>
          -- Not a compact-infix binop (e.g. `Olt`): render the full
          -- expression via `ppArithExpr` (`x = (y < z);`).
          (ppArithExpr (.Papp2 op (.Pvar y) (.Pvar z))).map
            (fun es => ind ++ x.var.vname ++ " = " ++ es ++ ";")
      | some opS =>
        let xn := x.var.vname
        let yn := y.gv.var.vname
        let zn := z.gv.var.vname
        if xn = yn then
          some (ind ++ xn ++ " " ++ opS ++ "= " ++ zn ++ ";")
        else if xn = zn then
          -- ALIAS GUARD: the dest aliases the second operand.  The compact
          -- `x = y; x OP= z;` expansion would clobber `z` (== `x`) before the
          -- `OP=`, computing `y OP y`.  Emit the single-expression form
          -- `x = (y OP z);` instead — jasminc lowers this correctly (it reads
          -- both operands before writing the destination).  Without this guard
          -- `r0 = r - r0` mis-compiles to `r0 = r; r0 -= r0;` (= 0).
          some (ind ++ xn ++ " = (" ++ yn ++ " " ++ opS ++ " " ++ zn ++ ");")
        else
          some (ind ++ xn ++ " = " ++ yn ++ ";\n" ++
                ind ++ xn ++ " " ++ opS ++ "= " ++ zn ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Papp2 op (.Pvar y) (.Pconst k)) =>
      match binOpStr op with
      | none =>
          (ppArithExpr (.Papp2 op (.Pvar y) (.Pconst k))).map
            (fun es => ind ++ x.var.vname ++ " = " ++ es ++ ";")
      | some opS =>
        let xn := x.var.vname
        let yn := y.gv.var.vname
        if xn = yn then
          some (ind ++ xn ++ " " ++ opS ++ "= " ++ toString k ++ ";")
        else
          some (ind ++ xn ++ " = " ++ yn ++ ";\n" ++
                ind ++ xn ++ " " ++ opS ++ "= " ++ toString k ++ ";")
  -- #262: `x = k OP y` with the *constant on the left*.  jasminc's asmgen
  -- cannot encode `dst = imm OP src` in one instruction (`reg = imm - reg`
  -- raises `(compile_arg) not compatible asm_arg`), so split into
  -- `x = k; x OP= y;` (load the immediate, then accumulate the variable).
  -- For `0 - y` this is the negation idiom `x = 0; x -= y;`, which jasminc
  -- lowers to `NEG`.  The `xn = yn` alias case (`x = k OP x`) is safe because
  -- `x = k` overwrites `x` before the `OP= y` reads it — except when `y` also
  -- aliases `x`, handled by emitting the read-before-write expression form.
  | .Cassgn (.Lvar x) _ _ (.Papp2 (.Osub _) (.Pconst 0) (.Pvar y)) =>
      -- `x = 0 - y` → unary negation `x = -y;` (jasminc lowers to `NEG`; the
      -- `0 - y` subtraction form is rejected by asmgen).  Safe under aliasing.
      some (ind ++ x.var.vname ++ " = -" ++ y.gv.var.vname ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Papp2 op (.Pconst k) (.Pvar y)) =>
      match binOpStr op with
      | none =>
          (ppArithExpr (.Papp2 op (.Pconst k) (.Pvar y))).map
            (fun es => ind ++ x.var.vname ++ " = " ++ es ++ ";")
      | some opS =>
        let xn := x.var.vname
        let yn := y.gv.var.vname
        if xn = yn then
          -- alias `x = k OP x`: stage the immediate in a copy first via the
          -- single-expression form (jasminc reads both operands before write).
          some (ind ++ xn ++ " = (" ++ toString k ++ " " ++ opS ++ " " ++ yn ++ ");")
        else
          some (ind ++ xn ++ " = " ++ toString k ++ ";\n" ++
                ind ++ xn ++ " " ++ opS ++ "= " ++ yn ++ ";")
  -- Opaque x86 intrinsic via `Copn`. Each lval is either a discarded
  -- flag (`Lnone` → `_`) or a named output (`Lvar name` → `name`).
  -- Each arg is a `Pvar` or `Pconst`.  Examples:
  --   `_, _, _, _, _, r = #LZCNT(a);`                   (all flags discarded)
  --   `of, cf, sf, pf, zf, r0 = #ADD_64(a0, b0);`       (flags kept as regs)
  --   `_, cf, _, _, _, r = #ADC_64(a, b, cf);`          (only carry kept)
  --   `r = #BSWAP_64(a);`                                (no flags)
  | .Copn lvs _ (.Oasm op) args => do
      let lvStrs ← lvs.mapM (fun
        | .Lnone _ _ => some "_"
        | .Lvar x    => some x.var.vname
        | _ => none)
      let argStrs ← args.mapM (fun
        | .Pvar gv => some gv.gv.var.vname
        | .Pconst k => some (toString k)
        -- Memory load as intrinsic arg: `#MULX(rdx, [:u64 bp + 16])`.
        -- x86 MULX supports a memory operand for its second source, which
        -- saves a register in tight schoolbook-multiplication kernels.
        | .Pload ws base (.Pconst k) =>
            some ("[:" ++ wsizeTok ws ++ " " ++ base.var.vname ++ " + " ++ toString k ++ "]")
        | _ => none)
      let lhs := String.intercalate ", " lvStrs
      let argStr := String.intercalate ", " argStrs
      some (ind ++ lhs ++ " = #" ++ op.name ++ "(" ++ argStr ++ ");")
  -- Extension 3A: counted for-loop. Only `.UpTo` with compile-time
  -- known `lo`/`hi` is emitted. The body is rendered with a deeper
  -- indent, and each body instruction must itself be emission-supported.
  | .Cfor vi range body =>
      match range.dir with
      | .UpTo => do
        let bodyStrs ← body.mapM (emitInstr (ind ++ "  "))
        let bodyStr := String.intercalate "\n" bodyStrs
        some (ind ++ "for " ++ vi.var.vname ++ " = " ++
              toString range.lo ++ " to " ++ toString range.hi ++ " {\n" ++
              bodyStr ++ "\n" ++ ind ++ "}")
      | .DownTo => none
  -- Extension 3B: runtime while-loop. The condition must be a simple
  -- comparison of a loop-counter variable to zero, and `cbefore` must
  -- be empty (the standard `while (n != 0) { body }` shape). Any other
  -- shape fails emission conservatively.
  --
  -- Emission: `while (n != 0) { <cafter> }`. Jasmin compiles this to
  -- the `cmp 0; jne loopHeader` pattern we verified with `jasminc`. The
  -- guard width (`Oneq .U64` / `.U32`) is the counter register's width;
  -- the surface form `n != 0` is width-independent.
  | .Cwhile [] (.Papp2 (.Oneq _) (.Pvar gv) (.Pconst 0)) cafter =>
      do
      let bodyStrs ← cafter.mapM (emitInstr (ind ++ "  "))
      let bodyStr := String.intercalate "\n" bodyStrs
      some (ind ++ "while (" ++ gv.gv.var.vname ++ " != 0) {\n" ++
            bodyStr ++ "\n" ++ ind ++ "}")
  -- Variant: `cond = (n != (word_of_int 0))`, produced by some
  -- frontends. Semantically identical.
  | .Cwhile [] (.Papp2 (.Oneq _) (.Pvar gv)
                  (.Papp1 (.Oword_of_int _) (.Pconst 0))) cafter =>
      do
      let bodyStrs ← cafter.mapM (emitInstr (ind ++ "  "))
      let bodyStr := String.intercalate "\n" bodyStrs
      some (ind ++ "while (" ++ gv.gv.var.vname ++ " != 0) {\n" ++
            bodyStr ++ "\n" ++ ind ++ "}")
  -- Conditional branch on a counter-style inequality `(gv != 0)`. This is
  -- the same `Papp2 (Oneq _) (Pvar _) (Pconst 0)` guard shape accepted by
  -- the `Cwhile` clause above (and by `isCT_Cmd`'s `Cif` whitelist). It
  -- covers the sign-equality / `mpn_compare`-result branches used by the
  -- signed-mpz dispatcher in `Mpn.SignedJasminPrototype.lean`. The bodies
  -- are rendered with a deeper indent; an unsupported body instruction
  -- propagates `none` as everywhere else. Emitted form:
  --   if (<gv> != 0) {
  --     <then>
  --   } else {
  --     <else>
  --   }
  | .Cif (.Papp2 (.Oneq _) (.Pvar gv) (.Pconst 0)) th el => do
      let thStrs ← th.mapM (emitInstr (ind ++ "  "))
      let elStrs ← el.mapM (emitInstr (ind ++ "  "))
      let thStr := String.intercalate "\n" thStrs
      let elStr := String.intercalate "\n" elStrs
      some (ind ++ "if (" ++ gv.gv.var.vname ++ " != 0) {\n" ++
            thStr ++ "\n" ++ ind ++ "} else {\n" ++
            elStr ++ "\n" ++ ind ++ "}")
  -- Built-in binop *Ccall* lowering: `Ccall _ [Lvar dst] fn [Pvar a, Pvar b]`
  -- where `fn.name` is one of `Add`/`Sub`/`Mul`/`BitXor`/`BitAnd`/`BitOr`/
  -- `Shl`/`Shr` (plus width-suffixed variants like `BitXor#32`) — emit it
  -- as a Jasmin infix `dst = a; dst OP= b;` (the two-operand form already
  -- used by the `Cassgn (Papp2 …)` arms above). `jasminc` has no callable
  -- functions named `BitXor` etc., so without this rewrite the bench-side
  -- AST-direct chain would emit `dst = BitXor(a, b);` which `jasminc`
  -- rejects. `LowCTToJasmin.toJasminCmd`'s `RCall f dest args` arm lowers
  -- to a `Ccall .DoNotInline [locToLVal dest] { name := f } …`, so this is
  -- the on-ramp the bench drivers (e.g. MAYO `sign_rwhile`) need to land
  -- per-iter scalar work inside an `RWhileNz` body. The previous infix
  -- rewriter lived only in `RustEmitJazz.lean` (the deprecated Rust-shaped
  -- path); this arm gives the canonical AST-direct path the same coverage.
  --
  -- Falls through for any other shape (multi-return, more/fewer than two
  -- `Pvar` args, non-binop name, …) to the regular function-call emit.
  | .Ccall _ii [.Lvar dst] fn [.Pvar a, .Pvar b] =>
      match binOpNameStr fn.name with
      | some opS =>
          let xn := dst.var.vname
          let yn := a.gv.var.vname
          let zn := b.gv.var.vname
          if xn = yn then
            some (ind ++ xn ++ " " ++ opS ++ "= " ++ zn ++ ";")
          else
            some (ind ++ xn ++ " = " ++ yn ++ ";\n" ++
                  ind ++ xn ++ " " ++ opS ++ "= " ++ zn ++ ";")
      | none =>
          -- Not a builtin binop — emit as a regular single-return function
          -- call: `dst = fn(a, b);`. Mirrors the multi-arg `Ccall` arm below.
          some (ind ++ dst.var.vname ++ " = " ++ fn.name ++
                "(" ++ a.gv.var.vname ++ ", " ++ b.gv.var.vname ++ ");")
  -- Function call: `lvs = fn(args);` (or just `fn(args);` for void).
  --
  -- Each lval is `Lvar name → name` or `Lnone → _`; each arg is
  -- `Pvar name`, `Pconst k`, or `Pload [:u64 base + k]`. The
  -- `InlineInfo` tag is consumed at compile-time by jasminc when it
  -- chooses a calling convention, but does not appear in surface
  -- syntax — `inline` / non-inline is a property of the callee's
  -- declaration, not the call site. Examples:
  --   `bignum_add_4(op, ap, bp);`            (void return)
  --   `r0, r1, r2, r3 = bignum_sqr_4(a0, a1, a2, a3);` (multi-return)
  | .Ccall _ii lvs fn args => do
      let lvStrs ← lvs.mapM (fun
        | .Lnone _ _ => some "_"
        | .Lvar x    => some x.var.vname
        | _ => none)
      let argStrs ← args.mapM (fun
        | .Pvar gv => some gv.gv.var.vname
        | .Pconst k => some (toString k)
        | .Pload ws base (.Pconst k) =>
            some ("[:" ++ wsizeTok ws ++ " " ++ base.var.vname ++ " + " ++ toString k ++ "]")
        | _ => none)
      let argStr := String.intercalate ", " argStrs
      if lvs.isEmpty then
        some (ind ++ fn.name ++ "(" ++ argStr ++ ");")
      else
        let lhs := String.intercalate ", " lvStrs
        some (ind ++ lhs ++ " = " ++ fn.name ++ "(" ++ argStr ++ ");")
  -- Phase DD (2026-05-28): literal-index array element load/store.
  -- `Cassgn (Laset _ ws arr (Pconst i)) _ _ (Pvar src)`  ↦  `arr[i] = src;`
  -- `Cassgn (Lvar dst) _ _ (Pget _ ws arr (Pconst i))`   ↦  `dst = arr[i];`
  -- These are the literal-index array slots emitted by
  -- `LowCTToJasmin.toJasminCmd` for the `RArrStoreLit`/`RArrLoadLit`
  -- constructors.  Jasmin's surface syntax accepts an integer literal in
  -- the bracket position directly, so we just stringify the `Pconst`.
  | .Cassgn (.Laset _ _ arr (.Pconst i)) _ _ (.Pvar src) =>
      some (ind ++ arr.var.vname ++ "[" ++ toString i ++ "] = " ++
            src.gv.var.vname ++ ";")
  | .Cassgn (.Lvar dst) _ _ (.Pget _ _ arr (.Pconst i)) =>
      some (ind ++ dst.var.vname ++ " = " ++ arr.gv.var.vname ++ "[" ++
            toString i ++ "];")
  -- Phase RND (2026-05-30): dynamic-index array store / load.  The bracket
  -- holds a register expression (a loop counter, possibly with arithmetic
  -- offset) rather than a `Pconst`.  Emitted by `LowCTToJasmin`'s
  -- `RArrStore`/`RArrLoad` arms.  jasminc scales the (`AAscale`) index by the
  -- element word size, so `arr[i]` selects the `i`-th `u32`.
  | .Cassgn (.Laset .AAscale _ arr idx) _ _ (.Pvar src) => do
      let is ← ppArithExpr idx
      some (ind ++ arr.var.vname ++ "[" ++ is ++ "] = " ++ src.gv.var.vname ++ ";")
  -- Dynamic-index store with a narrowing cast `arr[i] = (32u) src;`.
  | .Cassgn (.Laset .AAscale _ arr idx) _ _ (.Papp1 (.Ozeroext wso _) src) => do
      let is ← ppArithExpr idx
      let ss ← ppArithExpr src
      some (ind ++ arr.var.vname ++ "[" ++ is ++ "] = (" ++
            toString (wsizeBits wso) ++ "u) " ++ ss ++ ";")
  | .Cassgn (.Lvar dst) _ _ (.Pget .AAscale _ arr idx) => do
      let is ← ppArithExpr idx
      some (ind ++ dst.var.vname ++ " = " ++ arr.gv.var.vname ++ "[" ++ is ++ "];")
  -- Phase RND (2026-05-30): runtime-scalar arithmetic assignment.  The RHS is
  -- a nested arithmetic `PExpr` (`Papp2`/`Papp1`/`Pget`/`Pvar`/`Pconst`)
  -- produced by `sexprToPExpr`.  Render it via the recursive `ppArithExpr`.
  -- This arm is placed LAST among the `Cassgn (.Lvar _)` arms so the
  -- specific flat shapes above (single `Pvar`, single `Pconst`, two-operand
  -- `Papp2`) take priority and emit their compact two-operand form; only
  -- nested expressions reach here.
  | .Cassgn (.Lvar x) _ _ rhs => do
      let es ← ppArithExpr rhs
      some (ind ++ x.var.vname ++ " = " ++ es ++ ";")
  | _ => none

/-- Emit all instructions, separated by newlines. -/
def emitBody (ind : String) (body : List InstrR) : Option String :=
  body.mapM (emitInstr ind) |>.map (String.intercalate "\n")

/-! ## Optimization pipeline (applied before emission)

Three pre-emission optimizations:

1. **Arithmetic peephole** (`peepholeArith`). For the identity
   `x := a OP b; y := x OP' b;` where `x` is dead after `y` and
   `OP`/`OP'` form a cancelling pair — currently add ↔ sub — rewrite to
   `y := a;` (a copy). Covers `(b+a) − b = a` and `(a+b) − b = a`.
2. **Dead-code elimination** (`deadCodeElim` from the in-repo
   `Passes/DeadCode.lean`). Drops `Cassgn`s whose LHS is not live
   afterwards. Cheap liveness analysis.
3. **BSWAP_64 intrinsic path.** When a port uses `Copn` with `Oasm`
   name `"BSWAP_64"` (or any such intrinsic), `emitInstr` now emits
   the Jasmin source form `x = #BSWAP_64(y);`. `jasminc` lowers this
   to a single `bswap` — matching s2n's hand-written `word_bytereverse`.

The three compose cleanly: `peepholeArith` feeds into `deadCodeElim`
(which cleans up the now-dead producer assignment), and both run over
the input to `emitBody`. -/

/-- Count how many instructions in `body` read the variable named `x`. -/
def countReads (x : String) (body : List InstrR) : Nat :=
  body.foldl (init := 0) fun n i =>
    n + (instrReads i).foldl (init := 0) fun k v => if v.vname = x then k + 1 else k

/-- Count how many instructions in `body` write the variable named `x`. Used by
    the copy-coalescer to refuse merging `x := y OP z` into `y` when `y` is
    re-defined later in the tail: after renaming `x → y`, a later renamed read of
    `x` would otherwise read the *re-defined* `y` instead of the value that was
    held in `x`. -/
def countWrites (x : String) (body : List InstrR) : Nat :=
  body.foldl (init := 0) fun n i =>
    n + (instrWrites i).foldl (init := 0) fun k v => if v.vname = x then k + 1 else k

/-- Pairs of cancelling binary ops: `.Oadd` + `.Osub` cancel. Returns `true`
    iff applying `op1` then `op2` with the same RHS is the identity. -/
def cancelsWith : SOp2 → SOp2 → Bool
  | .Oadd .U64, .Osub .U64 => true
  | .Osub .U64, .Oadd .U64 => true
  | .Oadd .U32, .Osub .U32 => true
  | .Osub .U32, .Oadd .U32 => true
  | _, _ => false

/-- One pass of the arithmetic peephole, left-to-right.
    Rewrites `[… ; x := a OP c ; y := x OP' c ; …]` into
    `[… ; y := a ; …]` when `x` is read exactly once and `OP` / `OP'`
    cancel. (Also handles `x := c OP a` on the first, when `OP` is
    commutative — we restrict to `Oadd` there.) -/
def peepholeArith : List InstrR → List InstrR
  | [] => []
  | (i1@(.Cassgn (.Lvar x) _ ty1
       (.Papp2 op1 (.Pvar ya) (.Pvar c1)))) ::
    (.Cassgn (.Lvar y) _ _ (.Papp2 op2 (.Pvar xr) (.Pvar c2))) :: rest =>
    if xr.gv.var.vname = x.var.vname ∧ c1.gv.var.vname = c2.gv.var.vname ∧
       cancelsWith op1 op2 ∧ countReads x.var.vname rest = 0 then
      peepholeArith (.Cassgn (.Lvar y) .AT_none ty1 (.Pvar ya) :: rest)
    -- Commutative add: `x := c OP a; y := x - c;` → `y := a;`
    else if xr.gv.var.vname = x.var.vname ∧ c2.gv.var.vname = ya.gv.var.vname ∧
       cancelsWith op1 op2 ∧ (op1 = .Oadd .U64 ∨ op1 = .Oadd .U32) ∧
       countReads x.var.vname rest = 0 then
      peepholeArith (.Cassgn (.Lvar y) .AT_none ty1 (.Pvar c1) :: rest)
    else i1 :: peepholeArith (.Cassgn (.Lvar y) .AT_none ty1
           (.Papp2 op2 (.Pvar xr) (.Pvar c2)) :: rest)
  | i :: rest => i :: peepholeArith rest

/-! ### Copy coalescing

The emitter produces `x = y; x OP= z;` for every binary op. When `y` has no
uses after this instruction and is not in `liveOut`, we can rewrite to
`y := y OP z` — dropping the copy entirely and reusing `y`'s register —
then rename `x → y` in everything after. This shaves the redundant `movq`
that jasminc's register allocator sometimes can't coalesce. -/

/-- Rename variable `old` → `new` inside a `PExpr`. -/
def renameExpr (old new : String) : PExpr → PExpr
  | .Pvar gv =>
    if gv.gv.var.vname = old then
      let v' : Var := { gv.gv.var with vname := new }
      .Pvar { gv with gv := { gv.gv with var := v' } }
    else .Pvar gv
  | .Papp1 op e => .Papp1 op (renameExpr old new e)
  | .Papp2 op a b => .Papp2 op (renameExpr old new a) (renameExpr old new b)
  | .Pif ty c t f =>
    .Pif ty (renameExpr old new c) (renameExpr old new t) (renameExpr old new f)
  | e => e

/-- Rename in an l-value. -/
def renameLVal (old new : String) : LVal → LVal
  | .Lvar x =>
    if x.var.vname = old then
      .Lvar { x with var := { x.var with vname := new } }
    else .Lvar x
  | lv => lv

/-- Rename in one instruction. -/
def renameInstr (old new : String) : InstrR → InstrR
  | .Cassgn lv tag ty e =>
    .Cassgn (renameLVal old new lv) tag ty (renameExpr old new e)
  | .Copn lvs tag op es =>
    .Copn (lvs.map (renameLVal old new)) tag op (es.map (renameExpr old new))
  | i => i

/-- Rename in a liveOut (list of Vars). -/
def renameLiveOut (old new : String) : List Var → List Var :=
  List.map (fun v => if v.vname = old then { v with vname := new } else v)

/-- Copy-coalescing pass (one forward sweep; apply renames into the tail).
    For `x := y OP z` with `y` having no uses in the rest of the body and
    not in `liveOut`, rewrite to `y := y OP z` and rename `x → y` in the
    tail. Returns the rewritten body and the (possibly renamed) `liveOut`.

    The merge is sound only if `y` is also never **written** again in the tail
    (`countWrites yn rest = 0`): renaming `x → y` turns every later read of `x`
    into a read of `y`, so a later native re-definition of `y` would feed those
    reads the wrong value. This is the hazard that miscompiled the Pasta
    Montgomery reduce's conditional subtract — the shared carry scratch (`_g*`)
    is rewritten across columns, and a coalesced `x → _g*` rename then aliased a
    re-defined `_g*` in the final borrow chain, corrupting the select. -/
def coalesceGo
    (liveOut : List Var) : List InstrR → List InstrR × List Var
  | [] => ([], liveOut)
  | i :: rest =>
    match i with
    | .Cassgn (.Lvar x) tag ty (.Papp2 op (.Pvar y) (.Pvar z)) =>
      let yn := y.gv.var.vname
      let xn := x.var.vname
      let zn := z.gv.var.vname
      let canMerge :=
        xn ≠ yn ∧ yn ≠ zn ∧
        countReads yn rest = 0 ∧ countWrites yn rest = 0 ∧
        ¬(liveOut.any (·.vname = yn))
      if canMerge then
        let newLv : LVal := .Lvar { var := y.gv.var, info := x.info }
        let newInstr : InstrR := .Cassgn newLv tag ty (.Papp2 op (.Pvar y) (.Pvar z))
        let renamedRest := rest.map (renameInstr xn yn)
        let (tail, lo') := coalesceGo (renameLiveOut xn yn liveOut) renamedRest
        (newInstr :: tail, lo')
      else
        let (tail, lo') := coalesceGo liveOut rest
        (i :: tail, lo')
    | .Cassgn (.Lvar x) tag ty (.Papp2 op (.Pvar y) (.Pconst k)) =>
      let yn := y.gv.var.vname
      let xn := x.var.vname
      let canMerge :=
        xn ≠ yn ∧ countReads yn rest = 0 ∧ countWrites yn rest = 0 ∧
        ¬(liveOut.any (·.vname = yn))
      if canMerge then
        let newLv : LVal := .Lvar { var := y.gv.var, info := x.info }
        let newInstr : InstrR := .Cassgn newLv tag ty (.Papp2 op (.Pvar y) (.Pconst k))
        let renamedRest := rest.map (renameInstr xn yn)
        let (tail, lo') := coalesceGo (renameLiveOut xn yn liveOut) renamedRest
        (newInstr :: tail, lo')
      else
        let (tail, lo') := coalesceGo liveOut rest
        (i :: tail, lo')
    | _ =>
      let (tail, lo') := coalesceGo liveOut rest
      (i :: tail, lo')
termination_by body => body.length
decreasing_by
  all_goals (first | simp [List.length_map, List.length_cons] | omega)

/-! ### Constant propagation for single-use immediates

`c = Pconst k ; ... ; y = a OP c ;` becomes `... ; y = a OP k ;` —
the constant is inlined and the original definition is dropped. This
matches what s2n-bignum writes by hand (e.g. `xorq $2, %rax`) and
avoids a superfluous `movq $k, %reg` before the op.

Scope: only substitute when the constant-valued variable is used
**exactly once** in the body and the use is as the **right** operand
of a binary op (so the emitter's `Papp2 op (.Pvar _) (.Pconst k)` case
fires). For commutative ops where the constant is on the left, we
don't (yet) swap — our SSA builder always places constants on the
right so this is fine for the current ports. -/

/-- Collect single-use constant definitions eligible for folding.

    A `x := Pconst k` is foldable only when (a) `x` is read **exactly once**
    across the whole body (`uses`), and (b) `x` is **never written again** in
    the instructions following this definition (`countWrites … rest = 0`).

    Condition (b) is the soundness guard. Without it, a zero-initialization
    declaration (`x := 0`) that is later **re-defined** (`x := a OP b`) would be
    mistaken for the reaching definition of `x`'s single downstream read: the
    fold would replace that read — which actually observes the re-defined
    value — with the literal `0`, and drop the (irrelevant) initializer.
    This is exactly what corrupted the Pasta Montgomery reduce's conditional
    subtract: the per-scalar `declScalar` zero-inits alias the carry-mask
    scratch (`_gC*`) and borrow accumulator (`_co*`), whose real definitions
    come later, so `_gB &= _gC` folded to `_gB &= 0` and `bor := 1 - _co`
    folded to `bor := 1 - 0`. Requiring no later write to `x` makes the const
    def the unique reaching definition for the read, which is the condition
    under which inlining-and-dropping is value-preserving. -/
def collectSingleUseConsts
    (body : List InstrR) (uses : String → Nat) : List (String × Int) :=
  let rec go : List InstrR → List (String × Int)
    | [] => []
    | i :: rest =>
      match i with
      | .Cassgn (.Lvar x) _ _ (.Pconst k) =>
          if uses x.var.vname = 1 ∧ countWrites x.var.vname rest = 0 then
            (x.var.vname, k) :: go rest
          else go rest
      | _ => go rest
  go body

/-- Names of variables that appear as the **right** Pvar operand of some
    `Papp2` anywhere in the body — these are the ones we can actually fold
    (the emitter's `… .Papp2 op (.Pvar _) (.Pconst _)` case fires there). -/
def rightOperandVars : List InstrR → List String :=
  List.flatMap (fun i =>
    match i with
    | .Cassgn _ _ _ (.Papp2 _ _ (.Pvar gv)) => [gv.gv.var.vname]
    | _ => [])

def dropConstDefs (names : List String) : List InstrR → List InstrR :=
  List.filter (fun i =>
    match i with
    | .Cassgn (.Lvar x) _ _ (.Pconst _) => !names.contains x.var.vname
    | _ => true)

def substRightOp (cm : List (String × Int)) : InstrR → InstrR
  | .Cassgn lv tag ty (.Papp2 op a (.Pvar gv)) =>
      match cm.find? (·.1 = gv.gv.var.vname) with
      | some (_, k) =>
          .Cassgn lv tag ty (.Papp2 op a (.Pconst k))
      | none =>
          .Cassgn lv tag ty (.Papp2 op a (.Pvar gv))
  | i => i

def propagateConstants (body : List InstrR) : List InstrR :=
  let uses := fun name => countReads name body
  -- Candidates: single-use constants
  let candidates := collectSingleUseConsts body uses
  -- Filter down to those that are actually right-operands somewhere, so the
  -- emitter can consume the folded form. Otherwise dropping the const def
  -- leaves a dangling reference (e.g., for `m &= a` where m is on the LEFT).
  let folding := candidates.filter (fun (n, _) => (rightOperandVars body).contains n)
  let foldingNames := folding.map (·.1)
  dropConstDefs foldingNames body |>.map (substRightOp folding)

/-- Public entry point: apply all four optimization passes and return the
    optimized body together with the (possibly renamed) `liveOut`. Order:
    peephole → constprop → DCE → copy-coalesce. -/
def optimize (liveOut : List Var) (body : List InstrR) : List InstrR × List Var :=
  let phase1 := peepholeArith body
  let phase2 := propagateConstants phase1
  let phase3 := deadCodeElim liveOut phase2
  coalesceGo liveOut phase3

/-! ### Recursive structural helpers for Cfor

`emitFunDecl` needs to (a) detect flag-producing `Copn`s inside loop
bodies, and (b) collect loop index names so they're declared as
`inline int` rather than `reg u64`. These helpers traverse the
instruction tree. -/

/-- Does any instruction (or nested instruction) produce flag outputs?
    Recurses into `Cfor`, `Cwhile`, and `Cif` bodies — a flag-producing
    intrinsic inside a branch arm must trigger the `reg bool …;` declaration
    just as much as one at the top level. -/
partial def hasFlagCopn : List InstrR → Bool
  | [] => false
  | .Copn lvs _ _ _ :: rest =>
      (lvs.any (fun | .Lnone _ _ => true | _ => false)) || hasFlagCopn rest
  | .Cfor _ _ body :: rest => hasFlagCopn body || hasFlagCopn rest
  | .Cwhile cbefore _ cafter :: rest =>
      hasFlagCopn cbefore || hasFlagCopn cafter || hasFlagCopn rest
  | .Cif _ th el :: rest =>
      hasFlagCopn th || hasFlagCopn el || hasFlagCopn rest
  | _ :: rest => hasFlagCopn rest

/-- Collect loop-index variable names from all `Cfor`s in the body,
    including nested ones. `Cwhile` has no index variable (the counter
    is a regular `reg u64`), so only its body is traversed. `Cif` arms
    are likewise recursed into — a `Cfor` nested under a branch still
    needs its index in the `inline int …;` declaration. -/
partial def collectLoopIdxNames : List InstrR → List String
  | [] => []
  | .Cfor vi _ body :: rest =>
      vi.var.vname :: collectLoopIdxNames body ++ collectLoopIdxNames rest
  | .Cwhile cbefore _ cafter :: rest =>
      collectLoopIdxNames cbefore ++ collectLoopIdxNames cafter
        ++ collectLoopIdxNames rest
  | .Cif _ th el :: rest =>
      collectLoopIdxNames th ++ collectLoopIdxNames el ++ collectLoopIdxNames rest
  | _ :: rest => collectLoopIdxNames rest

/-! ### GPR-use detection for flag-named variables

A variable named like an x86 status flag (`of`/`cf`/`sf`/`pf`/`zf`) is only a
`reg bool` flag if it appears **solely** in flag positions: as a
`Copn` flag-bundle `Lvar` output, or as a flag carry-input *operand* (a
top-level `Pvar` argument) of a flag-consuming intrinsic such as `#ADC_64` /
`#SBB_64`, possibly with a `Pconst 0` initializer.

If, instead, the variable is *used as a general-purpose register* — it is
read inside an arithmetic subexpression (`Papp1`/`Papp2`/`Pif`/`Pget`/`Psub`,
or a memory base/offset/index), or it is computed by an ordinary data
`Cassgn` whose RHS is not a bare `Pconst` (e.g. the open-coded carry
`cf = cf1 ||| cf2`, an `Olor`), or it is copied from another register
(`x = cf`), or it is a data l-value / `Ccall` output — then it must be
declared `reg u64`, not `reg bool`.

`emitFunDecl` subtracts the GPR-used names from the hardcoded flag-bank set so
that a flag-named *value* register (the open-coded `mpn_add_n` carry) is
declared and initialized as a u64, instead of being misclassified into the
`reg bool of cf sf pf zf;` bank (which makes `cf = 0` a spurious
`int → bool` cast). -/

/-- Names read in an **arithmetic / memory** context inside an
    expression: anything reached through `Papp1`/`Papp2`/`Pif`/`Pget`/`Psub`,
    or as a memory base/offset. A *bare* top-level `Pvar` is **not** counted
    here (so a top-level `Copn` carry-input operand like `#ADC_64(_, _, cf)`
    does not, by itself, mark `cf` as a GPR) — only `exprArithReads` reached
    through an operator/load contributes. -/
partial def exprArithReads : PExpr → List String
  | .Pvar gv => [gv.gv.var.vname]
  | .Pget _ _ x idx => x.gv.var.vname :: exprArithReads idx
  | .Psub _ _ _ x idx => x.gv.var.vname :: exprArithReads idx
  | .Pload _ x off => x.var.vname :: exprArithReads off
  | .Papp1 _ e => exprArithReads e
  | .Papp2 _ a b => exprArithReads a ++ exprArithReads b
  | .PappN _ es => (es.map exprArithReads).flatten
  | .Pif _ c t f => exprArithReads c ++ exprArithReads t ++ exprArithReads f
  | _ => []

/-- For a *top-level* expression appearing as a `Cassgn` RHS or `Copn` arg:
    collect names used in a GPR (arithmetic/memory) way, but treat a bare
    top-level `Pvar` as a non-arithmetic read (it could be a flag carry-input
    operand or a pure copy source, neither of which forces u64 on its own). -/
def topExprArithReads : PExpr → List String
  | .Pvar _ => []
  | e => exprArithReads e

/-- Names read from an l-value's index/base (always GPR-context). -/
def lvalArithReads : LVal → List String
  | .Lmem _ x off => x.var.vname :: exprArithReads off
  | .Laset _ _ x idx => x.var.vname :: exprArithReads idx
  | .Lasub _ _ _ x idx => x.var.vname :: exprArithReads idx
  | _ => []

/-- Is a `Cassgn` RHS a "computed value" (so its `Lvar` LHS is a GPR), as
    opposed to a bare `Pconst`/`Parr_init` initializer (which a flag register
    may also legitimately take, e.g. `cf = 0`)? -/
def isComputedRHS : PExpr → Bool
  | .Pconst _ => false
  | .Pbool _ => false
  | .Parr_init _ => false
  | _ => true

/-- Names that are used as general-purpose registers somewhere in the body
    (recursing through `Cfor`/`Cwhile`/`Cif`). A flag-named variable in this
    set must be declared `reg u64`. See the section docstring above. -/
partial def gprUsedNames : List InstrR → List String
  | [] => []
  | .Cassgn lv _ _ e :: rest =>
      -- LHS is a GPR if it holds a computed value (non-`Pconst` RHS).
      let lhsGpr := match lv with
        | .Lvar x => if isComputedRHS e then [x.var.vname] else []
        | _ => []
      lhsGpr ++ lvalArithReads lv ++ topExprArithReads e ++ gprUsedNames rest
  | .Copn lvs _ _ es :: rest =>
      -- A `Copn` `Lvar` output may be a flag-bundle output; do NOT mark it.
      -- Only arithmetic-context reads inside its args (and any l-value
      -- index/base) count.
      (lvs.flatMap lvalArithReads) ++ (es.flatMap topExprArithReads)
        ++ gprUsedNames rest
  | .Cif c th el :: rest =>
      exprArithReads c ++ gprUsedNames th ++ gprUsedNames el ++ gprUsedNames rest
  | .Cfor _ _ body :: rest =>
      -- `Range.lo`/`hi` are compile-time `Nat` bounds, not register reads.
      gprUsedNames body ++ gprUsedNames rest
  | .Cwhile cb cond ca :: rest =>
      gprUsedNames cb ++ exprArithReads cond ++ gprUsedNames ca ++ gprUsedNames rest
  | .Ccall _ lvs _ args :: rest =>
      -- `Ccall` `Lvar` outputs receive u64 return values; treat as GPR.
      let outs := lvs.filterMap (fun | .Lvar x => some x.var.vname | _ => none)
      outs ++ (lvs.flatMap lvalArithReads) ++ (args.flatMap topExprArithReads)
        ++ gprUsedNames rest

/-! ### Open-coded carry materialization

The flag-producing arithmetic intrinsics come in two bundle shapes:

* **6-LVal flag-prefix bundle** — `#ADD_64` / `#ADC_64` / `#SUB_64` / `#SBB_64`
  (and their `_32` variants): `[of, cf, sf, pf, zf, dst]`.  The carry-out slot
  (`cf`) is at bundle position **1**.

* **2-LVal compact bundle** — `#ADCX` / `#ADOX` (and their `_32` variants):
  `[flag_out, dst]`.  Only the relevant flag is updated:
  * `#ADCX` writes its carry-out to **CF** (position 0).
  * `#ADOX` writes its carry-out to **OF** (position 0).

At the Jasmin source level the captured flag slot is a `reg bool`. The
executable semantics (`BignumExec.writeSubBundle` for ADD_64/SUB_64/…;
`BignumExec.writeAdxBundle` for ADCX/ADOX), however, stores the flag value as a
u64 `{0,1}` into a *general-purpose* register — which is exactly what the
open-coded `mpn_add_n` carry needs (it `|`s two carry-outs and threads the
result across the loop back-edge as a u64), and what an ADCX/ADOX dual-chain
needs at its **tail** (to extract the final CF/OF as a u64 for cross-chain
fold or for comparison against a single-chain reference).

When the carry-out l-value of such a bundle is a `Lvar` whose name is used as a
GPR elsewhere (so it is *not* a physical-flag carry that only flows back into
another carry instruction), we materialize the architectural flag into the u64
register via the standard x86 `setcc` + `movzx` idiom:

```
_, <c>__f, _, _, _, dst = #ADD_64(a, b);   // 6-LVal: carry-out at position 1
<c>__b = #SETcc(<c>__f);                    // setb : reg bool -> reg u8
<c> = (64u) <c>__b;                         // movzx : reg u8 -> reg u64
```

and, for the 2-LVal ADCX/ADOX bundles (carry-out at position 0):

```
<c>__f, dst = #ADCX(dst, b, cin);          // 2-LVal: carry-out at position 0
<c>__b = #SETcc(<c>__f);                    // setb (CF) / seto (OF) — same #SETcc
<c> = (64u) <c>__b;                         // movzx : reg u8 -> reg u64
```

`#SETcc`'s input is a `reg bool` (the captured architectural flag); jasminc's
asm pretty-printer chooses `setb` / `seto` from the boolean condition tracked
in `pp_ct` (see `Ox86_SETcc_instr` in `x86_instr_decl.v`).  The instruction
selector lowers any `#SETcc(reg bool)` to the right `setcc` mnemonic regardless
of which arithmetic produced the bool, so the **same materialization recipe
works for CF (ADCX) and OF (ADOX)**.

The pass leaves bundles whose carry slot is `Lnone` (discarded) or a
physical-flag register (not GPR-used, e.g. the `cf` / `of` threaded through a
pure dual-chain) untouched, so existing `#ADC_64` and `#ADCX`/`#ADOX` chain
kernels emit exactly as before.

### OF=1 seed (read me before designing a sub-via-ADOX kernel)

The two's-complement rewrite `out − lo ≡ out + (~lo) + 1` produces a clean
ADOX chain *iff* the chain is seeded with `OF=1` (the `+1` of two's
complement).  Unlike `STC` for CF, **x86 has no `STO` instruction**, and
jasminc has no `#STO` primitive (`x86_instr_decl.v` exposes `CLC`/`STC` but
no `CLO`/`STO`).  Consequently the emitter cannot insert a one-instruction
OF=1 seed.

The cleanest workaround that requires **no jasminc-side change** is to seed
OF=1 by an overflowing add of two large positive immediates: the signed
sum `0x7fffffffffffffff + 0x7fffffffffffffff = -2` flips into the negative
half-plane, setting `OF=1` (and as a side-effect `CF=1` because the unsigned
sum `2^64 − 2` overflows out of u64; the CF side-effect is harmless because
the CF chain is initialised by `xorClearFlags` *after* the OF seed when both
chains are needed, or the CF carry-out is simply discarded if only the OF
chain matters here).

The emitted shape (jasminc-accepted; verified at the InstrR level by the
existing 6-LVal `#ADD_64` bundle handling in `S2NBignumSSA` / `MpnAdd*`):

```
of_seed, _, _, _, _, _scratch = #ADD_64(BIG, BIG);   // BIG = 0x7fffffffffffffff
of_seed, r0  = #ADOX(r0, ~lo0, of_seed);             // first ADOX uses OF=1
of_seed, r1  = #ADOX(r1, ~lo1, of_seed);             // chain continues normally
...
```

This is a **kernel-author recipe**, not an emit-pass extension: the kernel
author writes the InstrR list emitting the seed `#ADD_64` plus the subsequent
ADOX chain.  The helper `ofSeedToOneCopn` below packages the seed step for
reuse by kernels that want to switch from single-CF subtract to dual-chain
ADOX-of-complement subtract.  It produces a single `Copn` that captures `OF=1`
into a named `reg bool` ready to feed an ADOX chain — no emitter pass changes
needed beyond the SETcc materialization (Part 1 above), which already lands
the *output* OF as a u64 if a kernel author wants to bridge back to a
single-chain reference. -/

/-- The arithmetic intrinsics whose carry-out lval is a `reg bool` at the
    Jasmin level, paired with the bundle-position of the carry-out lval:

    * `1` for the 6-LVal `[of, cf, sf, pf, zf, dst]` bundles
      (`#ADD_64`/`#ADC_64`/`#SUB_64`/`#SBB_64`, both `_64` and `_32`).
    * `0` for the 2-LVal `[flag_out, dst]` bundles (`#ADCX`/`#ADOX`,
      both `_64` and `_32`).

    `none` when the op is not a flag-producing carry bundle. -/
def carryBundleCarryIdx (name : String) : Option Nat :=
  if name = "ADD_64" || name = "ADC_64" || name = "SUB_64" || name = "SBB_64"
     || name = "ADD_32" || name = "ADC_32" || name = "SUB_32" || name = "SBB_32"
  then some 1
  else if name = "ADCX" || name = "ADOX" || name = "ADCX_32" || name = "ADOX_32"
  then some 0
  else none

/-- Backward-compatible: `true` iff the op has a `reg bool` carry-out lval.
    Now covers both the 6-LVal (ADD/ADC/SUB/SBB) and 2-LVal (ADCX/ADOX) bundles.
    Both the 64-bit and 32-bit limb widths use the same per-shape layout, so
    the open-carry materialization applies to either. -/
def isCarryBundleOp (name : String) : Bool :=
  (carryBundleCarryIdx name).isSome

/-- Per-carry-name temporaries for the materialization idiom. -/
def carryFlagTmp (c : String) : String := c ++ "__f"
def carryByteTmp (c : String) : String := c ++ "__b"

/-- The `Lvar` at bundle position `idx`, if any.  Helper for
    `carryBundleName` — looks up the carry-out slot at the shape-specific
    index (0 for ADCX/ADOX, 1 for ADD/ADC/SUB/SBB). -/
def lvAt? (lvs : List LVal) (idx : Nat) : Option String :=
  match lvs[idx]? with
  | some (.Lvar v) => some v.var.vname
  | _ => none

/-- Does this `Copn` need carry materialization, and if so what is the
    carry-register name?  Returns the bundle-shape-specific carry-slot `Lvar`
    name when the op is a carry bundle and that name is in `gprFlags`.

    Shape-specific slot index:
    * `1` for ADD/ADC/SUB/SBB (6-LVal `[of, cf, sf, pf, zf, dst]`).
    * `0` for ADCX/ADOX (2-LVal `[flag_out, dst]`). -/
def carryBundleName (gprFlags : List String) : InstrR → Option String
  | .Copn lvs _ (.Oasm op) _ =>
      match carryBundleCarryIdx op.name with
      | some idx =>
          match lvAt? lvs idx with
          | some name => if gprFlags.contains name then some name else none
          | none => none
      | none => none
  | _ => none

/-- Rewrite the carry-out slot of a carry bundle to a fresh `reg bool`, and
    append the `#SETcc` + zero-extend that lands the carry in the limb-width
    register `c`. The zero-extend target width `limbWS` is the kernel's GPR
    limb width (`U64` for the 64-bit kernels, `U32` for the 32-bit re-emission):
    the `#SETcc` always lands a `reg u8`, then `(64u)`/`(32u)` widens it into
    the threaded carry register.  The bundle's carry-slot position is `1` for
    the 6-LVal ADD/ADC/SUB/SBB bundles and `0` for the 2-LVal ADCX/ADOX
    bundles — looked up via `carryBundleCarryIdx`.  Non-matching instructions
    are returned unchanged. -/
def expandCarryInstr (limbWS : WSize) (gprFlags : List String) (i : InstrR) : List InstrR :=
  match i with
  | .Copn lvs tag (.Oasm op) args =>
      match carryBundleName gprFlags i with
      | some c =>
          -- The bundle-specific carry-slot index — guaranteed `some` here
          -- because `carryBundleName` already filtered on `carryBundleCarryIdx`.
          let carryIdx := (carryBundleCarryIdx op.name).getD 1
          let fTmp := carryFlagTmp c
          let bTmp := carryByteTmp c
          -- Redirect the bundle's carry-out slot to a fresh reg bool.
          let lvs' := lvs.zipIdx.map (fun (lv, idx) =>
            if idx = carryIdx then .Lvar { var := { vname := fTmp, vtype := .sbool } }
            else lv)
          [ .Copn lvs' tag (.Oasm op) args
          , .Copn [.Lvar { var := { vname := bTmp, vtype := .sword .U8 } }]
              tag (.Oasm ⟨"SETcc"⟩)
              [.Pvar { gv := { var := { vname := fTmp, vtype := .sbool } }, gs := false }]
          , .Cassgn (.Lvar { var := { vname := c, vtype := .sword limbWS } })
              tag (.sword limbWS)
              (.Papp1 (.Ozeroext limbWS .U8)
                (.Pvar { gv := { var := { vname := bTmp, vtype := .sword .U8 } },
                         gs := false })) ]
      | none => [i]
  | _ => [i]

/-- **OF=1 seed recipe** — produce a `Copn` that captures `OF=1` into a named
    `reg bool` ready to feed an `#ADOX` chain.

    Emitted shape (jasminc-accepted, 6-LVal `#ADD_64` bundle):

    ```
    <ofName>, _, _, _, _, <scratch> = #ADD_64(0x7fffffffffffffff, 0x7fffffffffffffff);
    ```

    Arithmetic: `0x7fff...f + 0x7fff...f = 0xfffe (unsigned) = -2 (signed)`.
    Both inputs are positive, the signed result is negative — signed overflow
    sets `OF=1`.  The `scratch` u64 register absorbs the (unused) sum;
    the kernel author should declare it as `reg u64`.

    This is the cleanest emit-side OF=1 seed available without a jasminc-side
    `#STO` primitive.  See the §"OF=1 seed" docstring above. -/
def ofSeedToOneCopn (ofName scratch : String) : InstrR :=
  let bigPos : Int := 0x7fffffffffffffff
  let ofLv : LVal := .Lvar { var := { vname := ofName, vtype := .sbool } }
  let lnoneU64 : LVal := .Lnone {} (.sword .U64)
  let scratchLv : LVal := .Lvar { var := { vname := scratch, vtype := .sword .U64 } }
  .Copn [ofLv, lnoneU64, lnoneU64, lnoneU64, lnoneU64, scratchLv]
        .AT_none (.Oasm ⟨"ADD_64"⟩)
        [.Pconst bigPos, .Pconst bigPos]

/-- Apply `expandCarryInstr` throughout the body, recursing into loop / branch
    bodies. -/
partial def expandFlagCaptures (limbWS : WSize) (gprFlags : List String) :
    List InstrR → List InstrR
  | [] => []
  | .Cwhile cb cond ca :: rest =>
      .Cwhile (expandFlagCaptures limbWS gprFlags cb) cond
          (expandFlagCaptures limbWS gprFlags ca)
        :: expandFlagCaptures limbWS gprFlags rest
  | .Cfor vi rng body :: rest =>
      .Cfor vi rng (expandFlagCaptures limbWS gprFlags body)
        :: expandFlagCaptures limbWS gprFlags rest
  | .Cif c th el :: rest =>
      .Cif c (expandFlagCaptures limbWS gprFlags th) (expandFlagCaptures limbWS gprFlags el)
        :: expandFlagCaptures limbWS gprFlags rest
  | i :: rest =>
      expandCarryInstr limbWS gprFlags i ++ expandFlagCaptures limbWS gprFlags rest

/-- Names of carry registers that get materialized (need the `reg bool` /
    `reg u8` temporaries declared). -/
partial def materializedCarryNames (gprFlags : List String) : List InstrR → List String
  | [] => []
  | .Cwhile cb _ ca :: rest =>
      materializedCarryNames gprFlags cb ++ materializedCarryNames gprFlags ca
        ++ materializedCarryNames gprFlags rest
  | .Cfor _ _ body :: rest =>
      materializedCarryNames gprFlags body ++ materializedCarryNames gprFlags rest
  | .Cif _ th el :: rest =>
      materializedCarryNames gprFlags th ++ materializedCarryNames gprFlags el
        ++ materializedCarryNames gprFlags rest
  | i :: rest =>
      (carryBundleName gprFlags i).toList ++ materializedCarryNames gprFlags rest

/-! ### Smoke tests for carry materialization (ADCX/ADOX/ADD_64) -/

section CarryMaterializeSmoke

/-- The shape-specific carry-slot index is `1` for the 6-LVal `#ADD_64`
    bundle and `0` for the 2-LVal `#ADCX`/`#ADOX` bundles. -/
example : carryBundleCarryIdx "ADD_64" = some 1 := rfl
example : carryBundleCarryIdx "ADC_64" = some 1 := rfl
example : carryBundleCarryIdx "SUB_64" = some 1 := rfl
example : carryBundleCarryIdx "SBB_64" = some 1 := rfl
example : carryBundleCarryIdx "ADCX"   = some 0 := rfl
example : carryBundleCarryIdx "ADOX"   = some 0 := rfl
example : carryBundleCarryIdx "ADCX_32" = some 0 := rfl
example : carryBundleCarryIdx "ADOX_32" = some 0 := rfl
example : carryBundleCarryIdx "MULX"   = none := rfl
example : carryBundleCarryIdx "XOR_64" = none := rfl

/-- `isCarryBundleOp` is the `.isSome` view of `carryBundleCarryIdx`; both the
    legacy 6-LVal and new 2-LVal bundles are covered. -/
example : isCarryBundleOp "ADD_64" = true := rfl
example : isCarryBundleOp "ADCX"   = true := rfl
example : isCarryBundleOp "ADOX"   = true := rfl
example : isCarryBundleOp "MULX"   = false := rfl

/-- `expandCarryInstr` on an `#ADCX` with the carry-out lval marked as a
    GPR-used flag produces a 3-instruction sequence:
    1. the original `#ADCX` with position-0 redirected to a fresh `reg bool`
       (named `cf__f`)
    2. `#SETcc(cf__f)` into a `reg u8` (`cf__b`)
    3. a `Cassgn` zero-extending `cf__b` to the limb width into `cf` -/
example :
    let cfLv : LVal := .Lvar { var := { vname := "cf", vtype := .sword .U64 } }
    let dstLv : LVal := .Lvar { var := { vname := "r0", vtype := .sword .U64 } }
    let aPv : PExpr := .Pvar { gv := { var := { vname := "r0", vtype := .sword .U64 } }, gs := false }
    let bPv : PExpr := .Pvar { gv := { var := { vname := "lo0", vtype := .sword .U64 } }, gs := false }
    let cinPv : PExpr := .Pvar { gv := { var := { vname := "cf", vtype := .sword .U64 } }, gs := false }
    let adcxI : InstrR := .Copn [cfLv, dstLv] .AT_none (.Oasm ⟨"ADCX"⟩) [aPv, bPv, cinPv]
    (expandCarryInstr .U64 ["cf"] adcxI).length = 3 := by decide

/-- `expandCarryInstr` on an `#ADOX` with the carry-out lval marked as a
    GPR-used flag also expands (same SETcc + movzx tail). -/
example :
    let ofLv : LVal := .Lvar { var := { vname := "of", vtype := .sword .U64 } }
    let dstLv : LVal := .Lvar { var := { vname := "r0", vtype := .sword .U64 } }
    let aPv : PExpr := .Pvar { gv := { var := { vname := "r0", vtype := .sword .U64 } }, gs := false }
    let bPv : PExpr := .Pvar { gv := { var := { vname := "lo0", vtype := .sword .U64 } }, gs := false }
    let oinPv : PExpr := .Pvar { gv := { var := { vname := "of", vtype := .sword .U64 } }, gs := false }
    let adoxI : InstrR := .Copn [ofLv, dstLv] .AT_none (.Oasm ⟨"ADOX"⟩) [aPv, bPv, oinPv]
    (expandCarryInstr .U64 ["of"] adoxI).length = 3 := by decide

/-- `expandCarryInstr` on an `#ADCX` whose carry-out is **not** a GPR-used name
    leaves the instruction unchanged (length = 1) — preserves the existing
    `MpnAddMul1AdxPrototype` dual-chain emission where `cf`/`of` are pure
    `reg bool` threads. -/
example :
    let cfLv : LVal := .Lvar { var := { vname := "cf", vtype := .sword .U64 } }
    let dstLv : LVal := .Lvar { var := { vname := "r0", vtype := .sword .U64 } }
    let aPv : PExpr := .Pvar { gv := { var := { vname := "r0", vtype := .sword .U64 } }, gs := false }
    let bPv : PExpr := .Pvar { gv := { var := { vname := "lo0", vtype := .sword .U64 } }, gs := false }
    let cinPv : PExpr := .Pvar { gv := { var := { vname := "cf", vtype := .sword .U64 } }, gs := false }
    let adcxI : InstrR := .Copn [cfLv, dstLv] .AT_none (.Oasm ⟨"ADCX"⟩) [aPv, bPv, cinPv]
    -- gprFlags = []  ⇒  `cf` is not flagged for materialization
    (expandCarryInstr .U64 [] adcxI).length = 1 := by decide

/-- `ofSeedToOneCopn` produces a single `#ADD_64` `Copn` with the OF lval at
    bundle position 0 (the 6-LVal layout) and the two large-positive
    immediates as args.  This is the recipe for seeding `OF=1` into a
    `reg bool` ready to feed an `#ADOX` chain. -/
example :
    (match ofSeedToOneCopn "of_seed" "scratch" with
     | .Copn lvs _ (.Oasm ⟨n⟩) args =>
         (decide (n = "ADD_64")) && (decide (lvs.length = 6)) &&
         (decide (args.length = 2))
     | _ => false) = true := by decide

end CarryMaterializeSmoke

/-! ### Limb-width detection

The GPR register width (`reg u64` vs `reg u32`) is not stored on the name-only
parameter / local lists — it is carried in the body's `InstrR`/`Op`.
`bodyLimbWidth` scans the body for the *first* memory-access (`Pload`/`Lmem`)
width and returns it, defaulting to `U64` when there is no load/store. We key
off memory accesses (not arithmetic-op widths) because the loop counter is
compared/decremented at the *pointer* width, which is not the limb width in a
mixed-width kernel. The 64-bit kernels detect `U64` (so their declarations are
byte-identical); the 32-bit `mpn_add_n` re-emission detects `U32`. -/

/-- The first **memory-access** width found in an expression (a `Pload`),
    searching left-to-right. The limb width is the width of the data the
    kernel loads/stores, which is unambiguous — unlike op widths (the loop
    counter is compared at the *pointer* width, not the limb width), so we key
    `bodyLimbWidth` off memory accesses rather than arithmetic ops. -/
partial def exprMemWidth : PExpr → Option WSize
  | .Pload ws _ _ => some ws
  | .Papp1 _ e => exprMemWidth e
  | .Papp2 _ a b => (exprMemWidth a).orElse (fun _ => exprMemWidth b)
  | .Pif _ c t f => (exprMemWidth c).orElse (fun _ => (exprMemWidth t).orElse (fun _ => exprMemWidth f))
  | _ => none

/-- The memory-access width of an l-value (a `Lmem` store). -/
def lvalMemWidth : LVal → Option WSize
  | .Lmem ws _ _ => some ws
  | _ => none

/-- The first memory-access width in one instruction, recursing into control
    flow. -/
partial def instrMemWidth : InstrR → Option WSize
  | .Cassgn lv _ _ e => (lvalMemWidth lv).orElse (fun _ => exprMemWidth e)
  | .Copn lvs _ _ es =>
      (lvs.findSome? lvalMemWidth).orElse (fun _ => es.findSome? exprMemWidth)
  | .Cif c th el =>
      (exprMemWidth c).orElse (fun _ =>
        (th.findSome? instrMemWidth).orElse (fun _ => el.findSome? instrMemWidth))
  | .Cfor _ _ body => body.findSome? instrMemWidth
  | .Cwhile cb cond ca =>
      (cb.findSome? instrMemWidth).orElse (fun _ =>
        (exprMemWidth cond).orElse (fun _ => ca.findSome? instrMemWidth))
  | .Ccall _ _ _ args => args.findSome? exprMemWidth

/-- The kernel's GPR limb width: the first **memory-access** width in the body,
    defaulting to `U64`. Drives the `(NNu)` cast width of the open-carry
    materialization (the threaded carry register inherits the limb width). A
    pure-register kernel with no loads/stores keeps the `U64` default, so the
    existing 64-bit emission is unchanged. -/
def bodyLimbWidth (body : List InstrR) : WSize :=
  (body.findSome? instrMemWidth).getD .U64

/-! ### Per-variable declared widths

The 32-bit re-emission is *mixed width*: the address/count parameters stay
`reg u64` while the limb data registers become `reg u32`. So the locals
declaration cannot use one global width — each declared register carries its
own width in the AST (the `.sword ws` of its defining `Cassgn`'s `ty` field,
or the `vtype` of its `Lvar` output). `declWidthOf` reads that width back for
one local name; unseen names (and anything not width-resolved) default to
`U64`, preserving the byte-identical 64-bit output. -/

/-- The word size declared for an `Lvar` (from its `vtype`). -/
def lvarSwordWidth : LVal → Option (String × WSize)
  | .Lvar x => match x.var.vtype with
      | .sword ws => some (x.var.vname, ws)
      | _ => none
  | _ => none

/-- Collect `(name, width)` for every register-typed `Lvar` written in the
    body, recursing into control flow. The `Cassgn` `ty` is preferred (it is
    the assignment's value type); the `Lvar`'s own `vtype` is the fallback. -/
partial def collectDeclWidths : List InstrR → List (String × WSize)
  | [] => []
  | .Cassgn (.Lvar x) _ ty _ :: rest =>
      let w := match ty with
        | .sword ws => (x.var.vname, ws)
        | _ => match x.var.vtype with
               | .sword ws => (x.var.vname, ws)
               | _ => (x.var.vname, .U64)
      w :: collectDeclWidths rest
  | .Copn lvs _ _ _ :: rest =>
      (lvs.filterMap lvarSwordWidth) ++ collectDeclWidths rest
  | .Ccall _ lvs _ _ :: rest =>
      (lvs.filterMap lvarSwordWidth) ++ collectDeclWidths rest
  | .Cfor _ _ body :: rest => collectDeclWidths body ++ collectDeclWidths rest
  | .Cwhile cb _ ca :: rest =>
      collectDeclWidths cb ++ collectDeclWidths ca ++ collectDeclWidths rest
  | .Cif _ th el :: rest =>
      collectDeclWidths th ++ collectDeclWidths el ++ collectDeclWidths rest
  -- `Cassgn` into a memory/array l-value (a store) declares no register; skip.
  | _ :: rest => collectDeclWidths rest

/-- Look up a local's declared width from the collected map, defaulting to
    `U64`. -/
def declWidthOf (wmap : List (String × WSize)) (name : String) : WSize :=
  (wmap.find? (·.1 = name)).map (·.2) |>.getD .U64

/-! ### E1: stack-array local declarations

`RLetZero "x" (TBytes N)` in the LowCT front lowers to a Jasmin
`Cassgn (.Lvar { vname := "x", vtype := .sarr N }) _ (.sarr N) (.Parr_init N)`.

Before E1, every local — including the array-typed ones — was declared as
`reg u64 x;` because `lvarSwordWidth` returned `none` on `.sarr` types and
the width fallback defaulted to `U64`.  Jasmin's frontend rejected the
emitted code whenever the local needed to be passed to a kernel expecting
`stack u64[N]`.

E1 collects the array-typed locals separately and emits a `stack uNN[k] x;`
declaration line via the layout table `tbytesStackLayout` (N ↦ (U64, N/8)
when N ≡ 0 mod 8; (U8, N) otherwise).  See the layout doc in
`LowCTToJasmin.tbytesStackLayout`. -/

/-- Pick `(byte count, element width, cell count)` for a `Parr_init n` Lvar.
    Returns the layout pair from `LowCTToJasmin.tbytesStackLayout`. -/
def tbytesStackLayout (n : Nat) : WSize × Nat :=
  if n % 8 == 0 then (.U64, n / 8) else (.U8, n)

/-! ### #253: Keccak-f1600 u64-ptr-array layout case

The #251 leaf-ABI pass renders an `.sarr n` buffer as `reg ptr u32[n/4]`
(the ML-DSA u32-packed poly layout, 4 bytes / coefficient).  The SHAKE sponge
that drives the ML-DSA seed schedule (ExpandA's SHAKE128, ExpandMask's
SHAKE256, the H(tr‖M) / c̃ digests) calls the real `keccak_f1600` permutation,
whose ABI is `reg ptr u64[25]` for the 1600-bit state and `reg ptr u64[113]`
for the absorb buffer — *u64-packed*, not u32.  A byte count alone (`SType.sarr
n` carries no element width) cannot tell a 200-byte Keccak state apart from a
50-coefficient u32 poly buffer, so the layout decision keys on the two
Keccak-f1600 ABI array sizes, which are the only u64-packed `reg ptr` arrays in
the ML-DSA composition: the 25-lane state (200 bytes) and the 113-lane absorb
buffer (904 bytes).  This is the single additive u64-layout case the #251
residual flagged.

A `.sarr n` whose byte count is a Keccak-f1600 array size renders
`reg ptr u64[n/8]` (param/result) and `stack u64[n/8]` (call-site slot);
every other size keeps the existing u32/u8 poly-buffer behaviour
byte-identically. -/

/-- The Keccak-f1600 ptr-array ABI byte counts: the 25-lane state (200 B) and
    the 113-lane absorb buffer (904 B).  An `.sarr n` of one of these sizes is
    a u64-packed Keccak buffer (`reg ptr u64[n/8]`), not a u32 poly buffer. -/
def keccakU64ArrayBytes (n : Nat) : Bool :=
  n == 200 || n == 904

/-- Extract `(name, n)` from an `Lvar` whose `vtype = .sarr n`.  Used by
    `collectArrayLocals` to recover array-typed slot info from `Ccall`
    and `Copn` LHS, where the `Parr_init` initializer may have been
    dropped by DCE because the slot is overwritten by the call before
    being read. -/
def lvarSarrSize : LVal → Option (String × Nat)
  | .Lvar x => match x.var.vtype with
      | .sarr n => some (x.var.vname, n)
      | _ => none
  | _ => none

/-- `(name, n)` for a `Pvar` whose `vtype = .sarr n` — a poly buffer passed by
    reference as a `Ccall` argument to a `reg ptr u32[N]` leaf (`#251`
    composition).  Such a buffer needs a `stack` slot declaration even when it
    is *only* an argument (never an lval), e.g. the `mldsa_ntt_4way(wbuf, nbuf)`
    input `nbuf`.  Additive: the `#244`/`#247` leaves pass only scalar `Pvar`s,
    so this never fires for them. -/
def pvarSarrSize : PExpr → Option (String × Nat)
  | .Pvar gv => match gv.gv.var.vtype with
      | .sarr n => some (gv.gv.var.vname, n)
      | _ => none
  | _ => none

/-- Collect `(name, n)` for every Lvar with array semantics written in
    the body.  Picks up:

    * `Cassgn (.Lvar x) _ _ (.Parr_init n)` — the lowering shape from
      `RLetZero loc (TBytes N)` in `LowCTToJasmin.toJasminCmd`.
    * Any `Cassgn` whose LHS `vtype = .sarr n`.
    * `Ccall _ lvs _ _` LHS `Lvar`s whose `vtype = .sarr n` — kernel
      outputs written into stack-array slots.  Without this arm, DCE
      that drops a `Parr_init` initializer (whose written slot is
      later overwritten by a Ccall before being read) would also drop
      the stack-array signal, falling back to the wrong `reg u64`.
    * `Copn _ lvs _ _` LHS likewise.

    Recurses into control-flow bodies, mirroring `lhsNames` /
    `collectDeclWidths`.  Same `name` written twice keeps the first
    byte-count (dedup is applied by the caller). -/
partial def collectArrayLocals : List InstrR → List (String × Nat)
  | [] => []
  | .Cassgn (.Lvar x) _ _ (.Parr_init n) :: rest =>
      (x.var.vname, n) :: collectArrayLocals rest
  | .Cassgn (.Lvar x) _ _ _ :: rest =>
      let acc := match x.var.vtype with
        | .sarr n => [(x.var.vname, n)]
        | _ => []
      acc ++ collectArrayLocals rest
  -- #258: a dynamic-index array store `arr[i] = …` (`.Laset .AAscale`) whose
  -- `Parr_init` declaration was dropped by DCE (the slot is fully overwritten
  -- before any read).  The `.sarr n` type is preserved on the `Laset` var, so
  -- recover the slot size here; without this a stack-array output kernel emits
  -- references to an undeclared array.  Additive: ordinary kernels whose
  -- `Parr_init` survives DCE still match the arms above first.
  | .Cassgn (.Laset _ _ x _) _ _ _ :: rest =>
      let acc := match x.var.vtype with
        | .sarr n => [(x.var.vname, n)]
        | _ => []
      acc ++ collectArrayLocals rest
  | .Copn lvs _ _ _ :: rest =>
      lvs.filterMap lvarSarrSize ++ collectArrayLocals rest
  | .Ccall _ lvs _ args :: rest =>
      lvs.filterMap lvarSarrSize ++ args.filterMap pvarSarrSize ++
      collectArrayLocals rest
  | .Cfor _ _ body :: rest =>
      collectArrayLocals body ++ collectArrayLocals rest
  | .Cwhile cb _ ca :: rest =>
      collectArrayLocals cb ++ collectArrayLocals ca ++ collectArrayLocals rest
  | .Cif _ th el :: rest =>
      collectArrayLocals th ++ collectArrayLocals el ++ collectArrayLocals rest
  | _ :: rest => collectArrayLocals rest

/-- **Phase RND (2026-05-30): u32-access detection.**  Collect the names of
    array slots that are read or written through a `.AAscale .U32` access
    (`Pget`/`Laset`/`Lasub`/`Psub`).  Such slots must be declared
    `stack u32[N/4]` rather than the default packed `stack u64[N/8]`, because
    jasminc requires the declared element width to match the access width.
    This is the signal the ML-DSA rounding / sampler leaves rely on: their
    poly buffers are `u32[256]` (1024 bytes), accessed coefficient-wise. -/
partial def u32AccessedArrays : List InstrR → List String
  | [] => []
  | instr :: rest =>
    let here : List String :=
      let rec exprU32 : PExpr → List String
        | .Pget .AAscale .U32 arr idx => arr.gv.var.vname :: exprU32 idx
        | .Pget _ _ _ idx => exprU32 idx
        | .Psub .AAscale .U32 _ arr idx => arr.gv.var.vname :: exprU32 idx
        | .Papp1 _ e => exprU32 e
        | .Papp2 _ a b => exprU32 a ++ exprU32 b
        | .Pif _ c t e => exprU32 c ++ exprU32 t ++ exprU32 e
        | .Pload _ _ off => exprU32 off
        | _ => []
      let lvU32 : LVal → List String
        | .Laset .AAscale .U32 x idx => x.var.vname :: exprU32 idx
        | .Lasub .AAscale .U32 _ x idx => x.var.vname :: exprU32 idx
        | _ => []
      -- E1 (2026-05-30): a poly buffer threaded through a `reg ptr u32[N]`
      -- leaf appears as a `Ccall` lval/arg as a bare `.sarr`-typed `Lvar`/
      -- `Pvar` (no in-orchestrator `.AAscale` index — the indexing happens
      -- inside the callee).  Such a buffer must still be declared
      -- `stack u32[N/4]` to match the callee's ptr-array param ABI, so a
      -- `.sarr`-typed `Ccall` operand counts as a u32 access.  This only fires
      -- for the dst-threaded composition orchestrator (`#251`); the `#244`/
      -- `#247` leaves index their buffers directly and never reach this arm,
      -- so their emit is unchanged.
      let lvSarrU32 : LVal → List String
        | .Lvar x => match x.var.vtype with | .sarr _ => [x.var.vname] | _ => []
        | _ => []
      let exprSarrU32 : PExpr → List String
        | .Pvar gv => match gv.gv.var.vtype with | .sarr _ => [gv.gv.var.vname] | _ => []
        | _ => []
      match instr with
      | .Cassgn lv _ _ e => lvU32 lv ++ exprU32 e
      | .Copn lvs _ _ es => lvs.flatMap lvU32 ++ es.flatMap exprU32
      | .Ccall _ lvs _ es =>
          lvs.flatMap lvU32 ++ es.flatMap exprU32 ++
          lvs.flatMap lvSarrU32 ++ es.flatMap exprSarrU32
      | .Cif c th el => exprU32 c ++ u32AccessedArrays th ++ u32AccessedArrays el
      | .Cfor _ _ body => u32AccessedArrays body
      | .Cwhile cb c ca => u32AccessedArrays cb ++ exprU32 c ++ u32AccessedArrays ca
    here ++ u32AccessedArrays rest

/-- **#262: u64-access detection.**  Collect the names of array slots that are
    read or written through a `.AAscale .U64` access (`Pget`/`Laset`).  Such a
    slot is a u64-packed array (`reg ptr u64[N/8]` param / `stack u64[N/8]`
    local), as opposed to the default u32-poly layout.  This is the access-based
    signal the safegcd 62-bit-radix divstep subroutines rely on: their limb
    vectors are `stack u64[5]` (`.sarr 40`), the matrix `stack u64[4]`
    (`.sarr 32`) and the scratch `stack u64[3]` (`.sarr 24`), all threaded
    between the divstep / update_de / update_fg / normalize subroutines as
    `reg ptr u64[N]` by-reference params.  A byte count alone is ambiguous
    (`.sarr 32` is a u64[4] matrix here but a u32[8] I/O buffer for `out`/`a`/`m`),
    so the layout decision keys on the actual access width recorded by
    `LowCTToJasmin.toJasminCmd`'s `arrElemWS` (`.U64` for a `TArr _ .TU64`
    slot). -/
partial def u64AccessedArrays : List InstrR → List String
  | [] => []
  | instr :: rest =>
    let here : List String :=
      let rec exprU64 : PExpr → List String
        | .Pget .AAscale .U64 arr idx => arr.gv.var.vname :: exprU64 idx
        | .Pget _ _ _ idx => exprU64 idx
        | .Psub .AAscale .U64 _ arr idx => arr.gv.var.vname :: exprU64 idx
        | .Papp1 _ e => exprU64 e
        | .Papp2 _ a b => exprU64 a ++ exprU64 b
        | .Pif _ c t e => exprU64 c ++ exprU64 t ++ exprU64 e
        | .Pload _ _ off => exprU64 off
        | _ => []
      let lvU64 : LVal → List String
        | .Laset .AAscale .U64 x idx => x.var.vname :: exprU64 idx
        | .Lasub .AAscale .U64 _ x idx => x.var.vname :: exprU64 idx
        | _ => []
      match instr with
      | .Cassgn lv _ _ e => lvU64 lv ++ exprU64 e
      | .Copn lvs _ _ es => lvs.flatMap lvU64 ++ es.flatMap exprU64
      | .Ccall _ lvs _ es => lvs.flatMap lvU64 ++ es.flatMap exprU64
      | .Cif c th el => exprU64 c ++ u64AccessedArrays th ++ u64AccessedArrays el
      | .Cfor _ _ body => u64AccessedArrays body
      | .Cwhile cb c ca => u64AccessedArrays cb ++ exprU64 c ++ u64AccessedArrays ca
    here ++ u64AccessedArrays rest

/-- Render one `stack uNN[k] name;` declaration.  When `u32Packed` is true,
    the slot is declared `stack u32[n/4]` (the ML-DSA poly-buffer layout);
    otherwise the default packed-u64 / byte-wise `tbytesStackLayout` applies. -/
def stackArrDeclW (u32Packed : Bool) (name : String) (n : Nat) : String :=
  -- #253: a Keccak-f1600 ABI array size declares a u64-packed `stack u64[n/8]`
  -- slot to match the `reg ptr u64[n/8]` callee param.  Takes precedence over
  -- the u32-poly case so the sponge state buffer is not mis-declared u32.
  let (w, k) := if keccakU64ArrayBytes n then (WSize.U64, n / 8)
                else if u32Packed && n % 4 == 0 then (WSize.U32, n / 4)
                else tbytesStackLayout n
  "  stack " ++ wsizeTok w ++ "[" ++ toString k ++ "] " ++ name ++ ";\n"

/-- Render one `stack uNN[k] name;` declaration. -/
def stackArrDecl (name : String) (n : Nat) : String :=
  let (w, k) := tbytesStackLayout n
  "  stack " ++ wsizeTok w ++ "[" ++ toString k ++ "] " ++ name ++ ";\n"

/-! ## Function emitter -/

/-- Internal: shared body-rendering core used by both `emitFunDecl` (export fn)
    and `emitFunDeclWithKind` (the subroutine / annotated emitter). Produces
    the optimised body string and the rendered prelude (parameter signature,
    local declarations, return signature, return statement) so the caller
    only has to plug in the `export fn` / `fn` prefix and any `#[...]`
    annotations. -/
def emitFunDeclCore (fd : FunDecl) (spillScalars : Bool := false) :
    Option (String × String × String × String) := do
  let liveOutIn := fd.results.map (·.var)
  let (optBody0, optLO) := optimize liveOutIn fd.body
  -- A flag-named variable that is actually used as a GPR (computed by
  -- arithmetic, read in an arithmetic/memory context, or a data/`Ccall`
  -- l-value) is NOT a flag — it is declared `reg u64` instead.
  let gprUsed := gprUsedNames optBody0
  let carryRegs := dedup (materializedCarryNames gprUsed optBody0)
  let limbWS := bodyLimbWidth optBody0
  let optBody := expandFlagCaptures limbWS gprUsed optBody0
  let body ← emitBody "  " optBody
  let declWidths := collectDeclWidths optBody
  -- E1/E2 (2026-05-30): a parameter or result typed `sarr n` (an array slot)
  -- is a *pointer-array* buffer passed by reference — the leaf-ABI shape the
  -- composed ML-DSA sign uses to thread poly buffers between leaves
  -- (`out = mldsa_ntt_4way(out, inp)`).  It renders `reg ptr u32[n/4]` (the
  -- ML-DSA u32-packed poly layout: 4 bytes / coefficient) when `n % 4 = 0`,
  -- else `reg ptr u8[n]`.  Scalar (`sword`) params keep the existing
  -- `reg uNN` form byte-identically, so the #244/#247/#248 leaves are
  -- unchanged.  This is the dst-threaded `Ccall` ABI's caller-side contract:
  -- the buffer slot is `stack u32[N]` at the call site (via `Parr_init` +
  -- `u32AccessedArrays`) and `reg ptr u32[N]` in the callee signature.
  -- #253: a Keccak-f1600 ABI array size (200 B state, 904 B absorb buffer)
  -- renders the u64-packed `reg ptr u64[n/8]` shape; every other `.sarr n`
  -- keeps the existing u32-poly / u8 layout byte-identically.
  -- #262: name-aware ptr-array element width.  A `.sarr`-typed param/result
  -- that is u64-accessed (the safegcd limb / matrix / scratch arrays threaded
  -- between the divstep subroutines) renders `reg ptr u64[n/8]`; the existing
  -- Keccak-size and u32-poly cases are unchanged.  `u64Names` is the set of
  -- array names this function accesses with a `.U64`-scaled `Pget`/`Laset`,
  -- plus the `.sarr`-typed (byte%8==0) Ccall operands that are NOT u32-accessed
  -- (a u64 array threaded through a `Ccall` appears as a bare `.sarr` operand
  -- with no in-orchestrator scaled access).
  -- Names accessed through an `.AAscale .U32`-scaled `Pget`/`Laset`
  -- (the real u32-poly buffers).  A u64 array threaded through a `Ccall` is
  -- never *also* u32-scaled, so this set disambiguates the bare-`.sarr` Ccall
  -- operand: if a `.sarr` (byte%8==0) operand is NOT in this set, it is the
  -- u64-packed limb/matrix array (the #262 case), not a u32 poly buffer.
  let u32Scaled : List String :=
    let rec exprS : PExpr → List String
      | .Pget .AAscale .U32 arr idx => arr.gv.var.vname :: exprS idx
      | .Pget _ _ _ idx => exprS idx
      | .Psub .AAscale .U32 _ arr idx => arr.gv.var.vname :: exprS idx
      | .Papp1 _ e => exprS e
      | .Papp2 _ a b => exprS a ++ exprS b
      | .Pif _ c t e => exprS c ++ exprS t ++ exprS e
      | .Pload _ _ off => exprS off
      | _ => []
    let lvS : LVal → List String
      | .Laset .AAscale .U32 x idx => x.var.vname :: exprS idx
      | .Lasub .AAscale .U32 _ x idx => x.var.vname :: exprS idx
      | _ => []
    let rec goS : List InstrR → List String
      | [] => []
      | .Cassgn lv _ _ e :: rest => lvS lv ++ exprS e ++ goS rest
      | .Copn lvs _ _ es :: rest => lvs.flatMap lvS ++ es.flatMap exprS ++ goS rest
      | .Ccall _ lvs _ es :: rest => lvs.flatMap lvS ++ es.flatMap exprS ++ goS rest
      | .Cfor _ _ b :: rest => goS b ++ goS rest
      | .Cwhile cb _ ca :: rest => goS cb ++ goS ca ++ goS rest
      | .Cif _ th el :: rest => goS th ++ goS el ++ goS rest
    dedup (goS optBody)
  let ccallSarrU64 : List String :=
    let rec goC : List InstrR → List String
      | [] => []
      | .Ccall _ lvs _ es :: rest =>
          let lvN : LVal → List String
            | .Lvar x => match x.var.vtype with
                         | .sarr n => if n % 8 == 0 then [x.var.vname] else []
                         | _ => []
            | _ => []
          let esN : PExpr → List String
            | .Pvar gv => match gv.gv.var.vtype with
                          | .sarr n => if n % 8 == 0 then [gv.gv.var.vname] else []
                          | _ => []
            | _ => []
          lvs.flatMap lvN ++ es.flatMap esN ++ goC rest
      | .Cfor _ _ b :: rest => goC b ++ goC rest
      | .Cwhile cb _ ca :: rest => goC cb ++ goC ca ++ goC rest
      | .Cif _ th el :: rest => goC th ++ goC el ++ goC rest
      | _ :: rest => goC rest
    (goC optBody).filter (fun n => !u32Scaled.contains n)
  let u64Names := dedup (u64AccessedArrays optBody ++ ccallSarrU64)
  let ptrArrayTok : String → Nat → String := fun nm n =>
    if u64Names.contains nm ∧ n % 8 == 0 then "reg ptr u64[" ++ toString (n / 8) ++ "]"
    else if keccakU64ArrayBytes n then "reg ptr u64[" ++ toString (n / 8) ++ "]"
    else if n % 4 == 0 then "reg ptr u32[" ++ toString (n / 4) ++ "]"
    else "reg ptr u8[" ++ toString n ++ "]"
  let paramStr := String.intercalate ", "
    (fd.params.map (fun p =>
      match p.var.var.vtype with
      | .sword ws => "reg " ++ wsizeTok ws ++ " " ++ p.var.var.vname
      | .sarr n   => ptrArrayTok p.var.var.vname n ++ " " ++ p.var.var.vname
      | _         => "reg u64 " ++ p.var.var.vname))
  let retTypes := String.intercalate ", "
    (optLO.map (fun v => match v.vtype with
      | .sword ws => "reg " ++ wsizeTok ws
      | .sarr n   => ptrArrayTok v.vname n
      | _ => "reg u64"))
  let retNames := String.intercalate ", " (optLO.map (·.vname))
  let paramNames := fd.params.map (·.var.var.vname)
  let needsFlags := hasFlagCopn optBody
  let flagBank : List String := if needsFlags then ["of", "cf", "sf", "pf", "zf"] else []
  let flagNames : List String := flagBank.filter (fun n => !gprUsed.contains n)
  let carryFlagTmps := carryRegs.map carryFlagTmp
  let carryByteTmps := carryRegs.map carryByteTmp
  let loopIdxNames := dedup (collectLoopIdxNames optBody)
  let tmpNames := carryFlagTmps ++ carryByteTmps
  -- E1: array-typed locals (`stack uNN[k]`) are partitioned out of the
  -- regular `reg uNN` declaration list.  An array name comes from a
  -- `Cassgn (.Lvar x) _ _ (.Parr_init n)` — the lowering shape produced
  -- by `LowCTToJasmin.toJasminCmd`'s `RLetZero loc (TBytes N)` arm.
  let arrayLocalsAll := collectArrayLocals optBody
  let arrayNames : List String :=
    dedup (arrayLocalsAll.map (·.1)) |>.filter
      (fun n => !paramNames.contains n && !flagNames.contains n
                && !loopIdxNames.contains n && !tmpNames.contains n)
  let locals := dedup (lhsNames optBody) |>.filter
                  (fun n => !paramNames.contains n && !flagNames.contains n
                            && !loopIdxNames.contains n && !tmpNames.contains n
                            && !arrayNames.contains n)
  let widthOrder : List WSize := [.U256, .U128, .U64, .U32, .U16, .U8]
  -- `spillScalars`: declare scalar locals as `stack uNN` rather than
  -- `reg uNN`.  Needed for large straight-through kernels (e.g. the MAYO
  -- GF(16) Gaussian-elimination solve) whose live-scalar count exceeds the
  -- ~13 usable GPRs — jasminc's register allocator cannot fit them all in
  -- registers, so they must be stack-spilled.  jasminc still keeps the
  -- hot ones in registers across a statement; the `stack uNN x;` form just
  -- gives every scalar a home slot.  Loop counters stay as scalar stack
  -- vars too (jasminc lowers `while (n != 0)` over a stack `n` fine).
  -- Result variables must stay `reg` even when spilling (jasminc requires
  -- a `reg`/`reg ptr` result for a non-inlined function), so partition the
  -- locals: result names → `reg`, the rest → `stack` (under `spillScalars`).
  let resultNames := optLO.map (·.vname)
  let mkGroups (cls : String) (ns : List String) : String :=
    String.intercalate "" <| widthOrder.filterMap (fun w =>
      let names := ns.filter (fun n => declWidthOf declWidths n == w)
      if names.isEmpty then none
      else some ("  " ++ cls ++ wsizeTok w ++ " " ++ String.intercalate " " names ++ ";\n"))
  let localDecl :=
    if locals.isEmpty then ""
    else if spillScalars then
      let forced := dedup (regForcedNames optBody)
      let keepReg := fun n => resultNames.contains n || forced.contains n
      let regKeep := locals.filter keepReg
      let stackSpill := locals.filter (fun n => !keepReg n)
      mkGroups "reg " regKeep ++ mkGroups "stack " stackSpill
    else
      mkGroups "reg " locals
  -- E1: render each array local as `stack uNN[k] name;` using the layout
  -- table.  Look up the byte count by name from `arrayLocalsAll` (first
  -- occurrence wins for repeated names).
  -- #262: a name that is u64-accessed (or threaded as a u64 ptr-array Ccall
  -- operand) is declared `stack u64[n/8]`, even though its bare `.sarr` Ccall
  -- operand also matched the u32 heuristic.  u64 detection wins.
  let u32Arrays := dedup (u32AccessedArrays optBody) |>.filter
                     (fun n => !u64Names.contains n)
  let arrayDecl :=
    String.intercalate "" <| arrayNames.map (fun name =>
      let n := (arrayLocalsAll.find? (·.1 = name)).map (·.2) |>.getD 0
      stackArrDeclW (u32Arrays.contains name) name n)
  let loopIdxDecl :=
    if loopIdxNames.isEmpty then ""
    else "  inline int " ++ String.intercalate " " loopIdxNames ++ ";\n"
  let boolNames := flagNames ++ carryFlagTmps
  let flagDecl :=
    if boolNames.isEmpty then ""
    else "  reg bool " ++ String.intercalate " " boolNames ++ ";\n"
  let byteDecl :=
    if carryByteTmps.isEmpty then ""
    else "  reg u8 " ++ String.intercalate " " carryByteTmps ++ ";\n"
  let sigArrow := if optLO.isEmpty then "" else " -> " ++ retTypes
  let retStmt  := if optLO.isEmpty then "" else "\n\n  return " ++ retNames ++ ";"
  let header := "(" ++ paramStr ++ ")" ++ sigArrow
  let decls  := flagDecl ++ byteDecl ++ localDecl ++ arrayDecl ++ loopIdxDecl
  let bodyBlock := "{\n" ++ decls ++ "\n" ++ body ++ retStmt ++ "\n}\n"
  some (header, decls, bodyBlock, body)

/-- Subroutine-function kinds at the Jasmin source level. `Export` is the
    default (callable from C); `Subroutine` is a non-`export`, non-`inline`
    `fn` that jasminc does NOT inline. `#[returnaddress=stack]` is the
    annotation we attach to `Subroutine` declarations whose callee receives
    its return address on the stack (mandatory for non-inlined, callable
    subroutines on x86-64 — jasmin compiler/src/functionAnnotations.ml). -/
inductive FnKind where
  /-- `export fn …` — externally callable, default. -/
  | Export : FnKind
  /-- `#[returnaddress=stack] fn …` — non-inlined subroutine (the form needed
      by `Ccall`-target wrappers in the mul_basecase Cwhile cascade). -/
  | SubroutineRastack : FnKind
  deriving Inhabited, DecidableEq

/-- Render the prefix (annotations + keyword) for a given `FnKind`. -/
def fnKindPrefix : FnKind → String
  | .Export => "export fn "
  | .SubroutineRastack => "#[returnaddress=stack]\nfn "

/-! ### E3 — require-line emit (2026-05-29)

Bench drivers that issue a `Ccall` to a kernel shipped in an
`include/` shim need a `require "..."` prologue at the top of the
`.jazz` so jasminc can resolve the symbol.  Before E3 the verified
emit produced a shape-correct body that the hand-edited bench
bridges then prefixed with a manual `require` line; E3 makes the
emit produce the line directly.

The mapping from kernel name to include path is a registered table
populated below for the five per-protocol bench bridges.  Kernels
NOT in the table emit no require line (callee is in scope by some
other means — e.g. a sibling `fn` in the same `.jazz`).  -/

/-- Look up the canonical `require "..."` path for a kernel name.

    Each per-protocol bench bridge (MAYO, UOV, HAWK, Falcon, ML-DSA)
    ships its leaf functions through a single `include/<x>_leaves.jinc`
    shim that the bench's hand-edited `.jazz` references via a
    top-of-file `require ".../<x>_leaves.jinc"`.  E3 lets the
    verified emit produce that prologue automatically so the bench
    drivers need no manual edit.  Returning `none` means
    the kernel is in scope by some other means (e.g. a sibling
    `fn` definition in the same `.jazz`); no require line is
    emitted in that case.  -/
def kernelRequireMap : String → Option String
  -- MAYO: `mayo_quadform_n8` lives in `mayo_leaves.jinc`.
  | "mayo_quadform_n8"             => some "../include/mayo_leaves.jinc"
  -- UOV: `uov_gf256_dot_l8` lives in `uov_leaves.jinc`.
  | "uov_gf256_dot_l8"             => some "../include/uov_leaves.jinc"
  -- HAWK: `hawk_mul_4way_packed_kernel` lives in `hawk_leaves.jinc`.
  | "hawk_mul_4way_packed_kernel"  => some "../include/hawk_leaves.jinc"
  -- Falcon (fndsa): `falcon_poly_sub_12289_512` lives in
  -- `falcon_leaves.jinc`.
  | "falcon_poly_sub_12289_512"    => some "../include/falcon_leaves.jinc"
  -- ML-DSA: `mldsa_ntt_4way` uses the sibling-emit path
  -- (`gen/mldsa_ntt_4way.jazz`), not a central include.
  | "mldsa_ntt_4way"               => some "../gen/mldsa_ntt_4way.jazz"
  -- #253: the ML-DSA seed-schedule sponge calls the real FIPS-202 `keccak_f1600`
  -- permutation, emitted at `bench/keccak_compare/gen/keccak_f1600.jazz`.
  | "keccak_f1600"                 => some "../../keccak_compare/gen/keccak_f1600.jazz"
  | _                              => none

/-- Collect every distinct kernel name referenced via `Ccall` in a
    body.  Recurses into `Cwhile` / `Cfor` / `Cif` bodies so calls
    inside loops or branches are picked up.  Order matches first
    occurrence in the body. -/
partial def collectCallNames : List InstrR → List String
  | [] => []
  | .Ccall _ _ fn _ :: rest => fn.name :: collectCallNames rest
  | .Cfor _ _ body :: rest =>
      collectCallNames body ++ collectCallNames rest
  | .Cwhile cbefore _ cafter :: rest =>
      collectCallNames cbefore ++ collectCallNames cafter ++
      collectCallNames rest
  | .Cif _ th el :: rest =>
      collectCallNames th ++ collectCallNames el ++ collectCallNames rest
  | _ :: rest => collectCallNames rest

/-- Render the `require "..."` prologue for a body: one line per
    distinct kernel name that has an entry in `kernelRequireMap`,
    in first-occurrence order.  Returns the empty string when no
    referenced kernel is in the map.  -/
def emitRequires (body : List InstrR) : String :=
  let names := dedup (collectCallNames body)
  let paths := names.filterMap kernelRequireMap
  if paths.isEmpty then ""
  else
    String.intercalate "\n" (paths.map (fun p => "require \"" ++ p ++ "\"")) ++ "\n\n"

/-- General-purpose emitter: render a `FunDecl` with the given function-kind
    prefix. `Export` matches the existing `emitFunDecl` byte-identically (so
    we use this as the new primitive). `SubroutineRastack` prepends the
    `#[returnaddress=stack]` annotation and emits `fn` instead of `export fn`,
    suitable as a `Ccall` target whose caller wants to force non-inlining
    (e.g., the mul_basecase Cwhile cascade's inner blocked-addmul kernel).

    **E3 (2026-05-29)**: prepends `require "..."` lines for every
    `Ccall` target name registered in `kernelRequireMap`.  This makes
    the verified emit's `.jazz` directly jasminc-compilable for the
    five per-protocol bench bridges that previously hand-edited the
    prologue. -/
def emitFunDeclWithKind (kind : FnKind) (fd : FunDecl)
    (spillScalars : Bool := false) : Option String := do
  let (header, _decls, bodyBlock, _body) ← emitFunDeclCore fd spillScalars
  let requires := emitRequires fd.body
  some <|
    "// Auto-generated from CatCrypt Jasmin AST. Do not edit by hand.\n" ++
    requires ++
    fnKindPrefix kind ++ fd.name.name ++ header ++ "\n" ++ bodyBlock

/-- Render a full Jasmin `export fn` declaration. Handles any number of
    `reg u64` return values (comma-separated return signature and
    `return` statement). Returns `none` if an instruction shape is
    unsupported by the emitter.

    Runs `optimize` (peephole + constprop + DCE + copy-coalesce) first.
    Return variable names are drawn from the *renamed* `liveOut` so that
    a coalesce that merged a result variable into one of its producers
    is reflected in the emitted `return` statement.

    Flag-register declarations are added automatically when the body
    contains a `Copn` whose lval list has `Lnone` entries (e.g.,
    from flag-producing intrinsics like `#ADD_64` / `#ADC_64`).

    For non-export `fn` (`#[returnaddress=stack]`) emit, see
    `emitFunDeclWithKind` with `FnKind.SubroutineRastack`. -/
def emitFunDecl (fd : FunDecl) : Option String :=
  emitFunDeclWithKind .Export fd

/-- Emit an `export fn` whose scalar locals are declared `stack uNN` rather
    than `reg uNN`.  Use for large kernels whose live-scalar count exceeds
    the GPR budget (the MAYO GF(16) solve, ML-DSA full samplers, …). -/
def emitFunDeclSpill (fd : FunDecl) : Option String :=
  emitFunDeclWithKind .Export fd (spillScalars := true)

/-- Convenience wrapper: emit `fd` as a `#[returnaddress=stack] fn` (a
    non-export, non-inline subroutine). Used by the mul_basecase Cwhile
    cascade to force jasminc to NOT inline the inner blocked-addmul
    callee — the inline expansion is what blows the GPR-allocator budget. -/
def emitFunDeclRastack (fd : FunDecl) : Option String :=
  emitFunDeclWithKind .SubroutineRastack fd

/-- Emit a `#[returnaddress=stack] fn` whose scalar locals are stack-spilled
    (`stack uNN` instead of `reg uNN`).  This is the subroutine analogue of
    `emitFunDeclSpill`: a non-inlined helper whose own live-scalar set still
    exceeds the GPR budget.  Used by the #262 safegcd-divstep62 split, where
    each lifted phase subroutine (`update_de` / `update_fg`) carries the i128
    accumulators plus the `#IMUL` RAX/RDX reserve. -/
def emitFunDeclRastackSpill (fd : FunDecl) : Option String :=
  emitFunDeclWithKind .SubroutineRastack fd (spillScalars := true)

/-- Emit without running the optimization passes. Useful for benchmarking the
    raw output against the optimized output. -/
def emitFunDeclRaw (fd : FunDecl) : Option String := do
  let body ← emitBody "  " fd.body
  let paramStr := String.intercalate ", "
    (fd.params.map (fun p => "reg u64 " ++ p.var.var.vname))
  let paramNames := fd.params.map (·.var.var.vname)
  let locals := dedup (lhsNames fd.body) |>.filter
                  (fun n => !paramNames.contains n)
  let localDecl :=
    if locals.isEmpty then ""
    else "  reg u64 " ++ String.intercalate " " locals ++ ";\n\n"
  let retName := (fd.results.head?).map (·.var.vname) |>.getD "r"
  some <|
    "// Auto-generated (raw, no optimization) from CatCrypt Jasmin AST.\n" ++
    "export fn " ++ fd.name.name ++ "(" ++ paramStr ++ ") -> reg u64\n" ++
    "{\n" ++ localDecl ++ body ++ "\n\n  return " ++ retName ++ ";\n}\n"

/-! ## IO -/

/-- Write the Jasmin source to `filename`; throw if any instruction is
    not in the supported SSA shape. -/
def writeJazz (filename : String) (fd : FunDecl) : IO Unit := do
  match emitFunDecl fd with
  | some s => IO.FS.writeFile filename s
  | none => throw <| .userError s!"emitFunDecl failed for {fd.name.name}"

end CatCrypt.Crypto.Jasmin.Emit
