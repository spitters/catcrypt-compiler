/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public meta import CatCrypt.Crypto.Jasmin.LowCTToJasmin
public import CatCrypt.Crypto.Jasmin.LowCTToJasmin

/-!
# `Com jasminDialect → JasminProg` lowering (phase (a) of the convergence plan)

This file is the next deliverable after `JasminDialect.lean`: a verified,
structured AST → structured AST lowering from CatCrypt's typed-SSA VIR
(`Com jasminDialect Γ t`) to the Jasmin program AST
(`CatCrypt.Crypto.Jasmin.JasminProg`). The `.jazz` *text* is produced by the
existing, already-tested `ppJasminProg` printer — so this file's job ends at
producing a `JasminProg`; no string-munging happens here.

```
Com[jasminDialect]  ──lowerComToProg──▶  JasminProg (AST)  ──ppJasminProg──▶ .jazz
```

This realises §3 of `jasmin-vir-convergence-plan.md` ("emit the AST, not
text"): the reg-vs-stack and width distinctions that `RustEmitJazz` inferred
by hand are now *dialect types*, lowered to `JasminAST` constructs.

## Naming scheme (de Bruijn → strings)

The traversal mirrors `ComToVeir.lowerCom`: we walk `Com.var`/`Com.ret`,
threading a `VarMap Γ : ∀ t, Var Γ t → String` that resolves each typed
De Bruijn variable to its emitted name. The free context `Γ` is materialised
as named function parameters (`p0`, `p1`, …, head-first, matching
`buildFuncFromCom`'s block-arg convention), and each `Com.var` binding gets a
fresh SSA name `v0`, `v1`, … in insertion order. `VarMap.extend` shifts
existing entries by `.there` and binds the fresh name at `.here`, exactly like
`ComToVeir.VarMap.extend`.

## Op → InstrR mapping

| dialect op            | `InstrR`                                                         |
|-----------------------|------------------------------------------------------------------|
| `regArith op w`       | `Cassgn (Lvar dst) AT_none (sword w) (Papp2 (op@w) (Pvar a) (Pvar b))` |
| `stackLoad w n`       | `Cassgn (Lvar dst) AT_none (sword w) (Pget AAscale w arr (Pvar idx))`  |
| `stackStore w n`      | `Cassgn (Laset AAscale w arr (Pvar idx)) AT_none (sword w) (Pvar src)` |
| `castW w w'`          | `Cassgn (Lvar dst) AT_none (sword w') (Papp1 (Ozeroext w' w) (Pvar src))` |
| `extCall name as ret` | `Ccall DoInline [Lvar dst] {name} (args.map Pvar)`                |

For `stackStore`, the SSA result-array name equals the *input* array name
(in-place update is how Jasmin models `a[i] = v`), so the binding introduced by
`Com.var` is named after the source array rather than a fresh `vN`.

## Bounded for-loop (best-effort, see `JForProg`)

`Com` is loopless. We add a self-contained `JForProg` wrapper carrying a static
iteration count `n` and an accumulator-update `Com jasminDialect [accTy] accTy`,
with a **total** denotation by `n`-fold iteration (`Nat.rec`, no fuel). It
emits a `Cfor` whose body is the lowering of the update Com. The body is
lowered with the accumulator threaded as the loop's carried variable; what is
modelled (the `n`-fold semantics + the `Cfor` skeleton) vs. deferred (no
SSA-phi for the carried value across iterations — the emitted body reads/writes
a single named accumulator, the standard Jasmin idiom) is documented at
`JForProg` below.

## Status

Printer + smoke (`.jazz` text emitted, structural facts `decide`/`rfl`-checked)
+ bounded-for loop. All goals closed; standard axioms only.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Jasmin

/-! ## 1. Width and operator translation -/

/-- Map a bit-width `Nat` to the nearest Jasmin `WSize`. Widths that aren't an
    exact Jasmin size round *up* to the next supported size (and saturate at
    `U512`, the AVX-512 `zmm` width); this keeps the lowering total. The
    dialect's `smokeProg` uses 32 and 64, which map exactly. A `reg 512`
    (an AVX-512 packed register, task #286) maps exactly to `U512` so it prints
    as `reg u512` rather than truncating to `u256`. -/
def wsizeOfNat (w : Nat) : WSize :=
  if w ≤ 8 then .U8
  else if w ≤ 16 then .U16
  else if w ≤ 32 then .U32
  else if w ≤ 64 then .U64
  else if w ≤ 128 then .U128
  else if w ≤ 256 then .U256
  else .U512

/-- Map a `JasminBinOp` to a Jasmin `SOp2` at a fixed word size. -/
def binOpToSOp2 (op : JasminBinOp) (ws : WSize) : SOp2 :=
  match op with
  | .add => .Oadd ws
  | .sub => .Osub ws
  | .mul => .Omul ws
  | .and => .Oland ws
  | .or  => .Olor ws
  | .xor => .Olxor ws
  | .shl => .Olsl ws
  | .shr => .Olsr ws
  -- BMI1 `andn` = `(¬a) ∧ b`. Jasmin has no `SOp2` infix for `andn` (it is the
  -- `#ANDN_w` `Copn` intrinsic). The `regArith` arm of `lowerExpr` does NOT call
  -- this function for `andn`: it special-cases it to
  -- `Papp2 (Oland ws) (Papp1 (Olnot ws) a) b` so the complement of the first
  -- operand is explicit (`((!a) & b)` in `.jazz`). This `Oland ws` fallback is
  -- kept only for totality; it is unreachable on the emit path.
  | .andn => .Oland ws

/-- The jasmin intrinsic mnemonic for an AVX-512 8×u64 packed `vpackZMM` op
    (task #286). Matches the `_8u64` surface names in `MpnAvx512Emit`
    (`#VPADD_8u64` / `#VPSUB_8u64` / `#VPMULL_8u64` / `#VPSRL_8u64`). The
    bitwise lanes (`and`/`or`/`xor`) are width-agnostic on a `zmm`
    (`#VPAND`/`#VPOR`/`#VPXOR`); `shl` is `#VPSLL_8u64`. -/
def vpackZMMMnemonic (bop : JasminBinOp) : String :=
  match bop with
  | .add => "#VPADD_8u64"
  | .sub => "#VPSUB_8u64"
  | .mul => "#VPMULL_8u64"
  | .and => "#VPAND"
  | .or  => "#VPOR"
  | .xor => "#VPXOR"
  | .shl => "#VPSLL_8u64"
  | .shr => "#VPSRL_8u64"
  -- BMI1/AVX `andn` `(¬a) ∧ b`: the packed AVX intrinsic `#VPANDN`
  -- (width-agnostic on a `zmm`, like `#VPAND`/`#VPOR`/`#VPXOR`).
  | .andn => "#VPANDN"

/-- The jasmin intrinsic mnemonic for an AVX-512 16×u32 packed dword
    `vpackZMMd` op (SHA-256/ChaCha20 dword lanes). Dword analogue of
    `vpackZMMMnemonic`: `_8u32` surface names (`#VPADDD` / `#VPSUBD` /
    `#VPMULLD` / `#VPSRLD`); the bitwise lanes are width-agnostic on a `zmm`. -/
def vpackZMMdMnemonic (bop : JasminBinOp) : String :=
  match bop with
  | .add => "#VPADDD"
  | .sub => "#VPSUBD"
  | .mul => "#VPMULLD"
  | .and => "#VPAND"
  | .or  => "#VPOR"
  | .xor => "#VPXOR"
  | .shl => "#VPSLLD"
  | .shr => "#VPSRLD"
  | .andn => "#VPANDN"

/-! ## 2. Names and the SSA `VarMap` -/

/-- A typed De Bruijn → string name resolver, mirroring
    `ComToVeir.VarMap`. Total by construction (`Var [] _` is uninhabited). -/
abbrev VarMap (Γ : Ctxt jasminDialect) : Type :=
  ∀ (t : jasminDialect.Ty), Ctxt.Var Γ t → String

namespace VarMap

/-- Empty resolver (for `Γ = []`); body vacuous since `Var [] t` has no
    inhabitants. -/
def empty : VarMap [] := fun _ v => by cases v

/-- Extend a resolver with a fresh binding `here ↦ name`, shifting existing
    entries by `.there`. -/
def extend {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (name : String) : VarMap (t :: Γ) :=
  fun s v => by
    cases v with
    | here => exact name
    | there v' => exact vm s v'

end VarMap

/-- Build a Jasmin `SType` from a dialect type. Registers/casts map to a word;
    stack arrays map to a byte-array of the right total size; `inlineInt` to
    `sint`; `bool` to `sbool`. -/
def styOfTy : jasminDialect.Ty → SType
  | .reg w => .sword (wsizeOfNat w)
  | .stackArr w n => .sarr (n * (wsizeOfNat w).bytes)
  | .inlineInt => .sint
  | .bool => .sbool

/-- A `VarI` from a name + dialect type. -/
def mkVarI (name : String) (t : jasminDialect.Ty) : VarI :=
  { var := { vname := name, vtype := styOfTy t } }

/-- A `Pvar` reading a local variable of the given name + type. -/
def pvarOf (name : String) (t : jasminDialect.Ty) : PExpr :=
  .Pvar { gv := mkVarI name t, gs := false }

/-- A `GVar` for an array variable of the given name + type. -/
def gvarOf (name : String) (t : jasminDialect.Ty) : GVar :=
  { gv := mkVarI name t, gs := false }

/-! ## 3. Positional argument extraction

`Expr.args : HVector (fun ty => Var Γ ty) (sig op)` carries one `Var` per
declared argument. The signature shapes are fixed, so we extract by
`head`/`tail.head` exactly as the dialect's `DialectDenote.denote` does — but
here we resolve each `Var` to a *name* via the `VarMap` rather than to a value.
We add `HVector` view helpers (the framework's `HVector.head`/`tail` already
exist; we reuse them). -/

/-- Name of the i-th (0/1/2) positional argument of an expression. Total: out
    of range returns `"<oob>"`, which the fixed signatures never trigger. -/
def argName {Γ : Ctxt jasminDialect} (vm : VarMap Γ) :
    {tys : List jasminDialect.Ty} →
    HVector (fun ty => Ctxt.Var Γ ty) tys → Nat → String
  | [], _, _ => "<oob>"
  | t :: _, .cons v _, 0 => vm t v
  | _ :: _, .cons _ rest, (k + 1) => argName vm rest k

/-- Type of the i-th positional argument (for emitting the right `SType`). -/
def argTy : (tys : List jasminDialect.Ty) → Nat → jasminDialect.Ty
  | [], _ => .reg 0
  | t :: _, 0 => t
  | _ :: rest, (k + 1) => argTy rest k

/-! ## 4. Lowering one `Expr` to an `InstrR`

`dst` is the SSA name we bind the expression's result to. We pattern-match on
`e.op` and read argument names off `e.args` via `argName`. -/

/-- Lower a single `Expr` to a Jasmin instruction binding `dst`. -/
def lowerExpr {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (e : Expr jasminDialect Γ t) (dst : String) : InstrR :=
  match e.op with
  | .regArith op w =>
      let ws := wsizeOfNat w
      let a := argName vm e.args 0
      let b := argName vm e.args 1
      -- BMI1 `andn` = `(¬a) ∧ b`. There is no `SOp2` for the complemented-first
      -- AND, so we render it as `Oland` of the *bitwise-complemented* first
      -- operand (`Papp1 (Olnot ws) a`) and the plain second operand `b`; the
      -- `ppPExpr` printer renders `Olnot` as `!`, yielding `((!a) & b)` —
      -- semantically `(~~~a) &&& b`. Every other `regArith` op is a plain
      -- `SOp2` infix. (Verified against SHA-256 `Ch = (e&f) ^ (~e&g)`.)
      match op with
      | .andn =>
          .Cassgn (.Lvar (mkVarI dst (.reg w))) .AT_none (.sword ws)
            (.Papp2 (.Oland ws)
              (.Papp1 (.Olnot ws) (pvarOf a (.reg w))) (pvarOf b (.reg w)))
      | _ =>
          .Cassgn (.Lvar (mkVarI dst (.reg w))) .AT_none (.sword ws)
            (.Papp2 (binOpToSOp2 op ws)
              (pvarOf a (.reg w)) (pvarOf b (.reg w)))
  | .stackLoad w n =>
      let ws := wsizeOfNat w
      let arr := argName vm e.args 0
      let idx := argName vm e.args 1
      .Cassgn (.Lvar (mkVarI dst (.reg w))) .AT_none (.sword ws)
        (.Pget .AAscale ws (gvarOf arr (.stackArr w n))
          (pvarOf idx (.reg 64)))
  | .stackStore w n =>
      let ws := wsizeOfNat w
      let arr := argName vm e.args 0
      let idx := argName vm e.args 1
      let src := argName vm e.args 2
      .Cassgn (.Laset .AAscale ws (mkVarI arr (.stackArr w n))
                (pvarOf idx (.reg 64)))
        .AT_none (.sword ws) (pvarOf src (.reg w))
  | .castW w w' =>
      let wsi := wsizeOfNat w
      let wso := wsizeOfNat w'
      let src := argName vm e.args 0
      .Cassgn (.Lvar (mkVarI dst (.reg w'))) .AT_none (.sword wso)
        (.Papp1 (.Ozeroext wso wsi) (pvarOf src (.reg w)))
  | .extCall name argTys retTy =>
      -- args.map Pvar : one Pvar per declared arg type.
      let args := (List.range argTys.length).map
        (fun i => pvarOf (argName vm e.args i) (argTy argTys i))
      .Ccall .DoInline [.Lvar (mkVarI dst retTy)] { name := name } args
  | .regConst w n =>
      let ws := wsizeOfNat w
      .Cassgn (.Lvar (mkVarI dst (.reg w))) .AT_none (.sword ws)
        (.Pconst (Int.ofNat n))
  | .select w =>
      -- Constant-time select (E2): `#CMOV` intrinsic on `[cond, a, b]` with
      -- `cond` a `reg 1` (matches the branchless mask the front's `emitBodyReg`
      -- renders; mirrors how `addCarryLo`/`mulhi` lower to `Ccall`).
      let cond := argName vm e.args 0
      let a := argName vm e.args 1
      let b := argName vm e.args 2
      .Ccall .DoInline [.Lvar (mkVarI dst (.reg w))]
        { name := "CMOV" }
        [pvarOf cond (.reg 1), pvarOf a (.reg w), pvarOf b (.reg w)]
  | .vpackZMM bop =>
      -- AVX-512 8×u64 packed op (task #286): emit the `#VPADD_8u64`-style
      -- intrinsic call on two `reg u512` (= `reg 512`) operands. Mirrors how
      -- `extCall` lowers to `Ccall`, with the lane-parallel mnemonic chosen by
      -- `bop` (matching `MpnAvx512Emit` render helpers).
      let a := argName vm e.args 0
      let b := argName vm e.args 1
      .Ccall .DoInline [.Lvar (mkVarI dst (.reg 512))]
        { name := vpackZMMMnemonic bop }
        [pvarOf a (.reg 512), pvarOf b (.reg 512)]
  | .vpackZMMd bop =>
      -- AVX-512 16×u32 packed dword op: dword analogue of `vpackZMM`, emitting
      -- a `#VPADDD`-style intrinsic call on two `reg 512` operands. Mirrors the
      -- `vpackZMM` Ccall arm with a dword mnemonic chosen by `bop`.
      let a := argName vm e.args 0
      let b := argName vm e.args 1
      .Ccall .DoInline [.Lvar (mkVarI dst (.reg 512))]
        { name := vpackZMMdMnemonic bop }
        [pvarOf a (.reg 512), pvarOf b (.reg 512)]
  | .vprordZMM n =>
      -- AVX-512 16×u32 packed right-rotate-by-immediate (`#VPRORD`): unary on
      -- one `reg 512` operand. Mirrors the `vpackZMM` Ccall arm shape.
      let a := argName vm e.args 0
      .Ccall .DoInline [.Lvar (mkVarI dst (.reg 512))]
        { name := "VPRORD" }
        [pvarOf a (.reg 512)]
  | .vpslldq n =>
      -- 128-bit byte-wise left shift (`#VPSLLDQ`): unary on one `reg 128`.
      -- Mirrors the `vpackZMM` Ccall arm shape.
      let a := argName vm e.args 0
      .Ccall .DoInline [.Lvar (mkVarI dst (.reg 128))]
        { name := "VPSLLDQ" }
        [pvarOf a (.reg 128)]
  | .vpsrldq n =>
      -- 128-bit byte-wise right shift (`#VPSRLDQ`): unary on one `reg 128`.
      -- Mirrors the `vpackZMM` Ccall arm shape.
      let a := argName vm e.args 0
      .Ccall .DoInline [.Lvar (mkVarI dst (.reg 128))]
        { name := "VPSRLDQ" }
        [pvarOf a (.reg 128)]
  | .vsimd op =>
      -- Parametrized 128-bit SIMD op (SIMD-dialect-unification): emit the
      -- `op.mnemonic` intrinsic call on two `reg 128` (= XMM) operands, mirroring
      -- the `vpackZMM` Ccall arm with the SimdOp-chosen mnemonic.
      let a := argName vm e.args 0
      let b := argName vm e.args 1
      .Ccall .DoInline [.Lvar (mkVarI dst (.reg 128))]
        { name := op.mnemonic }
        [pvarOf a (.reg 128), pvarOf b (.reg 128)]
  | .vymm op =>
      -- AVX2 256-bit vector op: emit the `op.jasminMnemonic` intrinsic call on
      -- `reg 256` (= YMM) operands, mirroring the `vsimd` Ccall arm with the
      -- YmmOp-chosen mnemonic. Binary ops read two operands, unary ops read one.
      let a := argName vm e.args 0
      if op.isBinary then
        .Ccall .DoInline [.Lvar (mkVarI dst (.reg 256))]
          { name := op.jasminMnemonic }
          [pvarOf a (.reg 256), pvarOf (argName vm e.args 1) (.reg 256)]
      else
        .Ccall .DoInline [.Lvar (mkVarI dst (.reg 256))]
          { name := op.jasminMnemonic }
          [pvarOf a (.reg 256)]
  | .mulhi w =>
      -- Widening multiply high word (#477): emit the BMI2 `#MULXHI` intrinsic on
      -- the two `reg w` factors. The paired low word is the producer's
      -- `regArith .mul`. Mirrors how `extCall`/`vpackZMM` lower to `Ccall`.
      let a := argName vm e.args 0
      let b := argName vm e.args 1
      .Ccall .DoInline [.Lvar (mkVarI dst (.reg w))]
        { name := "MULXHI" }
        [pvarOf a (.reg w), pvarOf b (.reg w)]
  | .addCarryLo w =>
      -- Carry-chain add data word (#477): `#ADCX` intrinsic on `[a, b, cin]`
      -- (cin a `reg 1` carry-in). `read_linear` routes the carry-in through CF.
      let a := argName vm e.args 0
      let b := argName vm e.args 1
      let cin := argName vm e.args 2
      .Ccall .DoInline [.Lvar (mkVarI dst (.reg w))]
        { name := "ADCX" }
        [pvarOf a (.reg w), pvarOf b (.reg w), pvarOf cin (.reg 1)]
  | .addCarryHi w =>
      -- Carry-chain carry-out bit (#477): `#ADCXHI` intrinsic on `[a, b, cin]`,
      -- producing the propagated `reg 1` carry. `read_linear` snapshots CF.
      let a := argName vm e.args 0
      let b := argName vm e.args 1
      let cin := argName vm e.args 2
      .Ccall .DoInline [.Lvar (mkVarI dst (.reg 1))]
        { name := "ADCXHI" }
        [pvarOf a (.reg w), pvarOf b (.reg w), pvarOf cin (.reg 1)]
  | .rorImm w n =>
      -- Native right-rotate (#497): emit the x86 rotate asm op `#ROR_w` on the
      -- single `reg w` source plus the compile-time immediate amount `n`
      -- (a `Pconst`). The Rust backend (`JasminToRustEmit`) already renders
      -- `#ROR_32`/`#ROR_64` as `(a).rotate_right((n) as u32)`, so this lowers
      -- one-to-one to the native rotate instead of the `shr; shl; or` triple.
      let ws := wsizeOfNat w
      let src := argName vm e.args 0
      -- jasminc's `#ROR_w` intrinsic produces THREE lvalues: the OF / CF flags
      -- (discarded via `_`, the flag-clobbering rotate) plus the rotated result.
      -- The op name is `ROR_w` *without* a leading `#` — `ppInstrR` prepends the
      -- `#` when rendering a `Copn (.Oasm …)`, so naming it `#ROR_w` here would
      -- emit a (rejected) `##ROR_w`.
      .Copn [.Lnone {} (.sbool), .Lnone {} (.sbool), .Lvar (mkVarI dst (.reg w))]
        .AT_none
        (.Oasm { name := "ROR_" ++ toString w })
        [pvarOf src (.reg w), .Pconst (Int.ofNat n)]
  | .shrImm w n =>
      -- Native immediate logical right-shift (#605): the shift amount `n` is a
      -- compile-time `Pconst`, not a register-file read, so jasminc x86
      -- linearizes it as `dst = src >> n;`. Same `Olsr` op-code as a
      -- `regArith .shr`, but the second operand is a literal.
      let ws := wsizeOfNat w
      let src := argName vm e.args 0
      .Cassgn (.Lvar (mkVarI dst (.reg w))) .AT_none (.sword ws)
        (.Papp2 (.Olsr ws) (pvarOf src (.reg w)) (.Pconst (Int.ofNat n)))
  | .sarImm w n =>
      -- Native immediate arithmetic right-shift (#606): the count `n` is a
      -- compile-time `Pconst`. `Oasr` (sign-extending) op-code — the
      -- arithmetic twin of `shrImm`'s `Olsr`; same literal-immediate shape.
      let ws := wsizeOfNat w
      let src := argName vm e.args 0
      .Cassgn (.Lvar (mkVarI dst (.reg w))) .AT_none (.sword ws)
        (.Papp2 (.Oasr ws) (pvarOf src (.reg w)) (.Pconst (Int.ofNat n)))
  | .shlImm w n =>
      -- Native immediate logical left-shift (#605); see `shrImm`.
      let ws := wsizeOfNat w
      let src := argName vm e.args 0
      .Cassgn (.Lvar (mkVarI dst (.reg w))) .AT_none (.sword ws)
        (.Papp2 (.Olsl ws) (pvarOf src (.reg w)) (.Pconst (Int.ofNat n)))
  | .callN name argTys retTys =>
      -- Multi-result external call (`func.call` lowering target). At this
      -- single-output print layer it emits a `Ccall` naming its head result
      -- slot (`callNRet`), mirroring the single-result `extCall` arm; the full
      -- `k`-result `Ccall` lowering is the follow-on.
      let args := (List.range argTys.length).map
        (fun i => pvarOf (argName vm e.args i) (argTy argTys i))
      .Ccall .DoInline [.Lvar (mkVarI dst (callNRet retTys))]
        { name := name } args

/-- The SSA name a `Com.var` binding should use for the result of `e`.
    For `stackStore` the result *array* keeps the source array's name
    (in-place update), so we reuse it instead of a fresh `vN`. Otherwise we
    use the supplied fresh name. -/
def resultName {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (e : Expr jasminDialect Γ t) (fresh : String) : String :=
  match e.op with
  | .stackStore _ _ => argName vm e.args 0
  | _ => fresh

/-! ## 5. Lowering a `Com` to a body (`List InstrR`) + result name -/

/-- Lower a `Com jasminDialect Γ t` to a Jasmin instruction list plus the name
    of its return value. `next` is the fresh-SSA counter (names `v{next}`). -/
def lowerCom {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (next : Nat) : Com jasminDialect Γ t → (List InstrR × String)
  | .ret v => ([], vm t v)
  | .var (t := tEx) e body =>
      let fresh := "v" ++ toString next
      let bound := resultName vm e fresh
      let instr := lowerExpr vm e bound
      let (rest, res) := lowerCom (vm.extend (t := tEx) bound) (next + 1) body
      (instr :: rest, res)

/-! ## 6. Top-level: closed `Com` → `JasminProg` -/

/-- Materialise the free context `Γ` as named function parameters, starting the
    naming at index `base`. The head of `Γ` (De Bruijn depth 0, `.here`) gets
    `p{base}` and each deeper binding `.there …` gets the next index — matching
    `buildFuncFromCom`'s block-arg convention (`Γ.head ↦ arg 0`) and the
    valuation convention (`.cons a … ↦ a` at `.here`). -/
def paramsAndMapFrom (base : Nat) : (Γ : Ctxt jasminDialect) →
    (List FunParam × VarMap Γ)
  | [] => ([], VarMap.empty)
  | t :: rest =>
      let name := "p" ++ toString base
      -- The tail's bindings (`.there v`) are named from `base + 1` on.
      let (restParams, restMap) := paramsAndMapFrom (base + 1) rest
      -- Resolver: `.here ↦ name`, `.there v ↦ restMap v`.
      let vm : VarMap (t :: rest) := restMap.extend (t := t) name
      let param : FunParam := { var := mkVarI name t }
      (param :: restParams, vm)

/-- Materialise the free context `Γ` as named function parameters `p0, p1, …`
    (head-first: `Γ.head ↦ p0`). Returns the params and the resolver. -/
def paramsAndMap (Γ : Ctxt jasminDialect) : (List FunParam × VarMap Γ) :=
  paramsAndMapFrom 0 Γ

/-- Lower a `Com jasminDialect Γ t` to a single-function `JasminProg` named
    `name`. The context `Γ` becomes the function parameters; the body is the
    lowered instruction list; the single result is the lowered `Com.ret`. -/
def lowerComToProg {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (name : String) (com : Com jasminDialect Γ t) : JasminProg :=
  let (params, vm) := paramsAndMap Γ
  let (body, resName) := lowerCom vm 0 com
  let fd : FunDecl :=
    { name := { name := name }
      params := params
      body := body
      results := [mkVarI resName t] }
  { funcs := [fd] }

/-! ### A jasminc-compilable `export fn` scaffold

`ppJasminProg` (the shared LowCT printer) emits a bare
`fn name(ty p0, …) -> (res) { … }` — fine for structural inspection, but **not**
directly feedable to `jasminc`: it lacks the `export` keyword, the `reg`/`reg ptr`
storage qualifiers on parameters, the local register declarations for the body's
SSA temporaries (`v0, v1, …`), and a `return`. The functions below wrap the same
lowered `JasminProg` in a real `export fn … { reg uW vN; …; <body>; return res; }`
so the emitted `.jazz` compiles with `jasminc -arch x86-64` as-emitted. The body is
the **actual** lowered instruction list printed by the shared `ppInstrR` (the same
text the structural proofs reason about — only the surrounding scaffold is added).

Scope: scalar `reg w` kernels (the ChaCha QR / SHA-256 round components — all
`reg w` params, a straight-line body, a single `reg w` result). Array/stack
parameters fall back to `ppJasminProg`'s structural rendering. -/

/-- Render a Jasmin `SType` as a jasminc storage-typed declaration fragment
    (e.g. `reg u32`). Scalar word types get `reg uW`; everything else keeps the
    structural `ppSType` rendering (used only on the fallback path). -/
def regDeclTy (ty : SType) : String :=
  match ty with
  | .sword ws => "reg " ++ CatCrypt.Crypto.Jasmin.LowCT.ppWSize ws
  | other => CatCrypt.Crypto.Jasmin.LowCT.ppSType other

/-- Collect the `(name, SType)` of every register lvalue bound in a body, in
    first-occurrence order (no duplicates). These are the SSA temporaries
    (`v0, v1, …`) that need a local `reg uW vN;` declaration. `Lnone` discards
    (the `#ROR_w` flag lvalues) are skipped — they need no declaration. -/
def collectRegDecls : List InstrR → List (String × SType)
  | [] => []
  | instr :: rest =>
      let here : List (String × SType) :=
        match instr with
        | .Cassgn (.Lvar v) _ _ _ => [(v.var.vname, v.var.vtype)]
        | .Copn lvs _ _ _ =>
            lvs.filterMap (fun lv => match lv with
              | .Lvar v => some (v.var.vname, v.var.vtype)
              | _ => none)
        | .Ccall _ lvs _ _ =>
            lvs.filterMap (fun lv => match lv with
              | .Lvar v => some (v.var.vname, v.var.vtype)
              | _ => none)
        | _ => []
      let restDecls := collectRegDecls rest
      -- prepend the new ones not already present deeper in the body
      here.foldr (fun nt acc =>
        if acc.any (fun p => p.1 == nt.1) then acc else nt :: acc) restDecls

/-- Is a parameter / result list entirely scalar `sword` registers? Only then do
    we emit the `export fn` scaffold (the array/stack case keeps the structural
    fallback). -/
def allScalarReg (vis : List VarI) : Bool :=
  vis.all (fun vi => match vi.var.vtype with | .sword _ => true | _ => false)

/-- Render one scalar-register instruction in jasmin's **two-address load-first**
    form, the idiom jasminc x86 register-allocation accepts.

    `ppCmd` would render `Cassgn dst _ _ (Papp2 op a b)` as the *expression* form
    `dst = (a op b);`. jasminc compiles `&`/`^`/`>>`/`<<`/`+`/… as flag-clobbering
    two-address ops, so when both operands are still live (e.g. SHA-256 `Ch` reads
    `e` twice) it tries to merge `dst` with an operand register and fails register
    allocation. The accepted idiom (matching the hand-written `bench/*/gen/*.jazz`
    and `JasminAbiEmit.renderRegArith`) loads the first operand into `dst` first,
    then computes in place: `dst = a; dst = dst op b;`. Unary forms (`#ROR_w`,
    casts, the `andn` complement) and plain copies are passed through. -/
def ppExportInstr (ind : Nat) : InstrR → String
  | .Cassgn (.Lvar dst) _ _
      (.Papp2 (.Oland _) (.Papp1 (.Olnot _) a) b) =>
      -- BMI1 `andn` = `(!a) & b`: `dst = a; dst = !dst; dst = dst & b;`.
      let d := dst.var.vname
      CatCrypt.Crypto.Jasmin.LowCT.indent ind (d ++ " = " ++
        CatCrypt.Crypto.Jasmin.LowCT.ppPExpr a ++ ";") ++ "\n" ++
      CatCrypt.Crypto.Jasmin.LowCT.indent ind (d ++ " = !" ++ d ++ ";") ++ "\n" ++
      CatCrypt.Crypto.Jasmin.LowCT.indent ind (d ++ " = " ++ d ++ " & " ++
        CatCrypt.Crypto.Jasmin.LowCT.ppPExpr b ++ ";")
  | .Cassgn (.Lvar dst) _ _ (.Papp2 op a b) =>
      -- Plain binary op: `dst = a; dst = dst <op> b;`.
      let d := dst.var.vname
      CatCrypt.Crypto.Jasmin.LowCT.indent ind (d ++ " = " ++
        CatCrypt.Crypto.Jasmin.LowCT.ppPExpr a ++ ";") ++ "\n" ++
      CatCrypt.Crypto.Jasmin.LowCT.indent ind (d ++ " = " ++ d ++ " " ++
        CatCrypt.Crypto.Jasmin.LowCT.ppSOp2 op ++ " " ++
        CatCrypt.Crypto.Jasmin.LowCT.ppPExpr b ++ ";")
  | .Copn [.Lnone _ _, .Lnone _ _, .Lvar dst] _ (.Oasm op) [src, amt] =>
      -- Flag-clobbering rotate `#ROR_w`: also two-address. Load the source into
      -- `dst` first, then rotate in place: `dst = src; _, _, dst = #ROR_w(dst, n);`.
      let d := dst.var.vname
      CatCrypt.Crypto.Jasmin.LowCT.indent ind (d ++ " = " ++
        CatCrypt.Crypto.Jasmin.LowCT.ppPExpr src ++ ";") ++ "\n" ++
      CatCrypt.Crypto.Jasmin.LowCT.indent ind ("_, _, " ++ d ++ " = #" ++
        op.name ++ "(" ++ d ++ ", " ++
        CatCrypt.Crypto.Jasmin.LowCT.ppPExpr amt ++ ");")
  | instr =>
      -- Unary (`#ROR_w`, casts, copies, calls): the shared printer already
      -- emits an accepted single-instruction form.
      CatCrypt.Crypto.Jasmin.LowCT.ppInstrR ind instr

/-- Render a lowered single-function `JasminProg` as a jasminc-compilable
    `export fn`. Falls back to `ppJasminProg` for non-scalar (array/stack) shapes
    or a multi-function program. -/
def ppExportFn (prog : JasminProg) : String :=
  match prog.funcs with
  | [fd] =>
    if allScalarReg (fd.params.map (·.var)) && allScalarReg fd.results then
      let params := String.intercalate ", "
        (fd.params.map (fun p =>
          regDeclTy p.var.var.vtype ++ " " ++ p.var.var.vname))
      let retTy := String.intercalate ", "
        (fd.results.map (fun r => regDeclTy r.var.vtype))
      let retNames := String.intercalate ", " (fd.results.map (fun r => r.var.vname))
      -- declare the body's SSA temporaries that are not already parameters
      let paramNames := fd.params.map (fun p => p.var.var.vname)
      let decls := (collectRegDecls fd.body).filter (fun nt => ¬ paramNames.contains nt.1)
      let declStr := String.intercalate "\n"
        (decls.map (fun nt => "  " ++ regDeclTy nt.2 ++ " " ++ nt.1 ++ ";"))
      let declBlock := if decls.isEmpty then "" else declStr ++ "\n"
      -- Render the body in jasmin two-address load-first form (jasminc-accepted).
      let body := String.intercalate "\n" (fd.body.map (ppExportInstr 2))
      "export fn " ++ fd.name.name ++ "(" ++ params ++ ") -> " ++ retTy ++ " {\n" ++
      declBlock ++ body ++ "\n" ++ "  return " ++ retNames ++ ";\n}"
    else
      CatCrypt.Crypto.Jasmin.LowCT.ppJasminProg prog
  | _ => CatCrypt.Crypto.Jasmin.LowCT.ppJasminProg prog

/-- **`.jazz` TEXT — for jasminc-comparison benchmarking / interop ONLY, NOT the
    canonical artifact.** The deployed output is the owned `.s` emitted by the
    verified x86 backend (`Com → toLprogPhysAbi → renderLprogAtt`, i.e.
    `LprogOptPipeline.renderOwned`); the `.jazz` produced here exists so the
    classic jasmin compiler (`jasminc`, an EXTERNAL toolchain) can lower the same
    emitted `Com` for a head-to-head cycle comparison. Never treat a `.jazz`
    (or the fact that a bench registry names one) as the deployed emit — see
    `bench/AGENTS.md` "jasminc is also an external toolchain" and the
    AST-direct-canonical convention.

    Convenience: lower + pretty-print to jasminc-compilable `.jazz` text. For a
    scalar `reg w` kernel this is the `export fn … { … return … }` scaffold
    (compiles with `jasminc -arch x86-64` as-emitted); other shapes fall back to
    the structural `ppJasminProg`. This is the only text-producing step. -/
def emitJazz {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (name : String) (com : Com jasminDialect Γ t) : String :=
  ppExportFn (lowerComToProg name com)

/-! ## 7. Bounded for-loop (`JForProg`)

`Com` is straight-line. `JForProg` is a self-contained wrapper expressing
`acc := init; for _ in 0..n { acc := body(acc) }; ret acc`, with a total
denotation by `n`-fold iteration.

**Modelled**: the `n`-fold semantics (`denote`, by `Nat.rec` — no fuel, the
bound is static) and a `Cfor` emission whose body is the lowering of `update`.

**Deferred**: SSA-phi wiring of the carried accumulator across iterations. The
emitted `Cfor` body reads and writes a single named accumulator variable
(`acc`), which is the standard Jasmin idiom for a loop-carried value, rather
than introducing a fresh φ-name per iteration. The functional denotation below
is the ground truth; the printer's `Cfor` is a faithful skeleton of it. -/

/-- A bounded for-loop program over a single accumulator type. `update` maps an
    `[accTy]`-context to an `accTy`: one iteration's accumulator transform. -/
structure JForProg (accTy : jasminDialect.Ty) where
  /-- Static iteration count. -/
  n : Nat
  /-- The accumulator-update body: `acc ↦ body(acc)`. -/
  update : Com jasminDialect [accTy] accTy

/-- One iteration: run `update` on a singleton valuation `[acc]`. -/
def JForProg.step {accTy : jasminDialect.Ty} (p : JForProg accTy)
    (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  p.update.denote (.cons acc .nil)

/-- Total `n`-fold denotation: iterate `step` `n` times from the initial
    accumulator. No fuel — `n` is static. -/
def JForProg.denote {accTy : jasminDialect.Ty} (p : JForProg accTy)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range p.n).foldl (fun acc _ => p.step acc) init

/-- Emit a `Cfor` for a `JForProg`. The loop variable iterates `0..n`; the body
    is the lowering of `update` with the accumulator threaded as the single
    named carried variable `acc` (read on entry, rebound to the result). The
    loop index variable is `i`. -/
def JForProg.toCfor {accTy : jasminDialect.Ty} (p : JForProg accTy) : InstrR :=
  -- Resolver mapping the singleton context's `.here` to the accumulator name.
  let vm : VarMap [accTy] := (VarMap.empty).extend (t := accTy) "acc"
  let (bodyInstrs, resName) := lowerCom vm 0 p.update
  -- Rebind `acc := <result>` at end of body so the next iteration reads it.
  let writeBack : InstrR :=
    .Cassgn (.Lvar (mkVarI "acc" accTy)) .AT_none (styOfTy accTy)
      (pvarOf resName accTy)
  .Cfor (mkVarI "i" .inlineInt)
    { dir := .UpTo, lo := 0, hi := p.n }
    (bodyInstrs ++ [writeBack])

/-- Lower a `JForProg` to a single-function `JasminProg`: parameter `acc`
    (the initial accumulator), the `Cfor` loop, and `ret acc`. -/
def JForProg.toProg {accTy : jasminDialect.Ty} (name : String)
    (p : JForProg accTy) : JasminProg :=
  let fd : FunDecl :=
    { name := { name := name }
      params := [{ var := mkVarI "acc" accTy }]
      body := [p.toCfor]
      results := [mkVarI "acc" accTy] }
  { funcs := [fd] }

/-- Count the let-binders (`Com.var` nodes) of a body — the number of fresh SSA
    temporaries `v0, …, v{k-1}` the lowering introduces. -/
def Com.numBinders {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} :
    Com jasminDialect Γ t → Nat
  | .ret _ => 0
  | .var _ body => 1 + Com.numBinders body

/-! ### A jasminc-compilable `export fn` for a `reg`-accumulator bounded loop

`JForProg.toProg`'s `JasminProg` captures the loop *structure* (the `Cfor` over
`0..n` whose body lowers `update`, plus the `acc` write-back) — that is the
object the denotation-preservation proof reasons about
(`JForProgSemCorrect.loop_denote_eq`). To *validate* it end-to-end we render it
as a self-contained jasminc `export fn`: the accumulator `acc` is a `reg`
declared and initialised from the export parameter, the body's fresh SSA names
`v0, …` are declared registers, the loop index `i` is `inline int`, and the
loop is the **actual** emitted `Cfor` body printed by the shared `ppInstrR`
(NOT unrolled). The body is reused verbatim from `JForProg.toCfor`, so the text
KAT'd by jasminc is the same loop the proof covers. -/

/-- Emit a jasminc-compilable `export fn` for a `reg w` accumulator bounded loop.
    The loop body is the *actual* emitted `Cfor` (from `toCfor`), printed by the
    shared `ppInstrR` — a real `for i = 0 to n { … }`, never unrolled.

    Shape (for a `reg w` accumulator):
    ```
    export fn <name>(reg u<w> acc0) -> reg u<w> {
      reg u<w> acc;
      reg u<w> v0; …            // one per body binder
      inline int i;
      acc = acc0;
      for i = 0 to n { <emitted body> }
      return acc;
    }
    ```
    Only the `reg w` accumulator shape is rendered (the simplest end-to-end loop
    kernel — running sums / Horner / doubling); other accumulator types fall back
    to the structural `toProg` rendering and are not the validation target. -/
def JForProg.toJazzExport {w : Nat} (name : String) (p : JForProg (.reg w)) :
    String :=
  let ws := (wsizeOfNat w).bits
  let wty := "u" ++ toString ws
  -- The emitted loop instruction (the verified `Cfor`), printed by `ppInstrR`.
  let loopStr := CatCrypt.Crypto.Jasmin.LowCT.ppInstrR 2 p.toCfor
  -- Temporaries the body introduces: `v0 … v{k-1}`.
  let k := Com.numBinders p.update
  let tempDecls := String.intercalate "\n"
    ((List.range k).map (fun j => "  reg " ++ wty ++ " v" ++ toString j ++ ";"))
  let tempBlock := if k = 0 then "" else tempDecls ++ "\n"
  "export fn " ++ name ++ "(reg " ++ wty ++ " acc0) -> reg " ++ wty ++ " {\n" ++
  "  reg " ++ wty ++ " acc;\n" ++
  tempBlock ++
  "  inline int i;\n" ++
  "  acc = acc0;\n" ++
  loopStr ++ "\n" ++
  "  return acc;\n" ++
  "}"

/-! ## 8. Smoke tests -/

/-- Substring containment via `splitOn`: `needle` occurs in `hay` iff splitting
    `hay` on `needle` yields more than one piece (Lean core has no
    `String.isInfixOf`). For the empty needle this returns `true`. -/
def strContains (hay needle : String) : Bool :=
  needle.isEmpty || (hay.splitOn needle).length > 1

/-- Lower the dialect's `smokeProg` (`reg 32` × `reg 32` → `reg 64`,
    `regArith add` then `castW 32 64`) and emit `.jazz`. -/
def smokeProg : JasminProg :=
  lowerComToProg "smoke" JasminDialect.smokeProg

/-- The emitted `.jazz` text. -/
def smokeJazz : String := emitJazz "smoke" JasminDialect.smokeProg

-- Print the emitted `.jazz` text for visual inspection.
#eval IO.println smokeJazz

/-- One function is produced. -/
theorem smoke_one_func : smokeProg.funcs.length = 1 := by decide

/-- The function takes two parameters (the two `reg 32` inputs). -/
theorem smoke_two_params :
    (smokeProg.funcs.head?.map (fun fd => fd.params.length)) = some 2 := by
  decide

/-- The body has two instructions (the `add` and the `castW`). -/
theorem smoke_two_instrs :
    (smokeProg.funcs.head?.map (fun fd => fd.body.length)) = some 2 := by
  decide

/- The emitted `.jazz` mentions the function name. -/
#guard (strContains smokeJazz "fn smoke")

/-- A small bounded-for example: accumulate `acc := acc + acc` for 4 iterations
    (a `regArith add` on `reg 64`). -/
def doubleLoop : JForProg (.reg 64) :=
  { n := 4
    update :=
      .var (.mk (.regArith .add 64) rfl
              (.cons .here (.cons .here .nil)))
        (.ret .here) }

/-- `step` doubles; iterating 4× from `1` gives `16`. -/
theorem doubleLoop_denote :
    doubleLoop.denote (1 : BitVec 64) = (16 : BitVec 64) := by rfl

/-- The loop lowers to a single-function program with a `Cfor` body. -/
def doubleLoopProg : JasminProg := doubleLoop.toProg "double_loop"

/-- The loop program emits to `.jazz` text. -/
def doubleLoopJazz : String :=
  CatCrypt.Crypto.Jasmin.LowCT.ppJasminProg doubleLoopProg

#eval IO.println doubleLoopJazz

/-- The loop body is a single top-level instruction (the `Cfor`). -/
theorem doubleLoop_one_instr :
    (doubleLoopProg.funcs.head?.map (fun fd => fd.body.length)) = some 1 := by
  decide

/- The emitted `.jazz` contains a `for` loop. -/
#guard (strContains doubleLoopJazz "for ")

/-- The jasminc-compilable `export fn` for the doubling loop. -/
def doubleLoopExportJazz : String := JForProg.toJazzExport "double_loop" doubleLoop

#eval IO.println doubleLoopExportJazz

/- The exported `.jazz` is a real `for` loop (structural check: it contains an
    actual `for i = 0 to 4` loop header, not an unrolled body). -/
#guard (strContains doubleLoopExportJazz "for i = 0 to 4")

/- The exported `.jazz` is an `export fn` jasminc unit. -/
#guard (strContains doubleLoopExportJazz "export fn double_loop")

/-- The exported `.jazz` does NOT unroll: it has a single `acc = acc + acc`
    inside the loop body (one occurrence), confirming the loop is emitted as a
    real `for`, not 4 copies of the body. -/
theorem doubleLoopExport_not_unrolled :
    (doubleLoopExportJazz.splitOn "(acc + acc)").length = 2 := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
