/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect

set_option autoImplicit false

/-!
# SIMD (`vsimd`) arm of the `CProg`-free direct front (`translateDialectControlV`)

`TranslateDialectDirectControl.translateDialectControl` fuses the whole
non-`while` scalar `LowCT` (`RScalarSetExpr`, the leaf-call arms, `RFor`,
`RIfNz`) into a `CProg`-free `Com catCryptDialect` recursion. Its coverage
fragment `IsCoveredCtl` is proved to **coincide with the deprecated `translate`
(CProg) front** on `⟨Γ', vm⟩` — every op it emits is one `CProg` already had.

The **128-bit SIMD** ops (`gf2p8mulb`/`vpshufb`/`clmul`/`affineqb`/`bitwise`/…,
plus the whole-register byte-shifts `vpsrldq`/`vpslldq`) are a genuinely **new**
front capability: they thread a `.sword 128` register value (`mapTy .sword 128 =
.reg 128`), and CryptoSSA's `CProg`/`translate` never carried a `.sword 128`
binding (`encodeTy` has no `.sword 128` image). So — exactly like the divergent
`RLetZero` dead-init elision, which `translateDialectFull` also handles outside
`IsCovered` — the SIMD arm cannot join the `translate`-agreeing fragment without
extending the deprecated `CProg` IR (forbidden). It is instead handled here, in
an isolated wrapper front `translateDialectControlV`, whose end-to-end guarantee
is the **concrete pilot's `denote = spec`** composed with the already-proved
generic lowering preservation `cryptoDialectToJasminCom_denote_eq'` — NOT the
`rustExecSimulatesDialect` / leak-factoring lemmas (which are stated relative to
the `CProg` front and cannot mention an op `CProg` lacks).

## Source shape (no new `LowCT` constructor)

A SIMD op is authored as an ordinary `LowCT.RCall` whose function name is a
`vsimd`-tag (`vsimdTag`) and whose operands are `.sword 128` slots:

```
  RCall "vsimd.gf2p8mulb" ⟨"prod",_⟩ [⟨"a",_⟩, ⟨"b",_⟩]   -- prod := gf2p8mulb(a,b)
  RCall "vpsrldq.8"       ⟨"s8",_⟩   [⟨"prod",_⟩]           -- s8   := prod >> 8 bytes
```

`translateDialectControlV` intercepts these `RCall`s and emits the matching
`CatCryptDialect` op (`.vsimd op` / `.vpsrldqC n` / `.vpslldqC n`) binding the
destination at `.sword 128`; **every other** `LowCT` arm (including a non-`vsimd`
`RCall`) delegates unchanged to `translateDialectControl`. Reusing `RCall`
(rather than a new `LowCT` constructor) keeps the change to this one file — no
cascade through the ~35 `LowCT`-matching modules.

The 128-bit input values enter as `.sword 128` **context parameters** (the front
context `Γ` is a bare `Ctx = List CryptoTy`, so `.sword 128` slots are placed
directly, needing no `TowerType`).
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (SimdOp)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (gf2p8mulbW)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located)

/-! ## 1. The `vsimd`-tag parser

A `vsimd`-tagged `RCall` function name is either a binary SIMD op tag
(`"vsimd.<op>"`) or a whole-register byte-shift (`"vpsrldq.<n>"` / `"vpslldq.<n>"`).
`VsimdTag` is the parsed result: a binary `SimdOp`, or a unary byte-shift op. -/

/-- Parsed `vsimd`-tag: a binary `SimdOp` (both operands `.sword 128`) or a unary
    whole-register byte-shift (`srl`/`sll` by `n` bytes). -/
inductive VsimdTag where
  /-- Binary SIMD op (`gf2p8mulb`/`vpshufb`/`bitwise`/`affineqb`/`clmul`/`packed`/…). -/
  | binary (op : SimdOp)
  /-- `vpsrldq n`: whole-128-bit right byte-shift by `n` bytes. -/
  | srl (n : Nat)
  /-- `vpslldq n`: whole-128-bit left byte-shift by `n` bytes. -/
  | sll (n : Nat)
  /-- `vpshufd imm`: per-lane dword shuffle (UNARY). Emits `.vpshufdC imm`. -/
  | ushuf (imm : Nat)
  /-- `vaeskeygenassist rcon`: key-schedule assist (UNARY). Emits `.vaeskeygenC rcon`. -/
  | ukeygen (rcon : BitVec 8)
  /-- `vconst128 val`: a BAKED 128-bit immediate (NULLARY, no operands). Emits
      `.vconst128 val`; the constant is carried in the tag itself. -/
  | vconst (val : BitVec 128)
  /-- `vsha256rnds2`: SHA-NI two-round step (TERNARY: abef, cdgh, mk). Emits
      `.vsha256rnds2`. -/
  | sha256rnds2
  /-- `vsha256msg1`: SHA-NI message-schedule partial step (BINARY). Emits
      `.vsha256msg1`. -/
  | sha256msg1
  /-- `vsha256msg2`: SHA-NI message-schedule final step (BINARY). Emits
      `.vsha256msg2`. -/
  | sha256msg2
  /-- `vloadidx128`: a **128-bit dynamic array load** — read `arr[idx]` at 128-bit
      granularity, where `arr` is a `.memref n` slot and `idx` a `.sword 64` slot.
      BINARY-shaped `RCall` (`[arr, idx]`), but the operands are a memref + a
      scalar index, NOT two `.sword 128` registers, so it does NOT go through
      `lookupReg128`; the front arm resolves `arr` via `lookupMemrefV` and `idx`
      via `lookupU64`, and emits `.memrefGetDyn128 n`. It is deliberately absent
      from `semV` (the SEnv models only 128-bit register values; a memref array +
      64-bit index live outside it), so the SEnv-based
      `translateDialectControlV_denote` homomorphism is vacuous on it — its
      whole-program correctness is instead the concrete `Com.denote = spec`
      (a memref-valuation `native_decide`, exercising `memrefGetDyn128`). -/
  | loadidx128
  deriving DecidableEq

/-- Parse a single hex digit (`0-9`/`a-f`/`A-F`). -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Parse a hex string (optional `0x`/`0X` prefix) into a `Nat`. `none` on an
    empty string or a non-hex character. Used to parse the baked-constant token of
    the `"vsimd.vconst.<hex>"` tag (`String.toNat?` is decimal-only). -/
def parseHexNat (s : String) : Option Nat :=
  let s := if s.startsWith "0x" ∨ s.startsWith "0X" then s.drop 2 else s
  if s.isEmpty then none
  else s.foldl (fun acc c =>
    match acc, hexDigit? c with
    | some a, some d => some (a * 16 + d)
    | _, _ => none) (some 0)

/-- Parse a `JasminBinOp` token (for the `packed.<bop>.<laneW>` tag). -/
def parseBop : String → Option JasminBinOp
  | "add" => some .add | "sub" => some .sub | "mul" => some .mul
  | "and" => some .and | "or"  => some .or  | "xor" => some .xor
  | "shl" => some .shl | "shr" => some .shr
  | _ => none

/-- Parse the binary-`SimdOp` token following `"vsimd."`. Covers the data-free
    GF-MQ / AES / GHASH SIMD alphabet the owned backend renders. The
    data-carrying ops (`affineqb`/`clmul`/`packed`) have their own `vsimdTag`
    syntax (they need an immediate / lane-width). -/
def parseSimdOp : String → Option SimdOp
  | "gf2p8mulb" => some .gf2p8mulb
  | "vpshufb"   => some .vpshufb
  | "xor"       => some (.bitwise .xor)
  | "and"       => some (.bitwise .and)
  | "or"        => some (.bitwise .or)
  | "vaesenc"     => some .vaesenc
  | "vaesenclast" => some .vaesenclast
  | "mulhi16"     => some .mulhi16
  | _ => none

/-- Parse a `vsimd`-tagged function name into a `VsimdTag`, or `none` if the name
    is not a SIMD tag (an ordinary crypto-leaf `RCall`). Syntax (full SimdOp
    alphabet): `"vsimd.<op>"`, `"affineqb.<imm>"`, `"clmul.<imm>"`,
    `"packed.<bop>.<laneW>"`, `"vpsrldq.<n>"`, `"vpslldq.<n>"`,
    `"vpshufd.<imm>"`, `"vaeskeygen.<rcon>"`. -/
def vsimdTag (fname : String) : Option VsimdTag :=
  match fname.splitOn "." with
  | ["vsimd", op]    => (parseSimdOp op).map .binary
  | ["vsimd", "vconst", h] =>
      (parseHexNat h).map (fun n => .vconst (BitVec.ofNat 128 n))
  | ["affineqb", n]  => (n.toNat?).map (fun i => .binary (.affineqb (BitVec.ofNat 8 i)))
  | ["clmul", n]     => (n.toNat?).map (fun i => .binary (.clmul i))
  | ["packed", op, lw] =>
      match parseBop op, lw.toNat? with
      | some b, some w => some (.binary (.packed b w))
      | _, _ => none
  | ["vpsrldq", n]   => (n.toNat?).map .srl
  | ["vpslldq", n]   => (n.toNat?).map .sll
  | ["vpshufd", n]   => (n.toNat?).map .ushuf
  | ["vaeskeygen", n] => (n.toNat?).map (fun i => .ukeygen (BitVec.ofNat 8 i))
  | ["vsha256rnds2"] => some .sha256rnds2
  | ["vsha256msg1"]  => some .sha256msg1
  | ["vsha256msg2"]  => some .sha256msg2
  | ["vloadidx128"]  => some .loadidx128
  | _ => none

/-! ## 2. Reg-128 slot lookup + the `vsimd` emit builders -/

/-- Look up a `.sword 128` (reg-128) slot by name; `none` if unbound or not a
    128-bit vector slot. The SIMD twin of `TranslateDialectDirectArms.lookupU64`. -/
def lookupReg128 {Γ : Ctx} (vm : VarMap Γ) (name : String) :
    Option (CVar Γ (.sword 128)) :=
  match vm.lookup name with
  | some ⟨.sword 128, v⟩ => some v
  | _ => none

/-- Look up a `.memref n` (array) slot by name, returning its size `n` and the
    typed variable; `none` if unbound or not a memref slot. The memref twin of
    `lookupReg128`, used by the `vloadidx128` (128-bit dynamic load) front arm. -/
def lookupMemrefV {Γ : Ctx} (vm : VarMap Γ) (name : String) :
    Option (Σ n : Nat, CVar Γ (.memref n)) :=
  match vm.lookup name with
  | some ⟨.memref n, v⟩ => some ⟨n, v⟩
  | _ => none

/-! ## 3. The SIMD-aware front `translateDialectControlV`

Intercepts `vsimd`-tagged `RCall`s (emitting `.vsimd`/`.vpsrldqC`/`.vpslldqC`)
and delegates every other arm to `translateDialectControl`. `RSeq`/`RBlock`/
`RSkip` are handled here so nested SIMD `RCall`s inside a straight-line block are
caught; all other structural arms (`RFor`, `RIfNz`, the scalar leaf calls) fall
through to `translateDialectControl` unchanged. -/

/-- SIMD-aware `CProg`-free front. Structural recursion on `LowCT`. -/
def translateDialectControlV {Γ : Ctx} (vm : VarMap Γ) :
    LowCT → Option (DTransOut Γ)
  | .RSkip => some { Γ' := Γ, cont := ComCont.id, vm := vm }
  | .RBlock body => translateDialectControlV vm body
  | .RSeq c₁ c₂ =>
      match translateDialectControlV vm c₁ with
      | some o₁ =>
          match translateDialectControlV o₁.vm c₂ with
          | some o₂ =>
              some { Γ' := o₂.Γ', cont := ComCont.comp o₁.cont o₂.cont, vm := o₂.vm }
          | none => none
      | none => none
  | .RCall fname dst args =>
      match vsimdTag fname, args with
      | some (.binary op), [a, b] =>
          match lookupReg128 vm a.locVar, lookupReg128 vm b.locVar with
          | some va, some vb =>
              let e : Expr catCryptDialect Γ (.sword 128) :=
                { op := .vsimd op, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some { Γ' := .sword 128 :: Γ, cont := ComCont.varBind e,
                     vm := vm.bind dst.locVar }
          | _, _ => translateDialectControl vm (.RCall fname dst args)
      | some (.srl n), [a] =>
          match lookupReg128 vm a.locVar with
          | some va =>
              let e : Expr catCryptDialect Γ (.sword 128) :=
                { op := .vpsrldqC n, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }
              some { Γ' := .sword 128 :: Γ, cont := ComCont.varBind e,
                     vm := vm.bind dst.locVar }
          | _ => translateDialectControl vm (.RCall fname dst args)
      | some (.sll n), [a] =>
          match lookupReg128 vm a.locVar with
          | some va =>
              let e : Expr catCryptDialect Γ (.sword 128) :=
                { op := .vpslldqC n, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }
              some { Γ' := .sword 128 :: Γ, cont := ComCont.varBind e,
                     vm := vm.bind dst.locVar }
          | _ => translateDialectControl vm (.RCall fname dst args)
      | some (.ushuf imm), [a] =>
          match lookupReg128 vm a.locVar with
          | some va =>
              let e : Expr catCryptDialect Γ (.sword 128) :=
                { op := .vpshufdC imm, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }
              some { Γ' := .sword 128 :: Γ, cont := ComCont.varBind e,
                     vm := vm.bind dst.locVar }
          | _ => translateDialectControl vm (.RCall fname dst args)
      | some (.ukeygen rcon), [a] =>
          match lookupReg128 vm a.locVar with
          | some va =>
              let e : Expr catCryptDialect Γ (.sword 128) :=
                { op := .vaeskeygenC rcon, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }
              some { Γ' := .sword 128 :: Γ, cont := ComCont.varBind e,
                     vm := vm.bind dst.locVar }
          | _ => translateDialectControl vm (.RCall fname dst args)
      | some (.vconst v), [] =>
          -- NULLARY: the baked 128-bit constant carries no operands.
          let e : Expr catCryptDialect Γ (.sword 128) :=
            { op := .vconst128 v, retTy_eq := rfl, args := .nil }
          some { Γ' := .sword 128 :: Γ, cont := ComCont.varBind e,
                 vm := vm.bind dst.locVar }
      | some .sha256rnds2, [a, b, c] =>
          -- TERNARY SHA-NI two-round step: (abef, cdgh, mk).
          match lookupReg128 vm a.locVar, lookupReg128 vm b.locVar,
              lookupReg128 vm c.locVar with
          | some va, some vb, some vc =>
              let e : Expr catCryptDialect Γ (.sword 128) :=
                { op := .vsha256rnds2, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) (.cons (toVIRVar vc) .nil)) }
              some { Γ' := .sword 128 :: Γ, cont := ComCont.varBind e,
                     vm := vm.bind dst.locVar }
          | _, _, _ => translateDialectControl vm (.RCall fname dst args)
      | some .sha256msg1, [a, b] =>
          match lookupReg128 vm a.locVar, lookupReg128 vm b.locVar with
          | some va, some vb =>
              let e : Expr catCryptDialect Γ (.sword 128) :=
                { op := .vsha256msg1, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some { Γ' := .sword 128 :: Γ, cont := ComCont.varBind e,
                     vm := vm.bind dst.locVar }
          | _, _ => translateDialectControl vm (.RCall fname dst args)
      | some .sha256msg2, [a, b] =>
          match lookupReg128 vm a.locVar, lookupReg128 vm b.locVar with
          | some va, some vb =>
              let e : Expr catCryptDialect Γ (.sword 128) :=
                { op := .vsha256msg2, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some { Γ' := .sword 128 :: Γ, cont := ComCont.varBind e,
                     vm := vm.bind dst.locVar }
          | _, _ => translateDialectControl vm (.RCall fname dst args)
      | some .loadidx128, [arr, idx] =>
          -- 128-bit dynamic array load `dst := arr[idx]`: `arr` a `.memref n`
          -- slot, `idx` a `.sword 64` slot, `dst` bound at `.sword 128`.
          match lookupMemrefV vm arr.locVar, lookupU64 vm idx.locVar with
          | some ⟨n, arrV⟩, some idxV =>
              let e : Expr catCryptDialect Γ (.sword 128) :=
                { op := .memrefGetDyn128 n, retTy_eq := rfl,
                  args := .cons (toVIRVar arrV) (.cons (toVIRVar idxV) .nil) }
              some { Γ' := .sword 128 :: Γ, cont := ComCont.varBind e,
                     vm := vm.bind dst.locVar }
          | _, _ => translateDialectControl vm (.RCall fname dst args)
      | _, _ => translateDialectControl vm (.RCall fname dst args)
  | c => translateDialectControl vm c

/-- Top-level SIMD-aware front: emit the `constUnit; ret` terminator at the final
    context (mirrors `translateDialectControlTop`). -/
def translateDialectControlVTop {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) :
    Option (Σ Γ' : Ctx, Com catCryptDialect Γ' .unit) :=
  match translateDialectControlV vm c with
  | some o =>
      let term : Com catCryptDialect o.Γ' .unit :=
        Com.var { op := .constUnit, retTy_eq := rfl, args := .nil } (.ret .here)
      some ⟨o.Γ', term⟩
  | none => none

/-! ## 4. Coverage marker for the SIMD arm

`IsCoveredV` marks the SIMD `RCall` arms this front adds on top of
`translateDialectControl`. It is deliberately **separate** from `IsCoveredCtl`:
the SIMD ops are the divergent-from-`CProg` capability (see the module
docstring), so — unlike `IsCoveredCtl` — there is no context-agreement lemma to
the `translate` front (`CProg` has no `.sword 128` binding to agree with). The
guarantee is instead the concrete `denote = spec` pin at the pilot, composed
with the verified `cryptoDialectToJasminCom` lowering. -/

/-- The SIMD-covered arms: a `vsimd`-tagged binary/unary `RCall` over `.sword 128`
    operands, plus straight-line `RSeq`/`RBlock`/`RSkip` closure. -/
inductive IsCoveredV : LowCT → Prop
  | rSkip : IsCoveredV .RSkip
  | rBlock {body : LowCT} : IsCoveredV body → IsCoveredV (.RBlock body)
  | rSeq {c₁ c₂ : LowCT} : IsCoveredV c₁ → IsCoveredV c₂ → IsCoveredV (.RSeq c₁ c₂)
  | rVsimd (fname : String) (dst : Located) (args : List Located) :
      (vsimdTag fname).isSome → IsCoveredV (.RCall fname dst args)

/-! ## 5. Worked example -/

/-- The empty program lowers through the SIMD-aware front. -/
example : (translateDialectControlVTop (Γ := []) VarMap.empty .RSkip).isSome := by
  decide

/-! ## 6. `.sword 128`-returning result program (for rendering / denotation)

The `…VTop` wrapper returns a `unit`-typed terminator (it exists only for the
context-agreement plumbing — like `translateDialectControlTop`, the emitted
prefix `o.cont` is not re-applied there). For rendering to owned `.s` and for the
`denote = spec` gate the kernels need the emitted `Com` that **returns the result
vector**. `vsimdResultProg` applies the emitted prefix `o.cont` to a `Com.ret` on
the named `.sword 128` result slot — the vector twin of
`ScalarSExprFrontValidate.frontResultProg`. -/

/-- The full front-emitted `vsimd` program returning the `.sword 128` slot named
    `retName`. `none` if the front declines, or `retName` is not a bound 128-bit
    slot. -/
def vsimdResultProg {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) (retName : String) :
    Option (Com catCryptDialect Γ (.sword 128)) :=
  match translateDialectControlV vm c with
  | some o =>
      match lookupReg128 o.vm retName with
      | some v => o.cont (Com.ret (toVIRVar v))
      | none => none
  | none => none

/-- `RVsimdSetExpr` bodies are `IsCoveredV`: `RVsimdSetExpr x tag args` is a
    `vsimd`-tagged `RCall`, so it is covered whenever the tag parses. -/
theorem isCoveredV_RVsimdSetExpr (x tag : String) (args : List String)
    (h : (vsimdTag tag).isSome) :
    IsCoveredV (LowCT.RVsimdSetExpr x tag args) :=
  IsCoveredV.rVsimd tag ⟨x, .TU64⟩ (args.map (fun s => ⟨s, .TU64⟩)) h

/-! ## 7. End-to-end validate: a small `vsimd` LowCT body

A two-op body authored with the dedicated vector node `RVsimdSetExpr`
(`out := gf2p8mulb(a,b) ⊕ a`) is pushed through the vector front and shown to
(1) **translate**, (2) **lower** to `Com jasminDialect` through the verified
`cryptoDialectToJasminCom` (reaching owned `.s`), and (3) **denote = spec** on
sample 128-bit inputs — the front-arm correctness gate, the vector analog of
`ScalarSExprFrontValidate`. -/

/-- Two 128-bit vector params `a` (`.here`), `b` (`.there .here`). -/
def vΓ : Ctx := [.sword 128, .sword 128]

/-- `VarMap` binding `a`, `b` to the two 128-bit slots. -/
def vVM : VarMap vΓ := (VarMap.empty.bind "b").bind "a"

/-- A small `vsimd` body written with the dedicated vector node:
    `prod := gf2p8mulb(a,b)`; `out := prod ⊕ a`. -/
def vBody : LowCT :=
  .RSeq (LowCT.RVsimdSetExpr "prod" "vsimd.gf2p8mulb" ["a", "b"])
        (LowCT.RVsimdSetExpr "out"  "vsimd.xor"       ["prod", "a"])

/-- The body is `IsCoveredV` (both ops are vsimd-tagged). -/
theorem vBody_covered : IsCoveredV vBody :=
  .rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
        (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))

/-- (1) The body translates through the vector front. -/
theorem vBody_translates : (translateDialectControlV vVM vBody).isSome := by native_decide

/-- The front-emitted result program (returns the `.sword 128` slot `out`). -/
def vProg : Option (Com catCryptDialect vΓ (.sword 128)) := vsimdResultProg vVM vBody "out"

/-- The front actually emits a result program. -/
theorem vProg_isSome : vProg.isSome := by native_decide

/-- (2) It lowers end-to-end to `Com jasminDialect` through the verified
    `cryptoDialectToJasminCom` map — i.e. it reaches owned `.s`. -/
theorem vProg_lowers : (vProg.bind cryptoDialectToJasminCom).isSome := by native_decide

/-- The pure-Lean spec value of `vBody`: `gf2p8mulb(a,b) ⊕ a`. -/
def vSpec (a b : BitVec 128) : BitVec 128 := gf2p8mulbW a b ^^^ a

/-- Denote the front-emitted program at inputs `a` (slot `a`), `b` (slot `b`). -/
def vDenote (a b : BitVec 128) : Option (BitVec 128) :=
  vProg.map (fun com => com.denote (.cons a (.cons b .nil)))

/-! ### (3) `denote = spec` on sample 128-bit inputs -/

example : vDenote 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f 0x00112233445566778899aabbccddeeff
    = some (vSpec 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f 0x00112233445566778899aabbccddeeff) := by
  native_decide

example : vDenote 0 0 = some (vSpec 0 0) := by native_decide

example : vDenote 0xffffffffffffffffffffffffffffffff 0x0102040810204080ff00ff00ff00ff00
    = some (vSpec 0xffffffffffffffffffffffffffffffff 0x0102040810204080ff00ff00ff00ff00) := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd
