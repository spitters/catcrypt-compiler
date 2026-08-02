/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.AdxChainFuse
import CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect

/-!
# `mpn_add_n` through the owned-RA ADX path, FRONT-GENERATED (#477 closed)

`MpnAdxLprog` supplies a *hand-authored* physical `Lprog` (raw `ADCX`
strings, pinned SysV registers, `mem.<base>.<off>` accesses) because the #477
note recorded that the `Com → Lprog` register allocator legalized only the
two-source binop alphabet, leaving the three-source flag-coupled `ADCX`/`ADOX`
carry chain unreachable from a source `Com`.

That gap is **closed**: the `Com → Lprog` RA (`JasminLprogExport.physBody` /
`physBodyWithStores`, driven by `Com.toLprogPhysAbi`) already legalizes the
three-source `ADCX`/`ADOX` ops. A three-source `Lopn [d] ADCX [a, s, cin]`
falls through `physBodyRmap`'s two-source arm to the general operand-remap arm
(**all** operands remapped, never truncated), the owned printer expands it to
the two-address `mov a,d; adcx s,d` shape and threads the explicit carry-in, and
`AdxChainFuse.fuseAdxChain` (a post-RA / pre-printer pass) collapses each
value-threaded `ADCX`/`ADCXHI`/`ADCX` limb triple into a live-flag `adcx` chain
— dropping the `setc`/`movzbq`/`bt` round-trip and, by construction, never
crossing a flag-clobbering instruction (its `findConsumer` scan stops at any
non-`MOV` op). The streaming `[base + 8·i]` memory operand is the printer's
`mem.<base>.<off>` form (`resolveName`), produced by the memref ABI
(`Com.toLprogPhysAbi` with `.memref n` pointer arguments). The BN254 `Fp2`
tower kernels (`Bn254TowerFrontEmit`) are the deployed end-to-end witness of the
same Com → RA → ADX-chain path (their `kernelAsm_selected` proves `adcx` reaches
the text).

This module is the **pure `mpn_add_n`** instance of that path: a straight-line
`n`-limb ripple-add expressed at the `LowCT` front (per-limb `bSltu` carry
synthesis, the `add2Prog` shape), selected by
`CarryChainSelect.translateDialectCarrySelect` into a `catCryptDialect` `Com`
whose carry-chain is `bvAddCarryLo`/`bvAddCarryHi` threading a single `sword 1`
carry limb-to-limb, lowered by `cryptoDialectToJasminCom` and rendered through
the owned RA (`toAsm`) — **no hand `Com`/`Lcmd`/`.s`**. The final carry-out
is architecturally dropped, so the kernel computes `out = (X + Y) mod 2^(64·n)`
(the `mpn_add_n` result words; the returned carry is a separate concern).

## What is verified here

* `add2FrontCom_isSome` / `add4FrontCom_isSome` — the pure-add bodies
  front-compile to a `catCryptDialect` `Com`.
* `add2Asm_shape` / `add4Asm_shape` — the RA-rendered `.s` carries the `adcx`
  chain (the selection reached the text), reads/writes the pointer registers,
  and emits no `UNHANDLED` sentinel.
* `add2_denote_spec` / `add4_denote_spec` — the front `Com` denotes the
  independent `Nat` spec `(X + Y) mod 2^(64·n)` on carry / no-carry / all-ones
  edge vectors.

The all-inputs byte-exact functional identity is the external GMP KAT vs
`__gmpn_add_n` in `bench/mpn_adx_owned_compare/`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (translateDialectCarrySelect)

/-! ## 1. Shared `SExpr` carry-chain pieces (the `add2Prog` `bSltu` synthesis) -/

/-- All-ones 64-bit literal. -/
def ones : Nat := 18446744073709551615

/-- Bitwise NOT via XOR with all-ones. -/
def notE (e : SExpr) : SExpr := .SXor e (.SLit ones)

/-- Bitwise OR via `(a ^ b) ^ (a & b)`. -/
def orE (a b : SExpr) : SExpr := .SXor (.SXor a b) (.SAnd a b)

/-- Named variable shorthand. -/
def v (n : String) : SExpr := .SVar n

/-- `dst := (x <u y)` as `0`/`1`, branch-free (the `MultiLimbKernel.add2Prog`
    `bSltu` synthesis).  Scratch slots `dst ++ "q"` / `dst ++ "r"`. -/
def ltuCmds (dst : String) (x y : SExpr) : List LowCT :=
  [ .RScalarSetExpr (dst ++ "q") (.SAnd (notE x) y),
    .RScalarSetExpr (dst ++ "r") (.SAnd (notE (.SXor x y)) (.SSub x y)),
    .RScalarSetExpr dst
      (.SShr (orE (.SVar (dst ++ "q")) (.SVar (dst ++ "r"))) (.SLit 63)) ]

/-- Sequence a `LowCT` list into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-! ## 2. The pure `n`-limb ripple-add body

`out[i] := a[i] + b[i] + carry`, carry threaded limb-to-limb, final carry-out
dropped (the `mpn_add_n` result-word contract). The per-limb carry is
synthesised branch-free with `ltuCmds`; the `CarryChainSelect` front recognises
the `addStart` / `addMid` / `addFin` windows and rewrites them to
`bvAddCarryLo`/`bvAddCarryHi`. -/

/-- Bind the constant cell indices `ix0 .. ix_{n-1}`. -/
def idxInit (n : Nat) : List LowCT :=
  (List.range n).map (fun i => (.RScalarSetExpr s!"ix{i}" (.SLit i) : LowCT))

/-- Load cells `0 .. n-1` of pointer `arr` into scalar slots `d0 .. d_{n-1}`.
    The `.TBytes (8*n)` located type encodes to `.memref n`, matching the
    pointer's bound memref so the dynamic-index memref-ABI arm fires. -/
def loadAll (arr d : String) (n : Nat) : List LowCT :=
  (List.range n).map (fun j =>
    (.RArrLoad ⟨s!"{d}{j}", .TU64⟩ ⟨arr, .TBytes (8 * n)⟩ s!"ix{j}" : LowCT))

/-- Store result slots `s0 .. s_{n-1}` into `out` cells `0 .. n-1`. -/
def storeAll (n : Nat) : List LowCT :=
  (List.range n).map (fun j =>
    (.RArrStore ⟨"out", .TBytes (8 * n)⟩ s!"ix{j}" ⟨s!"s{j}", .TU64⟩ : LowCT))

/-- The `n`-limb ripple ADD chain over the loaded `a`/`b` slots, result `s`.
    Limb 0 is the chain-start (`addStart`), limbs `1 .. n-2` are mid steps
    (`addMid`), limb `n-1` is the final step (`addFin`, carry-out dropped). -/
def addChain (n : Nat) : List LowCT :=
  [ .RScalarSetExpr "s0" (.SAdd (v "a0") (v "b0")) ]
  ++ ltuCmds "c0" (v "s0") (v "a0")
  ++ ((List.range (n - 2)).flatMap (fun k =>
      let j := k + 1
      [ (.RScalarSetExpr s!"t{j}" (.SAdd (v s!"a{j}") (v s!"b{j}")) : LowCT) ]
      ++ ltuCmds s!"ca{j}" (v s!"t{j}") (v s!"a{j}")
      ++ [ .RScalarSetExpr s!"s{j}" (.SAdd (v s!"t{j}") (v s!"c{j - 1}")) ]
      ++ ltuCmds s!"cb{j}" (v s!"s{j}") (v s!"t{j}")
      ++ [ .RScalarSetExpr s!"c{j}" (.SAdd (v s!"ca{j}") (v s!"cb{j}")) ]))
  ++ [ .RScalarSetExpr s!"t{n - 1}" (.SAdd (v s!"a{n - 1}") (v s!"b{n - 1}")),
       .RScalarSetExpr s!"s{n - 1}" (.SAdd (v s!"t{n - 1}") (v s!"c{n - 2}")) ]

/-- The full `mpn_add_n` body for `n` limbs: index init, load `x`/`y`, ripple
    add, store `out`. -/
def mpnAddBody (n : Nat) : LowCT :=
  seqAll (idxInit n ++ loadAll "x" "a" n ++ loadAll "y" "b" n
    ++ addChain n ++ storeAll n)

/-- Store result slots `e0 .. e_{n-1}` into `out` cells `0 .. n-1` (the sub
    chain's difference slots). -/
def storeAllE (n : Nat) : List LowCT :=
  (List.range n).map (fun j =>
    (.RArrStore ⟨"out", .TBytes (8 * n)⟩ s!"ix{j}" ⟨s!"e{j}", .TU64⟩ : LowCT))

/-- The `n`-limb ripple SUB borrow chain over the loaded `a`/`b` slots, result
    `e`, borrow chain `w` (the `bSltu` borrow synthesis — the same windows the
    `CarryChainSelect` front rewrites to `bvAddCarryLo`/`bvAddCarryHi` in the
    **complement-add** convention `x − y − borrow = x + ~y + (1 − borrow)`, so
    each step lowers to an `ADCX` op). Limb 0 is the chain-start (`subStart`),
    limbs `1 .. n-1` are mid steps (`subMid`); the final borrow `w_{n-1}` is
    architecturally dropped (the `mpn_sub_n` result-word contract). -/
def subChain (n : Nat) : List LowCT :=
  [ .RScalarSetExpr "e0" (.SSub (v "a0") (v "b0")) ]
  ++ ltuCmds "w0" (v "a0") (v "b0")
  ++ ((List.range (n - 1)).flatMap (fun k =>
      let j := k + 1
      [ (.RScalarSetExpr s!"g{j}" (.SSub (v s!"a{j}") (v s!"b{j}")) : LowCT) ]
      ++ ltuCmds s!"wa{j}" (v s!"a{j}") (v s!"b{j}")
      ++ [ .RScalarSetExpr s!"e{j}" (.SSub (v s!"g{j}") (v s!"w{j - 1}")) ]
      ++ ltuCmds s!"wb{j}" (v s!"g{j}") (v s!"w{j - 1}")
      ++ [ .RScalarSetExpr s!"w{j}" (.SAdd (v s!"wa{j}") (v s!"wb{j}")) ]))

/-- The full `mpn_sub_n` body for `n` limbs: index init, load `x`/`y`, ripple
    sub, store `out`. -/
def mpnSubBody (n : Nat) : LowCT :=
  seqAll (idxInit n ++ loadAll "x" "a" n ++ loadAll "y" "b" n
    ++ subChain n ++ storeAllE n)

/-! ## 3. Input context / `VarMap` (head-first `[y, x, out]`, `.memref n`)

`comToLfundef` reverses context↔argument order: `argName j` is context entry
`nArgs−1−j`. To land `out ← argName 0 ← RDI`, `x ← RSI`, `y ← RDX`, `out` is
bound deepest and the head-first context is `[y, x, out]`. -/

/-- Binary-kernel context, head-first `[y, x, out]` (all `.memref n`). -/
def inΓ (n : Nat) : Ctx := [.memref n, .memref n, .memref n]

/-- Binary-kernel `VarMap`: `out` deepest (→ RDI), then `x` (→ RSI), then `y`. -/
def inVM (n : Nat) : VarMap (inΓ n) :=
  ((VarMap.empty.bind (t := .memref n) "out").bind
    (t := .memref n) "x").bind (t := .memref n) "y"

/-! ## 4. Front-compile, lower, render -/

/-- Push an `n`-limb body through the carry-selecting front and cap with
    `ret out`. Shared by the add (`mpnAddBody`) and sub (`mpnSubBody`) kernels —
    both store their result into the `out` memref. -/
def frontComOf (n : Nat) (body : LowCT) :
    Option (Com catCryptDialect (inΓ n) (.memref n)) :=
  match translateDialectCarrySelect (inVM n) body with
  | some r =>
      match r.vm.lookup "out" with
      | some ⟨.memref m, vv⟩ =>
          if h : m = n then h ▸ r.cont (Com.ret (toVIRVar (h ▸ vv))) else none
      | _ => none
  | none => none

/-- Push the `n`-limb pure-add body through the front. -/
def frontCom (n : Nat) : Option (Com catCryptDialect (inΓ n) (.memref n)) :=
  frontComOf n (mpnAddBody n)

/-- Push the `n`-limb pure-sub body through the front. -/
def subFrontCom (n : Nat) : Option (Com catCryptDialect (inΓ n) (.memref n)) :=
  frontComOf n (mpnSubBody n)

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Com.toLprogPhysAbi Lprog)

/-- Lower a front dialect program to `Com jasminDialect` and render an owned
    `Lprog` under the SysV pointer ABI, then fuse the ADX carry chains and print
    AT&T. `none` if the front / lowering declines. -/
def toAsmOf (name : String) (abiArgs : List String) {n : Nat}
    (fc : Option (Com catCryptDialect (inΓ n) (.memref n))) : Option String :=
  match fc with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc =>
          some (renderLprogAtt
            (CatCrypt.Crypto.SecureCompilation.X86Backend.AdxChainFuse.fuseAdxChain
              (Com.toLprogPhysAbi jc name
                (fun _ => none) (fun _ => none) (fun _ => none) []
                (abiArgs := abiArgs) (abiTyin := abiArgs.map (fun _ => 64))
                (residence := none) (abiW := 0)
                (forceLivePin := true))))
      | none => none
  | none => none

/-- The owned AT&T `.s` for the pure `n`-limb ADX `mpn_add_n`
    (RDI = out, RSI = x, RDX = y). -/
def toAsm (n : Nat) (name : String) (abiArgs : List String) : Option String :=
  toAsmOf name abiArgs (frontCom n)

/-- The owned AT&T `.s` for the pure `n`-limb `mpn_add_n`. -/
def addAsm (n : Nat) : Option String :=
  toAsm n s!"mpn_add_n_adx_front_{n}" ["RDI", "RSI", "RDX"]

/-- The owned AT&T `.s` for the pure `n`-limb `mpn_sub_n` (complement-add ADX
    chain: `x − y = x + ~y + 1`). -/
def subAsm (n : Nat) : Option String :=
  toAsmOf s!"mpn_sub_n_adx_front_{n}" ["RDI", "RSI", "RDX"] (subFrontCom n)

/-! ## 5. Witnesses at 2 and 4 limbs -/

def add2FrontCom : Option (Com catCryptDialect (inΓ 2) (.memref 2)) := frontCom 2
def add4FrontCom : Option (Com catCryptDialect (inΓ 4) (.memref 4)) := frontCom 4
def sub2FrontCom : Option (Com catCryptDialect (inΓ 2) (.memref 2)) := subFrontCom 2
def sub4FrontCom : Option (Com catCryptDialect (inΓ 4) (.memref 4)) := subFrontCom 4

/-- The 2-limb and 4-limb pure-add bodies front-compile. -/
theorem add2FrontCom_isSome : add2FrontCom.isSome := by native_decide
theorem add4FrontCom_isSome : add4FrontCom.isSome := by native_decide

/-- The 2-limb and 4-limb pure-sub bodies front-compile. -/
theorem sub2FrontCom_isSome : sub2FrontCom.isSome := by native_decide
theorem sub4FrontCom_isSome : sub4FrontCom.isSome := by native_decide

/-- The RA-rendered 2-limb `.s` is a valid ADX chain: the `adcxq` carry chain
    reached the text (the front selection fired all the way through the RA),
    the streaming SIB memory operands `(%r14, %idx, 8)` are present (the memref
    ABI's dynamic-index accesses), and no `UNHANDLED` sentinel was emitted (every
    op — including the three-source `ADCX` — rendered to a real line). -/
theorem add2Asm_shape :
    strContains ((addAsm 2).getD "") "adcxq" = true
    ∧ strContains ((addAsm 2).getD "") "(%r14," = true
    ∧ strContains ((addAsm 2).getD "") "UNHANDLED" = false := by native_decide

/-- The RA-rendered 4-limb `.s` is a valid ADX chain (as `add2Asm_shape`). -/
theorem add4Asm_shape :
    strContains ((addAsm 4).getD "") "adcxq" = true
    ∧ strContains ((addAsm 4).getD "") "(%r14," = true
    ∧ strContains ((addAsm 4).getD "") "UNHANDLED" = false := by native_decide

/- The RA-rendered 2-limb `mpn_sub_n` `.s` is a valid complement-add ADX chain:
    the `adcxq` chain reached the text (the front rewrote the borrow windows to
    `x + ~y + carry` in the complement-add convention), the streaming SIB
    operands are present, and no `UNHANDLED` sentinel. -/
#guard (strContains ((subAsm 2).getD "") "adcxq")
    && (strContains ((subAsm 2).getD "") "(%r14,")
    && !(strContains ((subAsm 2).getD "") "UNHANDLED")

/- The RA-rendered 4-limb `mpn_sub_n` `.s` is a valid complement-add ADX chain. -/
#guard (strContains ((subAsm 4).getD "") "adcxq")
    && (strContains ((subAsm 4).getD "") "(%r14,")
    && !(strContains ((subAsm 4).getD "") "UNHANDLED")

/-! ## 6. `denote = spec` vs the independent `Nat` `mod 2^(64·n)` spec -/

/-- Recombine `n` little-endian 64-bit words to a `Nat`. -/
def valN (ws : List Nat) (n : Nat) : Nat :=
  ((List.range n).map (fun i => ws[i]! * 2 ^ (64 * i))).sum

/-- Split a `Nat` into `n` little-endian 64-bit limbs. -/
def limbsN (x : Nat) (n : Nat) : List Nat :=
  (List.range n).map (fun i => x / 2 ^ (64 * i) % 2 ^ 64)

/-- Independent spec of the pure `n`-limb add: `(X + Y) mod 2^(64·n)`. -/
def addSpecN (x y : List Nat) (n : Nat) : List Nat :=
  limbsN ((valN x n + valN y n) % 2 ^ (64 * n)) n

/-- Independent spec of the pure `n`-limb sub: `(X − Y) mod 2^(64·n)` with the
    two's-complement borrow/wrap `X + 2^(64·n) − Y` (matches GMP `__gmpn_sub_n`'s
    result words; the returned borrow is dropped). -/
def subSpecN (x y : List Nat) (n : Nat) : List Nat :=
  limbsN ((valN x n + 2 ^ (64 * n) - valN y n) % 2 ^ (64 * n)) n

/-- An `n`-cell memref valuation from a word list. -/
def vecOf (n : Nat) (ws : List Nat) : Fin n → BitVec 64 :=
  fun i => BitVec.ofNat 64 ws[i.val]!

/-- Binary-kernel valuation, head-first `[y, x, out]` (matches `inΓ n`). -/
def encodeVal (n : Nat) (xv yv : Fin n → BitVec 64) :
    @Ctxt.Valuation catCryptDialect _ (inΓ n) :=
  .cons yv (.cons xv (.cons (fun _ => (0 : BitVec 64)) .nil))

/-- Denote an `n`-limb front kernel and read out all `n` cells. -/
def denoteCells (n : Nat) (com : Option (Com catCryptDialect (inΓ n) (.memref n)))
    (x y : List Nat) : Option (List Nat) :=
  com.map (fun c =>
    (List.finRange n).map (fun i =>
      (c.denote (encodeVal n (vecOf n x) (vecOf n y)) i).toNat))

/-- Add sample pairs: no-carry, ripple-carry, all-ones (full-wrap), zero. -/
def samples : List (List Nat × List Nat) :=
  [ ([7, 9], [11, 13]),
    ([ones, 1], [1, 0]),
    ([ones, ones], [ones, ones]),
    ([0, 0], [0, 0]),
    ([ones, ones, ones, ones], [1, 0, 0, 0]),
    ([1, 2, 3, 4], [ones, ones, ones, 0]) ]

/-- **2-limb `mpn_add_n` denote = independent spec** on the 2-word samples. -/
theorem add2_denote_spec :
    [([7, 9], [11, 13]), ([ones, 1], [1, 0]),
     ([ones, ones], [ones, ones]), ([0, 0], [0, 0])].all (fun (x, y) =>
      denoteCells 2 add2FrontCom x y == some (addSpecN x y 2)) = true := by
  native_decide

/-- **4-limb `mpn_add_n` denote = independent spec** on the 4-word samples. -/
theorem add4_denote_spec :
    [([ones, ones, ones, ones], [1, 0, 0, 0]),
     ([1, 2, 3, 4], [ones, ones, ones, 0]),
     ([7, 9, 11, 13], [1, 2, 3, 4]),
     ([0, 0, 0, 0], [0, 0, 0, 0])].all (fun (x, y) =>
      denoteCells 4 add4FrontCom x y == some (addSpecN x y 4)) = true := by
  native_decide

/-- **2-limb `mpn_sub_n` denote = independent spec** (`(X−Y) mod 2^128`, with
    the borrow/wrap) on no-borrow / full-borrow / zero edges. -/
theorem sub2_denote_spec :
    [([13, 11], [9, 7]), ([1, 0], [ones, 1]),
     ([0, 0], [1, 0]), ([0, 0], [0, 0])].all (fun (x, y) =>
      denoteCells 2 sub2FrontCom x y == some (subSpecN x y 2)) = true := by
  native_decide

/-- **4-limb `mpn_sub_n` denote = independent spec** (`(X−Y) mod 2^256`, with
    the borrow/wrap) on borrow-ripple / full-wrap / zero edges. -/
theorem sub4_denote_spec :
    [([1, 0, 0, 0], [ones, ones, ones, ones]),
     ([5, 5, 5, 5], [7, 0, 0, 0]),
     ([0, 0, 0, 0], [0, 0, 0, 1]),
     ([0, 0, 0, 0], [0, 0, 0, 0])].all (fun (x, y) =>
      denoteCells 4 sub4FrontCom x y == some (subSpecN x y 4)) = true := by
  native_decide

/-! ## 7. Emit driver -/

/-- Write the front-generated owned-RA ADX `.s` for `mpn_add_n` / `mpn_sub_n` at
    `n = 4, 8, 16, 32` into the bench harness directory. FRONT-GENERATED (no
    hand `Com`/`Lcmd`/`.s`; the #477 RA gap is closed — both the add carry chain
    and the sub complement-add borrow chain lower to `ADCX` through the RA). -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/mpn_adx_owned_compare/gen_com"
  for n in [4, 8, 16, 32] do
    match addAsm n with
    | some s =>
        IO.FS.writeFile s!"bench/mpn_adx_owned_compare/gen_com/mpn_add_n_adx_front_{n}.s" s
    | none =>
        throw (IO.userError s!"front-compile of mpn_add_n at n={n} declined")
    match subAsm n with
    | some s =>
        IO.FS.writeFile s!"bench/mpn_adx_owned_compare/gen_com/mpn_sub_n_adx_front_{n}.s" s
    | none =>
        throw (IO.userError s!"front-compile of mpn_sub_n at n={n} declined")
  IO.println "wrote FRONT-generated owned-RA ADX mpn_add_n/mpn_sub_n .s at n=4,8,16,32 (Com→RA→ADX, no jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddFrontEmit
