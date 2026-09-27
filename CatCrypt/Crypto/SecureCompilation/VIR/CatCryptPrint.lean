/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Print
public import CatCrypt.Crypto.SecureCompilation.VIR.Print
public meta import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public meta import CatCrypt.Crypto.SecureCompilation.VIR.CryptoToVIR
public import CatCrypt.Crypto.SecureCompilation.VIR.CryptoToVIR

/-!
# DialectPrint instance for catCryptDialect

Renders each `CatCryptOp` binding as MLIR generic-syntax operations of the
upstream `arith`, `memref`, `scf`, `func` and `llvm` dialects whose meaning is the
op's denotation `catCryptDenote`. Where no single upstream operation has that
meaning, the binding is a short sequence of operations (`printCatCryptParts`);
the other ops print as one line (`Expr.printOneLine`).

## Op mapping

| CatCryptOp | MLIR |
|---|---|
| `constBit`, `constUnit`, `bvConst`, `vconst128` | `arith.constant` |
| `xor`/`and`/`or`, `bvXor`/`bvAnd`/`bvOr`, `bvAdd`/`bvSub`/`bvMul` | `arith.xori`/`andi`/`ori`/`addi`/`subi`/`muli` |
| `not`, `bvNot w` | `arith.xori` with the all-ones constant |
| `andn w` | `arith.xori` with the all-ones constant, then `arith.andi` |
| `eqBit`, `bvEq w` | `arith.cmpi eq` |
| `bvShiftL`/`bvShiftR w k`, `vpslldqC`/`vpsrldqC n` | `arith.shli`/`shrui` by a constant; the constant `0` when the amount is `≥ w` |
| `bvShiftRA w k` | `arith.shrsi` by `min k (w - 1)` |
| `bvShiftLV`/`bvShiftRV w` | `arith.shli`/`shrui`, then `arith.select` of `0` when the amount is `≥ w` |
| `bvRor`/`bvRol w n` | `llvm.intr.fshr`/`fshl (a, a, n mod w)` |
| `bvMulHi w` | `arith.mului_extended`, high result |
| `bvAddCarryLo`/`bvAddCarryHi w` | `arith.extui` of the carry-in and two `arith.addui_extended`; the sum, or `arith.ori` of the two overflow bits |
| `bvAdd64 w`, `bvAdc w` | the `arith.addui_extended` chain, the carry as `arith.extui`, packed into `!llvm.struct<(iw, iw)>` |
| `ite t` | `arith.select` |
| `bitToSword n` | `arith.extsi` (`arith.ori %c, %c` when `n = 1`) |
| `mkPair`, `inl`, `inr` | `llvm.mlir.undef` and `llvm.insertvalue`; a sum is `!llvm.struct<(i1, a, b)>` with tag `0` for `inl` |
| `fst`, `snd` | `llvm.extractvalue` |
| `memrefZero n` | `memref.alloc` and an `scf.for` storing `0` |
| `memrefSet`, `memrefSetDyn`, `memrefWSetDyn` | `memref.alloc` of a fresh buffer, `memref.copy`, `memref.store` |
| `memrefGet`, `memrefGetDyn`, `memrefWGetDyn` | `memref.load`; a runtime index is reduced by `arith.remui` modulo `n` |
| `memrefGetDyn128 n` | two `memref.load`s at `2k mod n` and `2k + 1 mod n`, packed into `i128` |
| `extCall` | `func.call` |

A `memref n` value has value semantics in the denotation. The printed form keeps
the `memref` type, which the extern signatures and the benchmark ABI use, and
every update writes a fresh buffer, so no printed operation writes to a buffer
that another binding reads. A runtime-index op on an empty memref prints its
denotation: the constant `0`, or an empty buffer.

The ops without an upstream counterpart print as unregistered `crypto.*` ops:
`sampleBit`, `sampleBv` (sampling) and the x86 SIMD instructions `vsimd`,
`vpshufdC`, `vaeskeygenC`, `vsha256rnds2`, `vsha256msg1`, `vsha256msg2`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.CatCryptPrint

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ## Type printer -/

/-- Print a `CryptoTy` as a textual MLIR type. A pair is the LLVM struct of its
    components; a sum is the LLVM struct of an `i1` tag and both components. -/
def printCryptoTy : CryptoTy → String
  | .bit => "i1"
  | .unit => "i1"   -- erased
  | .sword n => "i" ++ toString n
  | .memref n => "memref<" ++ toString n ++ "xi64>"
  | .memrefW w n => "memref<" ++ toString n ++ "xi" ++ toString w ++ ">"
  | .pair a b => "!llvm.struct<(" ++ printCryptoTy a ++ ", " ++ printCryptoTy b ++ ")>"
  | .sum a b =>
      "!llvm.struct<(i1, " ++ printCryptoTy a ++ ", " ++ printCryptoTy b ++ ")>"

/-! ## Op printer

`printCatCryptOp` is the quoted name of the principal MLIR operation of an op's
rendering; `printCatCryptParts` gives the text before and after that name when the
rendering is not the one-line form. -/

/-- The quoted name of the principal MLIR operation of an op's rendering. -/
def printCatCryptOp : CatCryptOp → String
  | .constBit _ | .constUnit | .bvConst _ _ | .vconst128 _ => "\"arith.constant\""
  | .xor | .bvXor _ | .not | .bvNot _ => "\"arith.xori\""
  | .and | .bvAnd _ | .andn _ => "\"arith.andi\""
  | .or | .bvOr _ => "\"arith.ori\""
  | .eqBit | .bvEq _ => "\"arith.cmpi\""
  | .bvAdd _ => "\"arith.addi\""
  | .bvSub _ => "\"arith.subi\""
  | .bvMul _ => "\"arith.muli\""
  | .bvShiftL w k => if k < w then "\"arith.shli\"" else "\"arith.constant\""
  | .bvShiftR w k => if k < w then "\"arith.shrui\"" else "\"arith.constant\""
  | .vpslldqC n => if n * 8 < 128 then "\"arith.shli\"" else "\"arith.constant\""
  | .vpsrldqC n => if n * 8 < 128 then "\"arith.shrui\"" else "\"arith.constant\""
  | .bvShiftLV _ => "\"arith.shli\""
  | .bvShiftRV _ => "\"arith.shrui\""
  | .bvShiftRA _ _ => "\"arith.shrsi\""
  | .bvRor _ _ => "\"llvm.intr.fshr\""
  | .bvRol _ _ => "\"llvm.intr.fshl\""
  | .bvMulHi _ => "\"arith.mului_extended\""
  | .bvAddCarryLo _ | .bvAddCarryHi _ | .bvAdd64 _ | .bvAdc _ =>
      "\"arith.addui_extended\""
  | .ite _ => "\"arith.select\""
  | .bitToSword n => if n = 1 then "\"arith.ori\"" else "\"arith.extsi\""
  | .mkPair _ _ | .inl _ _ | .inr _ _ => "\"llvm.insertvalue\""
  | .fst _ _ | .snd _ _ => "\"llvm.extractvalue\""
  | .memrefZero _ => "\"memref.alloc\""
  | .memrefSet _ _ => "\"memref.store\""
  | .memrefSetDyn n | .memrefWSetDyn _ n =>
      if n = 0 then "\"memref.alloc\"" else "\"memref.store\""
  | .memrefGet _ _ => "\"memref.load\""
  | .memrefGetDyn n | .memrefGetDyn128 n | .memrefWGetDyn _ n =>
      if n = 0 then "\"arith.constant\"" else "\"memref.load\""
  | .extCall _ _ _ => "\"func.call\""
  | .sampleBit => "\"crypto.sample_bit\""
  | .sampleBv _ => "\"crypto.sample_bv\""
  | .vsimd _ => "\"crypto.vsimd\""
  | .vpshufdC _ => "\"crypto.vpshufd\""
  | .vaeskeygenC _ => "\"crypto.vaeskeygenassist\""
  | .vsha256rnds2 => "\"crypto.sha256rnds2\""
  | .vsha256msg1 => "\"crypto.sha256msg1\""
  | .vsha256msg2 => "\"crypto.sha256msg2\""

/-- Inline attribute dictionary (with leading space) of the one-line form, or the
    empty string. -/
def printCatCryptAttrs : CatCryptOp → String
  | .constBit false => " {value = 0 : i1}"
  | .constBit true  => " {value = 1 : i1}"
  | .constUnit      => " {value = 0 : i1}"
  | .bvConst w v    =>
      " {value = " ++ toString v.toNat ++ " : i" ++ toString w ++ "}"
  | .vconst128 v    => " {value = " ++ toString v.toNat ++ " : i128}"
  | .eqBit | .bvEq _ => " {predicate = 0 : i64}"
  | .fst _ _ => " {position = array<i64: 0>}"
  | .snd _ _ => " {position = array<i64: 1>}"
  | .extCall name _ _ => " {callee = @" ++ name ++ "}"
  | .vpshufdC imm => " {imm = " ++ toString imm ++ " : i64}"
  | .vaeskeygenC rcon => " {rcon = " ++ toString rcon.toNat ++ " : i8}"
  | _ => ""

/-! ## Line builders -/

/-- The integer type `i<w>`. -/
def intTy (w : Nat) : String := "i" ++ toString w

/-- The SSA use `%x` of the name `x`. -/
def ssa (x : String) : String := "%" ++ x

/-- The result list `(T₁, T₂)` of a two-result operation. -/
def resPair (t₁ t₂ : String) : String := "(" ++ t₁ ++ ", " ++ t₂ ++ ")"

/-- The text of one MLIR operation before and after its quoted name: the indentation
    and the result list `res` (empty for an operation with no results), then the
    operands, attributes and type signature. -/
def opParts (res : String) (args : List String) (attrs : String)
    (argTys : List String) (resTy : String) : String × String :=
  ("  " ++ (if res.isEmpty then "" else res ++ " = "),
   "(" ++ ", ".intercalate (args.map ssa) ++ ")" ++ attrs ++ " : (" ++
     ", ".intercalate argTys ++ ") -> " ++ resTy)

/-- One MLIR operation line, without a trailing newline. -/
def opLine (res op : String) (args : List String) (attrs : String)
    (argTys : List String) (resTy : String) : String :=
  let p := opParts res args attrs argTys resTy
  p.1 ++ op ++ p.2

/-- The line `%x = "arith.constant"() {value = c : ty} : () -> ty`. -/
def constLine (x c ty : String) : String :=
  opLine (ssa x) "\"arith.constant\"" [] (" {value = " ++ c ++ " : " ++ ty ++ "}") [] ty

/-- The rendering whose principal operation `p` is preceded by the lines `pre` and
    followed by the lines `post`. -/
def withLines (pre : List String) (p : String × String) (post : List String) :
    String × String :=
  (String.join (pre.map (· ++ "\n")) ++ p.1, p.2 ++ String.join (post.map ("\n" ++ ·)))

/-- The zero extension of the `i1` value `%src` to `i<w>` as `%dst`: its lines and the
    name of the extended value, which is `src` itself when `w = 1`. -/
def extuiLines (w : Nat) (src dst : String) : List String × String :=
  if w = 1 then ([], src)
  else ([opLine (ssa dst) "\"arith.extui\"" [src] "" ["i1"] (intTy w)], dst)

/-- The all-ones value of `i<w>` as a decimal literal. -/
def allOnesLit (w : Nat) : String := toString (2 ^ w - 1)

/-- The attribute of a `memref.alloc` without dynamic sizes or symbols. -/
def allocAttr : String := " {operandSegmentSizes = array<i32: 0, 0>}"

/-- The shift of `%a : i<w>` by the constant `k` as `%nm`: the shift by `k` when
    `k < w`, the constant `0` otherwise. -/
def shiftImmParts (w k : Nat) (a nm : String) : String × String :=
  if k < w then
    withLines [constLine ("k" ++ nm) (toString k) (intTy w)]
      (opParts (ssa nm) [a, "k" ++ nm] "" [intTy w, intTy w] (intTy w)) []
  else opParts (ssa nm) [] (" {value = 0 : " ++ intTy w ++ "}") [] (intTy w)

/-- The shift of `%a : i<w>` by the `i<w>` value `%b` as `%nm`: the shift, replaced
    by `0` when `b ≥ w`. -/
def shiftVarParts (w : Nat) (a b nm : String) : String × String :=
  let t := intTy w
  withLines
    [constLine ("w" ++ nm) (toString w) t,
     opLine (ssa ("g" ++ nm)) "\"arith.cmpi\"" [b, "w" ++ nm] " {predicate = 9 : i64}"
       [t, t] "i1",
     constLine ("z" ++ nm) "0" t]
    (opParts (ssa ("s" ++ nm)) [a, b] "" [t, t] t)
    [opLine (ssa nm) "\"arith.select\"" ["g" ++ nm, "z" ++ nm, "s" ++ nm] ""
       ["i1", t, t] t]

/-- The lines reducing the `i64` index `%k` modulo `n` and converting it to the
    `index` value `%x<nm>`. -/
def dynIndexLines (n : Nat) (k nm : String) : List String :=
  [constLine ("n" ++ nm) (toString n) "i64",
   opLine (ssa ("r" ++ nm)) "\"arith.remui\"" [k, "n" ++ nm] "" ["i64", "i64"] "i64",
   opLine (ssa ("x" ++ nm)) "\"arith.index_castui\"" ["r" ++ nm] "" ["i64"] "index"]

/-- The update of cell `k mod n` of the buffer `%arr : m` (cells `e`) to `%v`, as the
    fresh buffer `%nm`; an empty buffer when `n = 0`. -/
def setDynParts (m e : String) (n : Nat) (arr k v nm : String) : String × String :=
  if n = 0 then opParts (ssa nm) [] allocAttr [] m
  else
    withLines
      (dynIndexLines n k nm ++
        [opLine (ssa nm) "\"memref.alloc\"" [] allocAttr [] m,
         opLine "" "\"memref.copy\"" [arr, nm] "" [m, m] "()"])
      (opParts "" [v, nm, "x" ++ nm] "" [e, m, "index"] "()") []

/-- The read of cell `k mod n` of the buffer `%arr : m` (cells `e`) as `%nm`; the
    constant `0` when `n = 0`. -/
def getDynParts (m e : String) (n : Nat) (arr k nm : String) : String × String :=
  if n = 0 then opParts (ssa nm) [] (" {value = 0 : " ++ e ++ "}") [] e
  else withLines (dynIndexLines n k nm) (opParts (ssa nm) [arr, "x" ++ nm] "" [m, "index"] e) []

/-- The lines storing `0` into every cell of the fresh buffer `%nm : m` of `n` cells
    of type `e`. -/
def zeroFillLines (m e : String) (n : Nat) (nm : String) : List String :=
  if n = 0 then []
  else
    [constLine ("z" ++ nm) "0" e,
     constLine ("lb" ++ nm) "0" "index",
     constLine ("ub" ++ nm) (toString n) "index",
     constLine ("st" ++ nm) "1" "index",
     "  \"scf.for\"(%lb" ++ nm ++ ", %ub" ++ nm ++ ", %st" ++ nm ++ ") ({",
     "  ^bb0(%iv" ++ nm ++ ": index):",
     "  " ++ opLine "" "\"memref.store\"" ["z" ++ nm, nm, "iv" ++ nm] "" [e, m, "index"] "()",
     "    \"scf.yield\"() : () -> ()",
     "  }) : (index, index, index) -> ()"]

/-- The lines building the struct `%nm : s` whose fields at positions `i` and `j` are
    `%f : tf` and `%g : tg`, from `llvm.mlir.undef`. -/
def structLines (s : String) (i : Nat) (f tf : String) (j : Nat) (g tg nm : String) :
    List String :=
  [opLine (ssa ("u" ++ nm)) "\"llvm.mlir.undef\"" [] "" [] s,
   opLine (ssa ("v" ++ nm)) "\"llvm.insertvalue\"" ["u" ++ nm, f]
     (" {position = array<i64: " ++ toString i ++ ">}") [s, tf] s,
   opLine (ssa nm) "\"llvm.insertvalue\"" ["v" ++ nm, g]
     (" {position = array<i64: " ++ toString j ++ ">}") [s, tg] s]

/-- The rendering of an op as MLIR lines, split around the name of its principal
    operation `printCatCryptOp op`, from the operand names `as` and the result name
    `nm`; `none` selects the one-line form. -/
def printCatCryptParts (op : CatCryptOp) (as : List String) (nm : String) :
    Option (String × String) :=
  let a := as.getD 0 ""
  let b := as.getD 1 ""
  let c := as.getD 2 ""
  let r := ssa nm
  let x (p : String) : String := p ++ nm
  match op with
  | .not => some <| withLines [constLine (x "m") "1" "i1"]
      (opParts r [a, x "m"] "" ["i1", "i1"] "i1") []
  | .bvNot w => some <| withLines [constLine (x "m") (allOnesLit w) (intTy w)]
      (opParts r [a, x "m"] "" [intTy w, intTy w] (intTy w)) []
  | .andn w => some <| withLines
      [constLine (x "m") (allOnesLit w) (intTy w),
       opLine (ssa (x "n")) "\"arith.xori\"" [a, x "m"] "" [intTy w, intTy w] (intTy w)]
      (opParts r [x "n", b] "" [intTy w, intTy w] (intTy w)) []
  | .bvShiftL w k | .bvShiftR w k => some (shiftImmParts w k a nm)
  | .vpslldqC n | .vpsrldqC n => some (shiftImmParts 128 (n * 8) a nm)
  | .bvShiftRA w k => some <| withLines [constLine (x "k") (toString (min k (w - 1))) (intTy w)]
      (opParts r [a, x "k"] "" [intTy w, intTy w] (intTy w)) []
  | .bvShiftLV w | .bvShiftRV w => some (shiftVarParts w a b nm)
  | .bvRor w n | .bvRol w n => some <| withLines [constLine (x "k") (toString (n % w)) (intTy w)]
      (opParts r [a, a, x "k"] "" [intTy w, intTy w, intTy w] (intTy w)) []
  | .bvMulHi w => some <|
      opParts (ssa (x "l") ++ ", " ++ r) [a, b] "" [intTy w, intTy w] (resPair (intTy w) (intTy w))
  | .bvAddCarryLo w =>
      let (el, cz) := extuiLines w c (x "cz")
      some <| withLines el
        (opParts (ssa (x "s") ++ ", " ++ ssa (x "o")) [a, b] "" [intTy w, intTy w]
          (resPair (intTy w) "i1"))
        [opLine (r ++ ", " ++ ssa (x "p")) "\"arith.addui_extended\"" [x "s", cz] ""
          [intTy w, intTy w] (resPair (intTy w) "i1")]
  | .bvAddCarryHi w =>
      let (el, cz) := extuiLines w c (x "cz")
      some <| withLines el
        (opParts (ssa (x "s") ++ ", " ++ ssa (x "o")) [a, b] "" [intTy w, intTy w]
          (resPair (intTy w) "i1"))
        [opLine (ssa (x "t") ++ ", " ++ ssa (x "p")) "\"arith.addui_extended\"" [x "s", cz] ""
          [intTy w, intTy w] (resPair (intTy w) "i1"),
         opLine r "\"arith.ori\"" [x "o", x "p"] "" ["i1", "i1"] "i1"]
  | .bvAdd64 w =>
      let s := printCryptoTy (.pair (.sword w) (.sword w))
      let (el, cc) := extuiLines w (x "o") (x "c")
      some <| withLines []
        (opParts (ssa (x "s") ++ ", " ++ ssa (x "o")) [a, b] "" [intTy w, intTy w]
          (resPair (intTy w) "i1"))
        (el ++ structLines s 0 cc (intTy w) 1 (x "s") (intTy w) nm)
  | .bvAdc w =>
      let s := printCryptoTy (.pair (.sword w) (.sword w))
      let (el₁, cz) := extuiLines w (x "cb") (x "cz")
      let (el₂, cc) := extuiLines w (x "q") (x "c")
      some <| withLines
        ([constLine (x "zc") "0" (intTy w),
          opLine (ssa (x "cb")) "\"arith.cmpi\"" [c, x "zc"] " {predicate = 1 : i64}"
            [intTy w, intTy w] "i1"] ++ el₁)
        (opParts (ssa (x "s") ++ ", " ++ ssa (x "o")) [a, b] "" [intTy w, intTy w]
          (resPair (intTy w) "i1"))
        ([opLine (ssa (x "t") ++ ", " ++ ssa (x "p")) "\"arith.addui_extended\"" [x "s", cz] ""
            [intTy w, intTy w] (resPair (intTy w) "i1"),
          opLine (ssa (x "q")) "\"arith.ori\"" [x "o", x "p"] "" ["i1", "i1"] "i1"] ++ el₂ ++
          structLines s 0 cc (intTy w) 1 (x "t") (intTy w) nm)
  | .bitToSword n => if n = 1 then some (opParts r [a, a] "" ["i1", "i1"] "i1") else none
  | .mkPair ta tb =>
      let s := printCryptoTy (.pair ta tb)
      some <| withLines
        [opLine (ssa (x "u")) "\"llvm.mlir.undef\"" [] "" [] s,
         opLine (ssa (x "v")) "\"llvm.insertvalue\"" [x "u", a] " {position = array<i64: 0>}"
           [s, printCryptoTy ta] s]
        (opParts r [x "v", b] " {position = array<i64: 1>}" [s, printCryptoTy tb] s) []
  | .inl ta tb | .inr ta tb =>
      let s := printCryptoTy (.sum ta tb)
      let (tag, pos, ty) := match op with
        | .inr _ _ => ("1", "2", printCryptoTy tb)
        | _ => ("0", "1", printCryptoTy ta)
      some <| withLines
        [opLine (ssa (x "u")) "\"llvm.mlir.undef\"" [] "" [] s,
         constLine (x "g") tag "i1",
         opLine (ssa (x "v")) "\"llvm.insertvalue\"" [x "u", x "g"]
           " {position = array<i64: 0>}" [s, "i1"] s]
        (opParts r [x "v", a] (" {position = array<i64: " ++ pos ++ ">}") [s, ty] s) []
  | .memrefZero n =>
      let m := printCryptoTy (.memref n)
      some <| withLines [] (opParts r [] allocAttr [] m) (zeroFillLines m "i64" n nm)
  | .memrefSet n i =>
      let m := printCryptoTy (.memref n)
      some <| withLines
        [opLine r "\"memref.alloc\"" [] allocAttr [] m,
         opLine "" "\"memref.copy\"" [a, nm] "" [m, m] "()",
         constLine (x "i") (toString i.val) "index"]
        (opParts "" [b, nm, x "i"] "" ["i64", m, "index"] "()") []
  | .memrefGet n i =>
      some <| withLines [constLine (x "i") (toString i.val) "index"]
        (opParts r [a, x "i"] "" [printCryptoTy (.memref n), "index"] "i64") []
  | .memrefSetDyn n => some (setDynParts (printCryptoTy (.memref n)) "i64" n a b c nm)
  | .memrefWSetDyn w n =>
      some (setDynParts (printCryptoTy (.memrefW w n)) (intTy w) n a b c nm)
  | .memrefGetDyn n => some (getDynParts (printCryptoTy (.memref n)) "i64" n a b nm)
  | .memrefWGetDyn w n =>
      some (getDynParts (printCryptoTy (.memrefW w n)) (intTy w) n a b nm)
  | .memrefGetDyn128 n =>
      let m := printCryptoTy (.memref n)
      let t := "i65"
      if n = 0 then some (opParts r [] " {value = 0 : i128}" [] "i128")
      else some <| withLines
        [opLine (ssa (x "e")) "\"arith.extui\"" [b] "" ["i64"] t,
         constLine (x "one") "1" t,
         opLine (ssa (x "lo")) "\"arith.shli\"" [x "e", x "one"] "" [t, t] t,
         opLine (ssa (x "hi")) "\"arith.ori\"" [x "lo", x "one"] "" [t, t] t,
         constLine (x "n") (toString n) t,
         opLine (ssa (x "lr")) "\"arith.remui\"" [x "lo", x "n"] "" [t, t] t,
         opLine (ssa (x "hr")) "\"arith.remui\"" [x "hi", x "n"] "" [t, t] t,
         opLine (ssa (x "lx")) "\"arith.index_castui\"" [x "lr"] "" [t] "index",
         opLine (ssa (x "hx")) "\"arith.index_castui\"" [x "hr"] "" [t] "index"]
        (opParts (ssa (x "lv")) [a, x "lx"] "" [m, "index"] "i64")
        [opLine (ssa (x "hv")) "\"memref.load\"" [a, x "hx"] "" [m, "index"] "i64",
         opLine (ssa (x "lw")) "\"arith.extui\"" [x "lv"] "" ["i64"] "i128",
         opLine (ssa (x "hw")) "\"arith.extui\"" [x "hv"] "" ["i64"] "i128",
         constLine (x "sh") "64" "i128",
         opLine (ssa (x "hs")) "\"arith.shli\"" [x "hw", x "sh"] "" ["i128", "i128"] "i128",
         opLine r "\"arith.ori\"" [x "lw", x "hs"] "" ["i128", "i128"] "i128"]
  | _ => none

instance : DialectPrint catCryptDialect where
  printOp := printCatCryptOp
  printAttrs := printCatCryptAttrs
  printTy := printCryptoTy
  printCustom? op as nm :=
    (printCatCryptParts op as nm).map fun p => p.1 ++ printCatCryptOp op ++ p.2

/-! ## Smoke program: add_3_4 -/

namespace Test

open CryptoSSA

/-- `let x = 3 : sword 8; let y = 4 : sword 8; let z = x + y; ret z`, authored
    directly as a `Com catCryptDialect`; the print/opCount smoke tests in
    `CatCryptPrintCorrect` use it. -/
def add_3_4_vir : Com catCryptDialect [] (.sword 8) :=
  .var { op := .bvConst 8 (3 : BitVec 8), retTy_eq := rfl, args := .nil }
    (.var { op := .bvConst 8 (4 : BitVec 8), retTy_eq := rfl, args := .nil }
      (.var { op := .bvAdd 8, retTy_eq := rfl,
              args := .cons (.there .here) (.cons .here .nil) }
        (.ret .here)))

/-- The textual MLIR. -/
def add_3_4_mlir : String :=
  Com.printModule add_3_4_vir "add_3_4"

end Test

end CatCrypt.Crypto.SecureCompilation.VIR.CatCryptPrint
