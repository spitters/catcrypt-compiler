/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

@[expose] public section

set_option autoImplicit false

/-!
# secp256k1 field multiply `feMul` (256×256 → 256 mod p), FRONT-COMPILED to owned x86

This module sources a full 4-limb secp256k1 field multiply
`out = (a · b) mod p`, `p = 2^256 − 2^32 − 977`, end-to-end through the verified
front — NO hand-built `Com` / `Lcmd` / `JInstr` anywhere in the emit
path (the framed straight-line route of `Bn254TowerFrontEmit`, scaled from a
4-limb add/sub to the 4-limb schoolbook multiply + Solinas reduce):

```
  feMulBody (LowCT: RArrLoad / RScalarSetExpr limb math / RArrStore)
    --(translateDialectControl)--> Com catCryptDialect inΓ (.memref 4)
    --(cryptoDialectToJasminCom)--> Com jasminDialect …   (stackLoad/stackStore)
    --(Com.toLprogPhysAbi, [RDI,RSI,RDX] memref ABI)--> Lprog
    --(renderLprogAtt)--> bench/secp256k1_femul_front_compare/gen_com/secp256k1_femul.s
```

## Why 32-bit limbs — carry-free through the covered `SExpr` alphabet

The front lowers the `SExpr` fragment `SMul`/`SAdd`/`SSub`/`SAnd`/`SShr`/`SShl`
(the `translateDialectDirectArms.lowerSExpr` alphabet). Carry/borrow is **not** an
`SExpr` (only the reg-1 `addCarryLo`/`addCarryHi` dialect ops carry it, and there
is no `SExpr` surface that emits them). So the kernel is written in **32-bit
limbs held in 64-bit words**: every partial product `A·B` of two 32-bit halves is
`< 2^64` (single `SMul`, no high word needed), and in an operand-scanning schedule
each column accumulator `acc + A·B + carry` stays `< 2^64`
(`(2^32−1) + (2^32−1)^2 + (2^32−1) = 2^64 − 1`). The carry is then extracted as a
plain word split `carry = t >>> 32`, `limb = t &&& (2^32−1)` — the reg-64 carry
synthesis (route (i) of the field-arith front plan), needing NO reg-1 op and NO
bit-hack `bSltu` window. Every operation is in the covered alphabet.

## The reduction — Solinas fold, `2^256 ≡ 2^32 + 977 (mod p)`

The `8×8` operand-scanning multiply yields the 16-limb (512-bit) product `P`.
With `c = 2^32 + 977` and `2^256 ≡ c (mod p)`, each fold replaces the high half by
`c ·` it: `R = P[0..7] + c · P[8..]`. Four folds collapse the value below `2^256`
(the top limb is provably `0` after fold 4 for every input incl. the extremal
`(p−1)^2`), after which a single branch-free conditional subtract of `p`
canonicalises `R ∈ [0, 2p)` into `[0, p)`. Both the `c·hi` step and the
conditional subtract are expressed with the same generic operand-scanning
`genMul` / `genAdd` and a 32-bit-limb borrow `genSub` — all in the covered
alphabet.

## ABI (the C caller's contract)

```c
extern void secp256k1_femul(uint64_t *out, const uint64_t *a, const uint64_t *b);
//   a[0..3], b[0..3] : little-endian 4×u64 canonical residues in [0, p)
//   out[0..3] = (a * b) mod p
```

`RDI = out`, `RSI = a`, `RDX = b` (the SysV 3-pointer memref ABI). Each pointer is
a 4-cell (`.memref 4`, 32-byte) `u64` frame.

## Gates

In-model: the body front-compiles and lowers to `Com jasminDialect` (`§5`). The
deployed `.s` is checked against GMP `mpz_mulmod` at `p` by the external known-answer
harness in `bench/secp256k1_femul_front_compare`; no evaluation of the program's
denotation runs in Lean.
-/

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim (renderLprogAttOpt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)

/-! ## 0. Constants -/

/-- secp256k1 base prime `p = 2^256 − 2^32 − 977`. -/
def pNat : Nat := 115792089237316195423570985008687907853269984665640564039457584007908834671663
/-- `2^32 − 1`, the 32-bit mask. -/
def mask32 : Nat := 4294967295
/-- The little-endian 32-bit limbs of `p` (`pl32[0]` least significant). -/
def pl32 : List Nat := (List.range 8).map (fun i => (pNat >>> (32 * i)) &&& mask32)
/-- Low 32-bit limb of `c = 2^32 + 977`, i.e. `977`. -/
def cc0 : Nat := 977
/-- High 32-bit limb of `c = 2^32 + 977`, i.e. `1`. -/
def cc1 : Nat := 1

/-! ## 1. Generic name-threaded limb-arithmetic generators

All generators emit a flat `List LowCT` of `RScalarSetExpr` bindings over the
covered `SExpr` alphabet and return the SSA names of their result limbs. Every
limb value is `< 2^64` so `SExpr.evalBV`'s 64-bit wrapping never truncates the
intended arithmetic. `zero` is the name of a slot bound to `0`. -/

/-- `SVar` shorthand. -/
def sv (n : String) : SExpr := .SVar n

abbrev MulI : Type := MProd (Array String) (MProd String (List LowCT))
abbrev MulO : Type := MProd (Array String) (List LowCT)

/-- The inner column step of `genMul`: one partial product accumulated into the
    column, split into a 32-bit digit and a carry. -/
def genMulInnerStep (_zero : String) (aN bN : List String) (pfx : String) (i : Nat) :
    Nat → MulI → Id (ForInStep MulI) :=
  fun j r =>
    let acc := r.fst
    let carry := r.snd.fst
    let cmds := r.snd.snd
    let pos := i + j
    let tn := s!"{pfx}t{i}_{j}"
    let cmds := cmds ++ [(LowCT.RScalarSetExpr tn
      (.SAdd (.SAdd (.SMul (sv (aN[i]!)) (sv (bN[j]!))) (sv (acc[pos]!))) (sv carry)))]
    let pn := s!"{pfx}p{i}_{j}"
    let cmds := cmds ++ [(LowCT.RScalarSetExpr pn (.SAnd (sv tn) (.SLit mask32)))]
    let kn := s!"{pfx}k{i}_{j}"
    let cmds := cmds ++ [(LowCT.RScalarSetExpr kn (.SShr (sv tn) (.SLit 32)))]
    ForInStep.yield ⟨acc.set! pos pn, kn, cmds⟩

def genMulOuterStep (zero : String) (aN bN : List String) (pfx : String) :
    Nat → MulO → Id (ForInStep MulO) :=
  fun i r =>
    let res : MulI :=
      (forIn [:bN.length] (⟨r.fst, zero, r.snd⟩) (genMulInnerStep zero aN bN pfx i) : Id _)
    ForInStep.yield ⟨res.fst.set! (i + bN.length) res.snd.fst, res.snd.snd⟩

def genMulRun (zero : String) (aN bN : List String) (pfx : String) : MulO :=
  (forIn [:aN.length] (⟨Array.replicate (aN.length + bN.length) zero, ([] : List LowCT)⟩)
    (genMulOuterStep zero aN bN pfx) : Id _)

abbrev AddS : Type := MProd String (MProd (List LowCT) (Array String))

def genAddStep (zero : String) (aN bN : List String) (pfx : String) :
    Nat → AddS → Id (ForInStep AddS) :=
  fun i r =>
    let carry := r.fst
    let cmds := r.snd.fst
    let res := r.snd.snd
    let ai := aN.getD i zero
    let bi := bN.getD i zero
    let tn := s!"{pfx}t{i}"
    let cmds := cmds ++ [(LowCT.RScalarSetExpr tn (.SAdd (.SAdd (sv ai) (sv bi)) (sv carry)))]
    let sn := s!"{pfx}s{i}"
    let cmds := cmds ++ [(LowCT.RScalarSetExpr sn (.SAnd (sv tn) (.SLit mask32)))]
    let kn := s!"{pfx}k{i}"
    let cmds := cmds ++ [(LowCT.RScalarSetExpr kn (.SShr (sv tn) (.SLit 32)))]
    ForInStep.yield ⟨kn, cmds, res.set! i sn⟩

def genAddRun (zero : String) (aN bN : List String) (pfx : String) : AddS :=
  (forIn [:max aN.length bN.length]
    (⟨zero, ([] : List LowCT), Array.replicate (max aN.length bN.length + 1) zero⟩)
    (genAddStep zero aN bN pfx) : Id _)

abbrev SubS : Type := MProd String (MProd (List LowCT) (Array String))

def genSubStep (zero : String) (aN pN : List String) (pfx : String) :
    Nat → SubS → Id (ForInStep SubS) :=
  fun i r =>
    let borrow := r.fst
    let cmds := r.snd.fst
    let res := r.snd.snd
    let tn := s!"{pfx}t{i}"
    let cmds := cmds ++ [(LowCT.RScalarSetExpr tn
      (.SSub (.SSub (.SAdd (sv (aN[i]!)) (.SLit 4294967296)) (sv (pN.getD i zero)))
        (sv borrow)))]
    let dn := s!"{pfx}d{i}"
    let cmds := cmds ++ [(LowCT.RScalarSetExpr dn (.SAnd (sv tn) (.SLit mask32)))]
    let hn := s!"{pfx}h{i}"
    let cmds := cmds ++ [(LowCT.RScalarSetExpr hn (.SShr (sv tn) (.SLit 32)))]
    let bn := s!"{pfx}b{i}"
    let cmds := cmds ++ [(LowCT.RScalarSetExpr bn (.SSub (.SLit 1) (sv hn)))]
    ForInStep.yield ⟨bn, cmds, res.set! i dn⟩

def genSubRun (zero : String) (aN pN : List String) (pfx : String) : SubS :=
  (forIn [:aN.length] (⟨zero, ([] : List LowCT), Array.replicate aN.length zero⟩)
    (genSubStep zero aN pN pfx) : Id _)

/-- Operand-scanning `na × nb` limb multiply. Returns the bindings and the
    `na + nb` result-limb names. Each column step `acc + a·b + carry < 2^64`. -/
def genMul (zero : String) (aN bN : List String) (pfx : String) :
    List LowCT × List String :=
  let r := genMulRun zero aN bN pfx
  (r.snd, r.fst.toList)

/-- Operand-scanning limb add. Returns bindings and `max(|a|,|b|) + 1` result
    names (the extra top limb is the final carry). -/
def genAdd (zero : String) (aN bN : List String) (pfx : String) :
    List LowCT × List String :=
  let r := genAddRun zero aN bN pfx
  (r.snd.fst, (r.snd.snd.set! (max aN.length bN.length) r.fst).toList)

/-- One Solinas fold `R = lo(8) + c · hi(rest)` on a limb list `full`, `c` given by
    its two limb names `c0N`, `c1N`. Returns the bindings and result names. -/
def genFold (zero c0N c1N : String) (full : List String) (pfx : String) :
    List LowCT × List String := Id.run do
  let lo := full.take 8
  let hi := full.drop 8
  if hi.isEmpty then
    return ([], full)
  else
    let (mc, chi) := genMul zero [c0N, c1N] hi (pfx ++ "m")
    let (ac, res) := genAdd zero lo chi (pfx ++ "a")
    return (mc ++ ac, res)

/-- 32-bit-limb ripple subtract `d = a − p`, borrow-free via
    `t = a[i] + 2^32 − p[i] − bin` (`t ∈ [0, 2^33)`, no `SExpr` underflow),
    `d[i] = t & mask`, `bout = 1 − (t >>> 32)`. Returns bindings, the `|a|`
    difference names, and the final-borrow name (`1` iff `a < p`). -/
def genSub (zero : String) (aN pN : List String) (pfx : String) :
    List LowCT × List String × String :=
  let r := genSubRun zero aN pN pfx
  (r.snd.fst, r.snd.snd.toList, r.fst)

/-! ## 2. The `feMul` body

Load `a`, `b` limbs, split each `u64` into two 32-bit halves, multiply, fold four
times, one conditional subtract, recombine to `u64`, store into `out`. -/

/-- Sequence a `List LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- Bind the constant cell indices `ix0 .. ix3` and the reduction constants. -/
def constInit : List LowCT :=
  ((List.range 4).map (fun i => (.RScalarSetExpr s!"ix{i}" (.SLit i) : LowCT)))
  ++ [ (.RScalarSetExpr "ZZ" (.SLit 0) : LowCT),
       (.RScalarSetExpr "CC0" (.SLit cc0) : LowCT),
       (.RScalarSetExpr "CC1" (.SLit cc1) : LowCT) ]
  ++ ((List.range 8).map (fun i => (.RScalarSetExpr s!"PL{i}" (.SLit (pl32.getD i 0)) : LowCT)))

/-- Load 4 `u64` limbs of frame `arr` into `{d}0 .. {d}3`. -/
def loadLimbs (arr d : String) : List LowCT :=
  (List.range 4).map (fun j =>
    (.RArrLoad ⟨s!"{d}{j}", .TU64⟩ ⟨arr, .TBytes 32⟩ s!"ix{j}" : LowCT))

/-- Split each of the 4 `u64` limbs `{src}0..3` into 8 little-endian 32-bit halves
    `{dst}0..7` (`{dst}(2i) = lo`, `{dst}(2i+1) = hi`). -/
def splitLimbs (src dst : String) : List LowCT :=
  (List.range 4).flatMap (fun i =>
    [ (.RScalarSetExpr s!"{dst}{2*i}" (.SAnd (sv s!"{src}{i}") (.SLit mask32)) : LowCT),
      (.RScalarSetExpr s!"{dst}{2*i+1}" (.SShr (sv s!"{src}{i}") (.SLit 32)) : LowCT) ])

/-- Recombine 8 32-bit result halves `{r}0..7` into 4 `u64` `{o}0..3`
    (`{o}i = {r}(2i) + ({r}(2i+1) << 32)`) and store into `out`. -/
def recombineStore (r o : String) : List LowCT :=
  (List.range 4).flatMap (fun i =>
    [ (.RScalarSetExpr s!"{o}{i}"
        (.SAdd (sv s!"{r}{2*i}") (.SShl (sv s!"{r}{2*i+1}") (.SLit 32))) : LowCT),
      (.RArrStore ⟨"out", .TBytes 32⟩ s!"ix{i}" ⟨s!"{o}{i}", .TU64⟩ : LowCT) ])

/-- Names of an 8-limb split half. -/
def halfNames (d : String) : List String := (List.range 8).map (fun i => s!"{d}{i}")

/-- The full front body. -/
def feMulBody : LowCT := Id.run do
  let mut cmds : List LowCT := constInit
  cmds := cmds ++ loadLimbs "a" "au" ++ splitLimbs "au" "A"
  cmds := cmds ++ loadLimbs "b" "bu" ++ splitLimbs "bu" "B"
  -- 8×8 operand-scanning multiply → 16 product limbs
  let (mc, prod) := genMul "ZZ" (halfNames "A") (halfNames "B") "M"
  cmds := cmds ++ mc
  -- four Solinas folds
  let (f1c, r1) := genFold "ZZ" "CC0" "CC1" prod "F1"
  let (f2c, r2) := genFold "ZZ" "CC0" "CC1" r1 "F2"
  let (f3c, r3) := genFold "ZZ" "CC0" "CC1" r2 "F3"
  let (f4c, r4) := genFold "ZZ" "CC0" "CC1" r3 "F4"
  cmds := cmds ++ f1c ++ f2c ++ f3c ++ f4c
  let lo8 := r4.take 8
  -- one conditional subtract of p
  let pN := (List.range 8).map (fun i => s!"PL{i}")
  let (sc, dN, bw) := genSub "ZZ" lo8 pN "S"
  cmds := cmds ++ sc
  -- select: keep `lo8` iff `lo8 < p` (bw = 1), else the difference `dN`
  -- mMask = (0 - bw) & mask  (all-ones iff bw=1);  notMask = mMask ^ mask
  cmds := cmds ++ [ (.RScalarSetExpr "MMR" (.SSub (.SLit 0) (sv bw)) : LowCT),
                    (.RScalarSetExpr "MM" (.SAnd (sv "MMR") (.SLit mask32)) : LowCT),
                    (.RScalarSetExpr "NM" (.SXor (sv "MM") (.SLit mask32)) : LowCT) ]
  let rNames : List String := (List.range 8).map (fun i => s!"R{i}")
  for i in [0:8] do
    cmds := cmds ++ [ (.RScalarSetExpr (rNames[i]!)
      (.SAdd (.SAnd (sv (lo8[i]!)) (sv "MM")) (.SAnd (sv (dN[i]!)) (sv "NM"))) : LowCT) ]
  -- recombine 8 halves → 4 u64 and store
  cmds := cmds ++ recombineStore "R" "O"
  return seqAll cmds

/-! ## 3. Input context + `VarMap`

`comToLfundef` reverses context↔argument order: to land `out ← RDI`, `a ← RSI`,
`b ← RDX`, bind `out` deepest; the head-first context is `[b, a, out]`. -/

/-- Head-first kernel context `[b, a, out]`, each a 4-cell `u64` memref. -/
def inΓ : Ctx := [.memref 4, .memref 4, .memref 4]

/-- The kernel `VarMap`: `out` deepest (→ RDI), then `a` (→ RSI), then `b`
    (head, → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 4) "out").bind
    (t := .memref 4) "a").bind (t := .memref 4) "b"

/-! ## 4. Front-compile, lower -/

/-- Push the body through the direct control front and cap with `ret out`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 4)) :=
  match translateDialectControl inVM feMulBody with
  | some r =>
      match r.vm.lookup "out" with
      | some ⟨.memref 4, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted dialect program lowers to a `Com jasminDialect`
    (`memrefGetDyn`/`memrefSetDyn` → `stackLoad`/`stackStore`). -/
def loweredOpt :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontCom with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

/-! ## 5. Front-compile / lower gates -/

/-- The body front-compiles (`translateDialectControl` + `ret out`). -/
theorem frontCom_isSome : frontCom.isSome := by native_decide

/-- The kernel lowers end-to-end to `Com jasminDialect`. -/
theorem lowered_isSome : loweredOpt.isSome := by native_decide

/-! ## 6. The `Nat` `(a·b) mod p` spec and a denotation reader -/

/-- Recombine 4 little-endian `u64` cells to a `Nat`. -/
def valOf (ws : List Nat) : Nat :=
  ws[0]! + 2 ^ 64 * ws[1]! + 2 ^ 128 * ws[2]! + 2 ^ 192 * ws[3]!

/-- Split a `Nat` into 4 little-endian `u64` limbs. -/
def limbs4 (n : Nat) : List Nat :=
  [n % 2 ^ 64, n / 2 ^ 64 % 2 ^ 64, n / 2 ^ 128 % 2 ^ 64, n / 2 ^ 192 % 2 ^ 64]

/-- Independent spec: `(a · b) mod p`, componentwise little-endian limbs. -/
def feMulSpec (a b : List Nat) : List Nat := limbs4 ((valOf a * valOf b) % pNat)

/-- A 4-cell memref valuation from a limb list. -/
def vecOf (ws : List Nat) : Fin 4 → BitVec 64 := fun i => BitVec.ofNat 64 ws[i.val]!

/-- Kernel valuation, head-first `[b, a, out]` (matches `inΓ`). -/
def encodeVal (av bv : Fin 4 → BitVec 64) : @Ctxt.Valuation catCryptDialect _ inΓ :=
  .cons bv (.cons av (.cons (fun _ => (0 : BitVec 64)) .nil))

/-- Denote the front kernel and read out all 4 result cells. -/
def denoteCells (a b : List Nat) : Option (List Nat) :=
  frontCom.map (fun c =>
    (List.range 4).map (fun i =>
      (c.denote (encodeVal (vecOf a) (vecOf b)) ⟨i % 4, Nat.mod_lt _ (by decide)⟩).toNat))

/-! ## 7. Owned emit driver -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Com.toLprogPhysAbi Lprog)

/-- The lowered kernel as an owned AT&T `.s` under the SysV 3-pointer ABI. -/
def femulAsm (_ : Unit) : Option String :=
  loweredOpt.map (fun s =>
    CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned
      (Com.toLprogPhysAbi s.2.2 "secp256k1_femul"
        (fun _ => none) (fun _ => none) (fun _ => none) []
        (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
        (residence := none) (abiW := 0) (forceLivePin := true)))

/-- Write the front-generated kernel to `gen_com/secp256k1_femul.s`. -/
def emit (path : System.FilePath) : IO Unit := do
  match femulAsm () with
  | some a => do
      if let some d := path.parent then IO.FS.createDirAll d
      IO.FS.writeFile path a
      IO.println s!"SECP256K1-FEMUL emit OK : {path} ({a.toUTF8.size} bytes, symbol secp256k1_femul)"
  | none => throw (IO.userError "front-compile of secp256k1_femul failed (front/lowering declined)")

end CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
