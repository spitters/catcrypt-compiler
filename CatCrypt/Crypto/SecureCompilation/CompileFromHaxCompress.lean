/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxScope

/-!
# The SHA-256 compression round loop compiles, value-correct

The companion to §9's message schedule: the **compression loop** (FIPS 180-4
§6.2.2). Each round `t` updates the eight working words `a..h`:

```text
T1 = h + Σ₁(e) + Ch(e,f,g) + K[t] + W[t]
T2 = Σ₀(a) + Maj(a,b,c)
(a,b,c,d,e,f,g,h) := (T1+T2, a, b, c, d+T1, e, f, g)
```
with `Σ₀(x)=(x⋙2)⊕(x⋙13)⊕(x⋙22)`, `Σ₁(x)=(x⋙6)⊕(x⋙11)⊕(x⋙25)`,
`Ch(e,f,g)=(e∧f)⊕(¬e∧g)`, `Maj(a,b,c)=(a∧b)⊕(a∧c)⊕(b∧c)`, and `K[t]` the FIPS
round constants.

Only `a` and `e` are new each round (`b,c,d` shift down from `a`;
`f,g,h` from `e`), so the SSA unrolling binds **two** fresh state locals per round
plus the round's scratch temporaries, passing the renamed words to the next round
— the register-renaming the round loop is. `K[t]` is materialised as a literal
constant (the front's `regConst`), `W[t]` read from the input array. Every binding
has atom arguments, so it compiles through the unchanged `compileFromHax` with no
`anfLift`. This file builds the round body + spec and validates the single round by
`rfl`; the general-N preservation (the §9 induction with the eight-word state) and
the full 64-round result build on it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxCompress

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxScope
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect JasminBinOp)

/-! ## §1  The FIPS 180-4 round functions (spec) -/

/-- `Σ₀(x) = (x ⋙ 2) ⊕ (x ⋙ 13) ⊕ (x ⋙ 22)`. -/
def bigSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- `Σ₁(x) = (x ⋙ 6) ⊕ (x ⋙ 11) ⊕ (x ⋙ 25)`. -/
def bigSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- `Ch(e,f,g) = (e ∧ f) ⊕ (¬e ∧ g)`. The complement is written `e ⊕ (2³²−1)`
    (`= ~~~e`) — the all-ones constant the front materialises (`__ones`), so the
    value proof closes by `rfl`. -/
def chFn (e f g : BitVec 32) : BitVec 32 :=
  (e &&& f) ^^^ ((e ^^^ BitVec.ofNat 32 4294967295) &&& g)

/-- `Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)`. -/
def majFn (a b c : BitVec 32) : BitVec 32 := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

/-! ## §2  The compression state and round (spec) -/

/-- The eight SHA-256 working words `a..h`. -/
structure St where
  a : BitVec 32
  b : BitVec 32
  c : BitVec 32
  d : BitVec 32
  e : BitVec 32
  f : BitVec 32
  g : BitVec 32
  h : BitVec 32

/-- One FIPS 180-4 compression round at constant `ki` and schedule word `wi`. -/
def roundFn (s : St) (ki wi : BitVec 32) : St :=
  let t1 := s.h + bigSigma1 s.e + chFn s.e s.f s.g + ki + wi
  let t2 := bigSigma0 s.a + majFn s.a s.b s.c
  St.mk (t1 + t2) s.a s.b s.c (s.d + t1) s.e s.f s.g

/-- The compression fold: `count` rounds from `init`, round `t` using `K t`/`W t`. -/
def compFold (init : St) (K W : Nat → BitVec 32) : Nat → St
  | 0 => init
  | n + 1 => roundFn (compFold init K W n) (K n) (W n)

/-- The FIPS 180-4 §4.2.2 round constants `K[0..63]` (first 32 bits of the
    fractional parts of the cube roots of the first 64 primes). -/
def kTable : List Nat :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
   0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
   0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
   0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
   0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
   0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
   0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
   0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
   0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- `K[t]` as a `Nat` (the source materialises this as a literal `regConst`). -/
def kVal (t : Nat) : Nat := kTable.getD t 0

/-- `K[t]` as the `BitVec 32` spec value. -/
def kBV (t : Nat) : BitVec 32 := BitVec.ofNat 32 (kVal t)

/-! ## §3  The round body and unroller (`ImpExpr`)

Each round is emitted **already let-normalized** (atom args throughout): the Σ/Ch/Maj
sub-results bind to scratch temporaries, then `t1`/`t2` and the two new
words `a'`/`e'`. The other six words are renames, passed by name to the next round.
`K[t]` is a literal; `W[t]` an input read (`index[in, lit (8+t)]`). All scratch
names are literals (reused per round, dead after) so env comparisons stay cheap; the
two fresh words per round are round-indexed. -/

/-- Per-round fresh `a'` / `e'` names (round-indexed, unary so they reduce cheaply
    and are distinct across rounds and from the literal scratch names). -/
def aN (r : Nat) : String := "qa" ++ String.ofList (List.replicate (r + 1) 'I')
def eN (r : Nat) : String := "qe" ++ String.ofList (List.replicate (r + 1) 'I')

/-- An input read `index[in, lit k]`. -/
def rdIn (k : Nat) : ImpExpr := .app "index" [.var "in", .lit (.int k)]

/-- A 3-rotate `Σ` block: bind `nout := (rE⋙rot1) ⊕ (rE⋙rot2) ⊕ (rE⋙rot3)` (scratch
    `ba/bb/bc/bx`), then `cont`. -/
def bigSigBlock (rot1 rot2 rot3 : Nat) (nout : String) (rE cont : ImpExpr) : ImpExpr :=
  .letBind "ba" (.app "rotate_right" [rE, .lit (.int rot1)])
   (.letBind "bb" (.app "rotate_right" [rE, .lit (.int rot2)])
    (.letBind "bc" (.app "rotate_right" [rE, .lit (.int rot3)])
     (.letBind "bx" (.app "BitXor" [.var "ba", .var "bb"])
      (.letBind nout (.app "BitXor" [.var "bx", .var "bc"]) cont))))

/-- The `Ch` block: bind `nout := (eE ∧ fE) ⊕ (¬eE ∧ gE)` (`¬e = e ⊕ __ones`, scratch
    `ca/cb/cc`), then `cont`. -/
def chBlock (nout : String) (eE fE gE cont : ImpExpr) : ImpExpr :=
  .letBind "ca" (.app "BitAnd" [eE, fE])
   (.letBind "cb" (.app "BitXor" [eE, .var "__ones"])
    (.letBind "cc" (.app "BitAnd" [.var "cb", gE])
     (.letBind nout (.app "BitXor" [.var "ca", .var "cc"]) cont)))

/-- The `Maj` block: bind `nout := (aE ∧ bE) ⊕ (aE ∧ cE) ⊕ (bE ∧ cE)` (scratch
    `ma/mb/mc/mx`), then `cont`. -/
def majBlock (nout : String) (aE bE cE cont : ImpExpr) : ImpExpr :=
  .letBind "ma" (.app "BitAnd" [aE, bE])
   (.letBind "mb" (.app "BitAnd" [aE, cE])
    (.letBind "mc" (.app "BitAnd" [bE, cE])
     (.letBind "mx" (.app "BitXor" [.var "ma", .var "mb"])
      (.letBind nout (.app "BitXor" [.var "mx", .var "mc"]) cont))))

/-- The let-normalized compression round body for round `r`, with the eight current
    working words supplied as **atom read-expressions** `aE..hE` (a `var` for a
    computed word, or an inline `index[in, …]` seed — the front accepts `index`
    only as an operand, not as a `let`-value). Composes the Σ₁/Ch/Σ₀/Maj blocks and
    the five adds (`t1 = h+Σ₁+Ch+K+W`, `t2 = Σ₀+Maj`, `a' = t1+t2`, `e' = d+t1`),
    then runs `cont`. `K[r]` is materialised to a register `kc`; `W[r]` is
    `index[in, lit (8+r)]`. -/
def roundBody (r : Nat) (aE bE cE dE eE fE gE hE : ImpExpr) (cont : ImpExpr) : ImpExpr :=
  bigSigBlock 6 11 25 "s1" eE
   (chBlock "s2" eE fE gE
    (.letBind "u7" (.app "wrapping_add" [hE, .var "s1"])
     (.letBind "u8" (.app "wrapping_add" [.var "u7", .var "s2"])
      (.letBind "kc" (.lit (.int (kVal r)))
       (.letBind "u9" (.app "wrapping_add" [.var "u8", .var "kc"])
        (.letBind "t1" (.app "wrapping_add" [.var "u9", rdIn (8 + r)])
         (bigSigBlock 2 13 22 "s3" aE
          (majBlock "s4" aE bE cE
           (.letBind "t2" (.app "wrapping_add" [.var "s3", .var "s4"])
            (.letBind (aN r) (.app "wrapping_add" [.var "t1", .var "t2"])
             (.letBind (eN r) (.app "wrapping_add" [dE, .var "t1"])
              cont)))))))))))

/-- The compression unroller: run `count` rounds from round `r`, threading the eight
    current working-word read-expressions, returning the final `a` (`aE` at
    `count = 0`). After a round the state shifts: `(a', a, b, c, e', e, f, g)`. -/
def compUnroll : (count r : Nat) → (aE bE cE dE eE fE gE hE : ImpExpr) → ImpExpr
  | 0, _, aE, _, _, _, _, _, _, _ => aE
  | c + 1, r, aE, bE, cE, dE, eE, fE, gE, hE =>
      roundBody r aE bE cE dE eE fE gE hE
        (compUnroll c (r + 1) (.var (aN r)) aE bE cE (.var (eN r)) eE fE gE)

/-- The whole compiled compression: bind the all-ones constant `__ones`, then run
    `N` rounds with the eight initial working words read inline from the input array
    (`index[in, 0..7]`), returning the final `a`. Inputs `0..7` are the initial
    state `a..h`; inputs `8..8+N-1` are the schedule words `W[0..N-1]`. The flat
    `ImpExpr` the front's `impExprToThir` consumes directly. -/
def compProgram (N : Nat) : ImpExpr :=
  .letBind "__ones" (.lit (.int 4294967295))
   (compUnroll N 0 (rdIn 0) (rdIn 1) (rdIn 2) (rdIn 3) (rdIn 4) (rdIn 5) (rdIn 6) (rdIn 7))

/-- The initial compression state read from the input array. -/
def initSt {nIn : Nat} (I : Fin nIn → BitVec 32) : St :=
  St.mk (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)
        (inpGet I 4) (inpGet I 5) (inpGet I 6) (inpGet I 7)

/-- The schedule words as read by the program: `W[t] = index[in, lit (8+t)]`. -/
def wSpec {nIn : Nat} (I : Fin nIn → BitVec 32) (t : Nat) : BitVec 32 := inpGet I (8 + t)

/-! ## §4  The unroller compiles, at every unroll depth

The compression program is a chain of `letBind`s whose operands are either
round-local names just bound or indexed reads of the input array, so it satisfies
the syntactic scope condition of `CompileFromHaxScope`. Discharging that condition
is an induction on the unroll depth: one round extends the bound-name list by
`roundLocals`, and the eight working-word operands handed to the next round are
either freshly bound (`aN r` / `eN r`) or already in scope. -/

/-- The locals one compression round binds, newest first. -/
def roundLocals (r : Nat) : List String :=
  [eN r, aN r, "t2", "s4", "mx", "mc", "mb", "ma", "s3", "bx", "bc", "bb", "ba",
   "t1", "u9", "kc", "u8", "u7", "s2", "cc", "cb", "ca", "s1", "bx", "bc", "bb", "ba"]

/-- The round-output name `aN r` begins with `'q'`. -/
theorem aN_head (r : Nat) : (aN r).toList.head? = some 'q' := by
  simp [aN, String.toList_append, String.toList_ofList]

/-- The round-output name `eN r` begins with `'q'`. -/
theorem eN_head (r : Nat) : (eN r).toList.head? = some 'q' := by
  simp [eN, String.toList_append, String.toList_ofList]

/-- `aN r` is not the array parameter `"in"`. -/
theorem aN_notParam (r : Nat) : (["in"] : List String).idxOf? (aN r) = none := by
  have h : aN r ≠ "in" := by
    intro h; have := aN_head r; rw [h] at this; exact absurd this (by decide)
  simp [List.idxOf?, Ne.symm h]

/-- `eN r` is not the array parameter `"in"`. -/
theorem eN_notParam (r : Nat) : (["in"] : List String).idxOf? (eN r) = none := by
  have h : eN r ≠ "in" := by
    intro h; have := eN_head r; rw [h] at this; exact absurd this (by decide)
  simp [List.idxOf?, Ne.symm h]

/-- A `Σ` block compiles: three rotates of an in-scope operand and two xors. -/
theorem bigSigBlock_compiles {nIn : Nat} (rot1 rot2 rot3 : Nat) (nout : String)
    (rE cont : ImpExpr) (S : List String)
    (hrE : OperandInScope ["in"] nIn S rE)
    (hcont : Compiles ["in"] 32 nIn (nout :: "bx" :: "bc" :: "bb" :: "ba" :: S) cont) :
    Compiles ["in"] 32 nIn S (bigSigBlock rot1 rot2 rot3 nout rE cont) := by
  have hb : recogBin "rotate_right" = none := by simp [recogBin]
  have hs : recogShift "rotate_right" = some ShiftKind.ror := by simp [recogShift]
  have hx : recogBin "BitXor" = some JasminBinOp.xor := by simp [recogBin]
  refine Compiles.letShift (n := rot1) hb hs hrE (by simp [litNat?]) ?_
  refine Compiles.letShift (n := rot2) hb hs (hrE.mono (by intro y hy; simp [hy]))
    (by simp [litNat?]) ?_
  refine Compiles.letShift (n := rot3) hb hs (hrE.mono (by intro y hy; simp [hy]))
    (by simp [litNat?]) ?_
  refine Compiles.letBin hx (.local_ "ba" (by decide) (by simp))
    (.local_ "bb" (by decide) (by simp)) ?_
  exact Compiles.letBin hx (.local_ "bx" (by decide) (by simp))
    (.local_ "bc" (by decide) (by simp)) hcont

/-- The `Ch` block compiles, using the `__ones` complement local. -/
theorem chBlock_compiles {nIn : Nat} (nout : String) (eE fE gE cont : ImpExpr)
    (S : List String) (hones : "__ones" ∈ S)
    (heE : OperandInScope ["in"] nIn S eE)
    (hfE : OperandInScope ["in"] nIn S fE)
    (hgE : OperandInScope ["in"] nIn S gE)
    (hcont : Compiles ["in"] 32 nIn (nout :: "cc" :: "cb" :: "ca" :: S) cont) :
    Compiles ["in"] 32 nIn S (chBlock nout eE fE gE cont) := by
  have hand : recogBin "BitAnd" = some JasminBinOp.and := by simp [recogBin]
  have hx : recogBin "BitXor" = some JasminBinOp.xor := by simp [recogBin]
  refine Compiles.letBin hand heE hfE ?_
  refine Compiles.letBin hx (heE.mono (by intro y hy; simp [hy]))
    (.local_ "__ones" (by decide) (by simp [hones])) ?_
  refine Compiles.letBin hand (.local_ "cb" (by decide) (by simp))
    (hgE.mono (by intro y hy; simp [hy])) ?_
  exact Compiles.letBin hx (.local_ "ca" (by decide) (by simp))
    (.local_ "cc" (by decide) (by simp)) hcont

/-- The `Maj` block compiles: three ands of in-scope operands and two xors. -/
theorem majBlock_compiles {nIn : Nat} (nout : String) (aE bE cE cont : ImpExpr)
    (S : List String)
    (haE : OperandInScope ["in"] nIn S aE)
    (hbE : OperandInScope ["in"] nIn S bE)
    (hcE : OperandInScope ["in"] nIn S cE)
    (hcont : Compiles ["in"] 32 nIn (nout :: "mx" :: "mc" :: "mb" :: "ma" :: S) cont) :
    Compiles ["in"] 32 nIn S (majBlock nout aE bE cE cont) := by
  have hand : recogBin "BitAnd" = some JasminBinOp.and := by simp [recogBin]
  have hx : recogBin "BitXor" = some JasminBinOp.xor := by simp [recogBin]
  refine Compiles.letBin hand haE hbE ?_
  refine Compiles.letBin hand (haE.mono (by intro y hy; simp [hy]))
    (hcE.mono (by intro y hy; simp [hy])) ?_
  refine Compiles.letBin hand (hbE.mono (by intro y hy; simp [hy]))
    (hcE.mono (by intro y hy; simp [hy])) ?_
  refine Compiles.letBin hx (.local_ "ma" (by decide) (by simp))
    (.local_ "mb" (by decide) (by simp)) ?_
  exact Compiles.letBin hx (.local_ "mx" (by decide) (by simp))
    (.local_ "mc" (by decide) (by simp)) hcont

/-- One compression round compiles: the four blocks and the five adds resolve, and
    the continuation runs with `roundLocals r` added to the bound names. -/
theorem roundBody_compiles {nIn : Nat} (r : Nat)
    (aE bE cE dE eE fE gE hE cont : ImpExpr) (S : List String)
    (hones : "__ones" ∈ S) (hw : 8 + r < nIn)
    (haE : OperandInScope ["in"] nIn S aE)
    (hbE : OperandInScope ["in"] nIn S bE)
    (hcE : OperandInScope ["in"] nIn S cE)
    (hdE : OperandInScope ["in"] nIn S dE)
    (heE : OperandInScope ["in"] nIn S eE)
    (hfE : OperandInScope ["in"] nIn S fE)
    (hgE : OperandInScope ["in"] nIn S gE)
    (hhE : OperandInScope ["in"] nIn S hE)
    (hcont : Compiles ["in"] 32 nIn (roundLocals r ++ S) cont) :
    Compiles ["in"] 32 nIn S (roundBody r aE bE cE dE eE fE gE hE cont) := by
  have hadd : recogBin "wrapping_add" = some JasminBinOp.add := by simp [recogBin]
  refine bigSigBlock_compiles 6 11 25 "s1" eE _ S heE ?_
  refine chBlock_compiles "s2" eE fE gE _ _ (by simp [hones])
    (heE.mono (by intro y hy; simp [hy])) (hfE.mono (by intro y hy; simp [hy]))
    (hgE.mono (by intro y hy; simp [hy])) ?_
  refine Compiles.letBin hadd (hhE.mono (by intro y hy; simp [hy]))
    (.local_ "s1" (by decide) (by simp)) ?_
  refine Compiles.letBin hadd (.local_ "u7" (by decide) (by simp))
    (.local_ "s2" (by decide) (by simp)) ?_
  refine Compiles.letLit (l := .int (kVal r)) (n := kVal r) (by simp [litNat?]) ?_
  refine Compiles.letBin hadd (.local_ "u8" (by decide) (by simp))
    (.local_ "kc" (by decide) (by simp)) ?_
  refine Compiles.letBin hadd (.local_ "u9" (by decide) (by simp))
    (.input "in" (.int (8 + r)) (8 + r) (by simp) (by simp [litNat?]; omega) hw) ?_
  refine bigSigBlock_compiles 2 13 22 "s3" aE _ _
    (haE.mono (by intro y hy; simp [hy])) ?_
  refine majBlock_compiles "s4" aE bE cE _ _
    (haE.mono (by intro y hy; simp [hy])) (hbE.mono (by intro y hy; simp [hy]))
    (hcE.mono (by intro y hy; simp [hy])) ?_
  refine Compiles.letBin hadd (.local_ "s3" (by decide) (by simp))
    (.local_ "s4" (by decide) (by simp)) ?_
  refine Compiles.letBin hadd (.local_ "t1" (by decide) (by simp))
    (.local_ "t2" (by decide) (by simp)) ?_
  exact Compiles.letBin hadd (hdE.mono (by intro y hy; simp [hy]))
    (.local_ "t1" (by decide) (by simp)) hcont

/-- **The compression unroller compiles at every depth.** `compUnroll (c+1) r`
    — the `c+1`-round chain from round `r`, threading the eight working-word read
    operands — satisfies the scope condition whenever the operands and `__ones` are
    in scope and the schedule words `W[r .. r+c]` are input slots. Induction on the
    unroll depth. -/
theorem compUnroll_compiles {nIn : Nat} :
    ∀ (c r : Nat) (S : List String) (aE bE cE dE eE fE gE hE : ImpExpr),
      8 + r + c < nIn → "__ones" ∈ S →
      OperandInScope ["in"] nIn S aE → OperandInScope ["in"] nIn S bE →
      OperandInScope ["in"] nIn S cE → OperandInScope ["in"] nIn S dE →
      OperandInScope ["in"] nIn S eE → OperandInScope ["in"] nIn S fE →
      OperandInScope ["in"] nIn S gE → OperandInScope ["in"] nIn S hE →
      Compiles ["in"] 32 nIn S (compUnroll (c + 1) r aE bE cE dE eE fE gE hE) := by
  intro c
  induction c with
  | zero =>
      intro r S aE bE cE dE eE fE gE hE hw hones ha hb hc hd he hf hg hh
      refine roundBody_compiles r aE bE cE dE eE fE gE hE _ S hones (by omega)
        ha hb hc hd he hf hg hh ?_
      exact Compiles.var (aN_notParam r) (by simp [roundLocals])
  | succ c ih =>
      intro r S aE bE cE dE eE fE gE hE hw hones ha hb hc hd he hf hg hh
      refine roundBody_compiles r aE bE cE dE eE fE gE hE _ S hones (by omega)
        ha hb hc hd he hf hg hh ?_
      refine ih (r + 1) (roundLocals r ++ S) _ _ _ _ _ _ _ _ (by omega)
        (by simp [roundLocals, hones])
        (.local_ (aN r) (aN_notParam r) (by simp [roundLocals]))
        (ha.mono (by intro y hy; simp [roundLocals, hy]))
        (hb.mono (by intro y hy; simp [roundLocals, hy]))
        (hc.mono (by intro y hy; simp [roundLocals, hy]))
        (.local_ (eN r) (eN_notParam r) (by simp [roundLocals]))
        (he.mono (by intro y hy; simp [roundLocals, hy]))
        (hf.mono (by intro y hy; simp [roundLocals, hy]))
        (hg.mono (by intro y hy; simp [roundLocals, hy]))

/-- **The compression program compiles at every round count.** `compProgram (N+1)`
    over `nIn` input slots satisfies the scope condition whenever the eight initial
    words and the `N+1` schedule words are input slots. -/
theorem compProgram_compiles {nIn N : Nat} (h : 8 + N < nIn) :
    Compiles ["in"] 32 nIn [] (compProgram (N + 1)) := by
  refine Compiles.letLit (l := .int 4294967295) (n := 4294967295) (by simp [litNat?]) ?_
  exact compUnroll_compiles N 0 ["__ones"] _ _ _ _ _ _ _ _ (by omega) (by simp)
    (.input "in" (.int 0) 0 (by simp) (by simp [litNat?]) (by omega))
    (.input "in" (.int 1) 1 (by simp) (by simp [litNat?]) (by omega))
    (.input "in" (.int 2) 2 (by simp) (by simp [litNat?]) (by omega))
    (.input "in" (.int 3) 3 (by simp) (by simp [litNat?]) (by omega))
    (.input "in" (.int 4) 4 (by simp) (by simp [litNat?]) (by omega))
    (.input "in" (.int 5) 5 (by simp) (by simp [litNat?]) (by omega))
    (.input "in" (.int 6) 6 (by simp) (by simp [litNat?]) (by omega))
    (.input "in" (.int 7) 7 (by simp) (by simp [litNat?]) (by omega))

/-! ## §5  The full compression loop compiles -/

/-- **The full SHA-256 compression loop compiles.** All 64 rounds (`compProgram 64`,
    over the 8 initial words + 64 schedule words = 72 input slots) compile through
    the unchanged `compileFromHax`. -/
theorem fullCompress_isSome :
    (compileFromHax (w := 32) (nIn := 72) ["in"] (compProgram 64)).isSome :=
  compileFromHax_isSome_of_compiles (compProgram_compiles (N := 63) (by omega))

/-! ## §6  Round-body value-correctness (validated by `rfl`)

The single round (and, by `rfl`, a handful of rounds) denotes to exactly the FIPS
`roundFn` fold — validating the round body is the real compression round. General-N
value-correctness is the §9-pattern per-round env-induction (`compFold` as the
array-state, the four block-denote lemmas threaded), built on this body. -/

/-- The single compression round compiles. -/
theorem compress1_isSome :
    (compileFromHax (w := 32) (nIn := 9) ["in"] (compProgram 1)).isSome :=
  compileFromHax_isSome_of_compiles (compProgram_compiles (N := 0) (by omega))

set_option maxRecDepth 4000 in
/-- **The compression round body is value-correct.** The one-round program
    denotes to exactly the FIPS 180-4 round `(compFold (initSt I) kBV (wSpec I) 1).a`
    — the final `a` after one round. The round body is the real `roundFn`. -/
theorem compress1_value :
    ∃ c : Com jasminDialect (frontCtxt 32 9 []) (rW 32),
      compileFromHax (w := 32) (nIn := 9) ["in"] (compProgram 1) = some c ∧
      ∀ I : Fin 9 → BitVec 32,
        c.denote (inputValuation 32 9 I) = (compFold (initSt I) kBV (wSpec I) 1).a := by
  refine ⟨_, (Option.some_get compress1_isSome).symm, fun I => ?_⟩
  refine compileFromHax_meets_spec (w := 32) (nIn := 9) ["in"] I (compProgram 1) _
    (Option.some_get compress1_isSome).symm ?_
  rfl

/-- Four compression rounds compile. -/
theorem compress4_isSome :
    (compileFromHax (w := 32) (nIn := 12) ["in"] (compProgram 4)).isSome :=
  compileFromHax_isSome_of_compiles (compProgram_compiles (N := 3) (by omega))

set_option maxRecDepth 8000 in
/-- **Four compression rounds are value-correct** — the round body *chains*
    correctly: the program denotes to `(compFold (initSt I) kBV (wSpec I) 4).a`, the
    final `a` after four FIPS rounds (each consuming the previous state). -/
theorem compress4_value :
    ∃ c : Com jasminDialect (frontCtxt 32 12 []) (rW 32),
      compileFromHax (w := 32) (nIn := 12) ["in"] (compProgram 4) = some c ∧
      ∀ I : Fin 12 → BitVec 32,
        c.denote (inputValuation 32 12 I) = (compFold (initSt I) kBV (wSpec I) 4).a := by
  refine ⟨_, (Option.some_get compress4_isSome).symm, fun I => ?_⟩
  refine compileFromHax_meets_spec (w := 32) (nIn := 12) ["in"] I (compProgram 4) _
    (Option.some_get compress4_isSome).symm ?_
  rfl

/-! ## §7  Block denotation lemmas (toward general-N value-correctness)

The four block helpers each denote, under `denoteScalar`, to `cont` run in the env
extended at `nout` with the block value (plus dead scratch). The compression
analogue of §9's `sigBlock_denote`, the per-round workhorses the general-N induction
threads. The read operands are required to denote *stably* across the block's
scratch extension (the `hr*` hypotheses), exactly as in §9. -/

/-- `bigSigBlock` is value-preserving: it runs `cont` with `nout := Σ(v)`. -/
theorem bigSigBlock_denote {nIn : Nat} (I : Fin nIn → BitVec 32)
    (ρ : String → Option (BitVec 32)) (rot1 rot2 rot3 : Nat) (nout : String)
    (rE : ImpExpr) (v : BitVec 32)
    (hr : ∀ ρ', (∀ y, y ≠ "ba" → y ≠ "bb" → ρ' y = ρ y) →
        denoteAtomExpr ["in"] I rE ρ' = some v)
    (cont : ImpExpr) :
    ImpExpr.denoteScalar ["in"] I (bigSigBlock rot1 rot2 rot3 nout rE cont) ρ
      = ImpExpr.denoteScalar ["in"] I cont
          (fun y => if y = nout then some (v.rotateRight rot1 ^^^ v.rotateRight rot2 ^^^ v.rotateRight rot3)
                    else if y = "bx" then some (v.rotateRight rot1 ^^^ v.rotateRight rot2)
                    else if y = "bc" then some (v.rotateRight rot3)
                    else if y = "bb" then some (v.rotateRight rot2)
                    else if y = "ba" then some (v.rotateRight rot1) else ρ y) := by
  have e0 := hr ρ (fun _ _ _ => rfl)
  have e1 := hr (fun y => if y = "ba" then some (v.rotateRight rot1) else ρ y)
    (fun y h _ => by simp [if_neg h])
  have e2 := hr (fun y => if y = "bb" then some (v.rotateRight rot2)
                          else if y = "ba" then some (v.rotateRight rot1) else ρ y)
    (fun y h1 h2 => by simp [if_neg h1, if_neg h2])
  have hba : denoteAtomExpr ["in"] I (ImpExpr.var "ba") = fun ρ' => ρ' "ba" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("in":String) ≠ "ba" by decide)]
  have hbb : denoteAtomExpr ["in"] I (ImpExpr.var "bb") = fun ρ' => ρ' "bb" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("in":String) ≠ "bb" by decide)]
  have hbc : denoteAtomExpr ["in"] I (ImpExpr.var "bc") = fun ρ' => ρ' "bc" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("in":String) ≠ "bc" by decide)]
  have hbx : denoteAtomExpr ["in"] I (ImpExpr.var "bx") = fun ρ' => ρ' "bx" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("in":String) ≠ "bx" by decide)]
  simp only [bigSigBlock, ImpExpr.denoteScalar, recogBin, recogShift, litNat?,
    ShiftKind.apply, JasminBinOp.apply, reduceIte, String.reduceEq, Int.toNat,
    or_self, or_false, e0, e1, e2, hba, hbb, hbc, hbx,
    Option.bind_some, Option.map_some, if_true]

/-- `chBlock` is value-preserving: it runs `cont` with `nout := Ch(ve,vf,vg)`. The
    `__ones` local (the all-ones complement) is read from `ρ` (`h_ones`). -/
theorem chBlock_denote {nIn : Nat} (I : Fin nIn → BitVec 32)
    (ρ : String → Option (BitVec 32)) (nout : String) (eE fE gE : ImpExpr)
    (ve vf vg : BitVec 32) (h_ones : ρ "__ones" = some (BitVec.ofNat 32 4294967295))
    (hre : ∀ ρ', (∀ y, y ≠ "ca" → y ≠ "cb" → ρ' y = ρ y) →
        denoteAtomExpr ["in"] I eE ρ' = some ve)
    (hrf : ∀ ρ', (∀ y, y ≠ "ca" → y ≠ "cb" → ρ' y = ρ y) →
        denoteAtomExpr ["in"] I fE ρ' = some vf)
    (hrg : ∀ ρ', (∀ y, y ≠ "ca" → y ≠ "cb" → ρ' y = ρ y) →
        denoteAtomExpr ["in"] I gE ρ' = some vg)
    (cont : ImpExpr) :
    ImpExpr.denoteScalar ["in"] I (chBlock nout eE fE gE cont) ρ
      = ImpExpr.denoteScalar ["in"] I cont
          (fun y => if y = nout then some (chFn ve vf vg)
                    else if y = "cc" then some ((ve ^^^ BitVec.ofNat 32 4294967295) &&& vg)
                    else if y = "cb" then some (ve ^^^ BitVec.ofNat 32 4294967295)
                    else if y = "ca" then some (ve &&& vf) else ρ y) := by
  have ea0 := hre ρ (fun _ _ _ => rfl)
  have ef0 := hrf ρ (fun _ _ _ => rfl)
  have ea1 := hre (fun y => if y = "ca" then some (ve &&& vf) else ρ y)
    (fun y h _ => by simp [if_neg h])
  have eg2 := hrg (fun y => if y = "cb" then some (ve ^^^ BitVec.ofNat 32 4294967295)
                            else if y = "ca" then some (ve &&& vf) else ρ y)
    (fun y h1 h2 => by simp [if_neg h1, if_neg h2])
  have hca : denoteAtomExpr ["in"] I (ImpExpr.var "ca") = fun ρ' => ρ' "ca" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("in":String) ≠ "ca" by decide)]
  have hcb : denoteAtomExpr ["in"] I (ImpExpr.var "cb") = fun ρ' => ρ' "cb" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("in":String) ≠ "cb" by decide)]
  have hcc : denoteAtomExpr ["in"] I (ImpExpr.var "cc") = fun ρ' => ρ' "cc" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("in":String) ≠ "cc" by decide)]
  have hones : denoteAtomExpr ["in"] I (ImpExpr.var "__ones") = fun ρ' => ρ' "__ones" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("in":String) ≠ "__ones" by decide)]
  simp only [chBlock, ImpExpr.denoteScalar, recogBin, JasminBinOp.apply, reduceIte,
    String.reduceEq, or_self, ea0, ef0, ea1, eg2, hca, hcb, hcc,
    hones, h_ones, chFn, Option.bind_some, Option.map_some, if_true]

/-- `majBlock` is value-preserving: it runs `cont` with `nout := Maj(va,vb,vc)`. -/
theorem majBlock_denote {nIn : Nat} (I : Fin nIn → BitVec 32)
    (ρ : String → Option (BitVec 32)) (nout : String) (aE bE cE : ImpExpr)
    (va vb vc : BitVec 32)
    (hra : ∀ ρ', (∀ y, y ≠ "ma" → y ≠ "mb" → ρ' y = ρ y) →
        denoteAtomExpr ["in"] I aE ρ' = some va)
    (hrb : ∀ ρ', (∀ y, y ≠ "ma" → y ≠ "mb" → ρ' y = ρ y) →
        denoteAtomExpr ["in"] I bE ρ' = some vb)
    (hrc : ∀ ρ', (∀ y, y ≠ "ma" → y ≠ "mb" → ρ' y = ρ y) →
        denoteAtomExpr ["in"] I cE ρ' = some vc)
    (cont : ImpExpr) :
    ImpExpr.denoteScalar ["in"] I (majBlock nout aE bE cE cont) ρ
      = ImpExpr.denoteScalar ["in"] I cont
          (fun y => if y = nout then some (majFn va vb vc)
                    else if y = "mx" then some ((va &&& vb) ^^^ (va &&& vc))
                    else if y = "mc" then some (vb &&& vc)
                    else if y = "mb" then some (va &&& vc)
                    else if y = "ma" then some (va &&& vb) else ρ y) := by
  have ea0 := hra ρ (fun _ _ _ => rfl)
  have eb0 := hrb ρ (fun _ _ _ => rfl)
  have ea1 := hra (fun y => if y = "ma" then some (va &&& vb) else ρ y)
    (fun y h _ => by simp [if_neg h])
  have ec1 := hrc (fun y => if y = "ma" then some (va &&& vb) else ρ y)
    (fun y h _ => by simp [if_neg h])
  have eb2 := hrb (fun y => if y = "mb" then some (va &&& vc)
                            else if y = "ma" then some (va &&& vb) else ρ y)
    (fun y h1 h2 => by simp [if_neg h1, if_neg h2])
  have ec2 := hrc (fun y => if y = "mb" then some (va &&& vc)
                            else if y = "ma" then some (va &&& vb) else ρ y)
    (fun y h1 h2 => by simp [if_neg h1, if_neg h2])
  have hma : denoteAtomExpr ["in"] I (ImpExpr.var "ma") = fun ρ' => ρ' "ma" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("in":String) ≠ "ma" by decide)]
  have hmb : denoteAtomExpr ["in"] I (ImpExpr.var "mb") = fun ρ' => ρ' "mb" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("in":String) ≠ "mb" by decide)]
  have hmc : denoteAtomExpr ["in"] I (ImpExpr.var "mc") = fun ρ' => ρ' "mc" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("in":String) ≠ "mc" by decide)]
  have hmx : denoteAtomExpr ["in"] I (ImpExpr.var "mx") = fun ρ' => ρ' "mx" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("in":String) ≠ "mx" by decide)]
  simp only [majBlock, ImpExpr.denoteScalar, recogBin, JasminBinOp.apply, reduceIte,
    String.reduceEq, or_self, ea0, eb0, ea1, ec1, eb2, ec2, hma,
    hmb, hmc, hmx, majFn, Option.bind_some, Option.map_some, if_true]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxCompress
