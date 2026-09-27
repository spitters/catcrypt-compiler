/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# Instruction builders of the Solinas field-multiply kernels

A Solinas field multiply over `n` 64-bit limbs is a dual-carry `MULX`/`ADCX`/`ADOX`
schoolbook product into a scratch frame `sp[0..2n-1]`, followed by a signed
combination of Solinas terms, each assembled from 32-bit half-words of the product
and added to or subtracted from an `(n+1)`-word two's-complement accumulator, a
number of sign-gated add-backs of the modulus, a number of trial subtracts of the
modulus with restore on borrow, and the store of the `n` low accumulator words to
`z`. This module defines the instruction builders of each piece for an arbitrary
limb count, and `solinasMulBlock S`, the whole block of a `SolinasShape S`.

The builders take the register window as a list. The half-word `d[i]` of the
product is the low (`i` even) or high (`i` odd) 32 bits of `sp[i / 2]`; index `64`
reads a zero half-word.

## Main definitions

* `packWord`, `buildTermG`, `buildTerm` — a Solinas term from half-word indices.
* `accAddG`, `accSubG` — an `n`-word term added to or subtracted from the accumulator.
* `condAddPG` — the sign-gated add-back of the modulus.
* `condSubP` — the trial subtract of the modulus, with the trial words in registers
  (`TrialLayout.regs`) or staged in the term words (`TrialLayout.staged`).
* `row0G`, `rowG`, `schoolbook` — the dual-carry schoolbook product.
* `SolinasShape`, `solinasReduce`, `solinasMulBlock` — a Solinas field multiply.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasKernel

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)

/-! ## 1. Term assembly from 32-bit half-words -/

/-- Load the 32-bit half-word `d[idx]` (zero-extended) into register `dst`. -/
def loadD (dst : String) (idx : Nat) : List (JInstr 64) :=
  let word := idx / 2
  if idx % 2 == 0 then
    [ .loadMem dst "sp" (8 * word), .mov "hi" (.imm 0xffffffff), .and_ dst (.reg "hi") ]
  else
    [ .loadMem dst "sp" (8 * word), .shr dst (.imm 32) ]

/-- Pack the half-words `(hiIdx, loIdx)` into `dst := d[hiIdx]·2^32 + d[loIdx]`, index
    `64` reading a zero half-word. -/
def packWord (dst : String) (hiIdx loIdx : Nat) : List (JInstr 64) :=
  (if loIdx == 64 then [ .mov dst (.imm 0) ] else loadD dst loIdx) ++
  (if hiIdx == 64 then [] else
    loadD "lo" hiIdx ++ [ .shl "lo" (.imm 32), .or_ dst (.reg "lo") ])

/-- One packed term word followed by its store to `sp[o]`. -/
def packStore (o : Int) (h l : Nat) : List (JInstr 64) :=
  packWord "w0" h l ++ [.storeMem "sp" o (.reg "w0")]

/-- The packed term words `sp[o + 8i] ← d[hᵢ]·2^32 + d[lᵢ]` for the index pairs `ps`
    (least significant first). -/
def buildTermG : List (Nat × Nat) → Int → List (JInstr 64)
  | [], _ => []
  | (h, l) :: ps, o => packStore o h l ++ buildTermG ps (o + 8)

/-- The index pairs of a half-word index list written most significant first,
    `[hₖ, lₖ, …, h₀, l₀]`, prepended in reverse to `acc`. -/
def idxPairsAux : List Nat → List (Nat × Nat) → List (Nat × Nat)
  | h :: l :: rest, acc => idxPairsAux rest ((h, l) :: acc)
  | _, acc => acc

/-- The index pairs `[(h₀, l₀), …, (hₖ, lₖ)]` (least significant first) of the
    half-word index list `[hₖ, lₖ, …, h₀, l₀]` (most significant first). -/
def idxPairs (idx : List Nat) : List (Nat × Nat) := idxPairsAux idx []

/-- The term with half-word indices `idx` (most significant first) stored at
    `sp[slot]`. -/
def buildTerm (slot : Int) (idx : List Nat) : List (JInstr 64) :=
  buildTermG (idxPairs idx) slot

/-! ## 2. The two's-complement accumulator

The accumulator words are loaded into the registers `r₀ :: rs`, the term words are
added (subtracted) through `lo` with one carry (borrow) chain, the chain's carry is
folded into the top accumulator word through `top`, and all words are stored back. -/

/-- The load-and-`ADC` chain over the registers `rs`. -/
def adcChain : List String → Int → Int → List (JInstr 64)
  | [], _, _ => []
  | r :: rs, a, t =>
      [.loadMem r "sp" a, .loadMem "lo" "sp" t, .adc r (.reg "lo")]
        ++ adcChain rs (a + 8) (t + 8)

/-- The load-and-`SBB` chain over the registers `rs`. -/
def sbbChain : List String → Int → Int → List (JInstr 64)
  | [], _, _ => []
  | r :: rs, a, t =>
      [.loadMem r "sp" a, .loadMem "lo" "sp" t, .sbb r (.reg "lo")]
        ++ sbbChain rs (a + 8) (t + 8)

/-- The stores of the registers `rs` to consecutive words from `sp[a]`. -/
def storeChain : List String → Int → List (JInstr 64)
  | [], _ => []
  | r :: rs, a => .storeMem "sp" a (.reg r) :: storeChain rs (a + 8)

/-- The loads of consecutive words from `sp[a]` into the registers `rs`. -/
def loadChain : List String → Int → List (JInstr 64)
  | [], _ => []
  | r :: rs, a => .loadMem r "sp" a :: loadChain rs (a + 8)

/-- The accumulate of the `rs.length + 1` term words at `t` into the `rs.length + 2`
    accumulator words at `a`. -/
def accAddG (r0 : String) (rs : List String) (top : String) (a t : Int) : List (JInstr 64) :=
  [.loadMem r0 "sp" a, .loadMem "lo" "sp" t, .add r0 (.reg "lo")] ++ adcChain rs (a + 8) (t + 8)
    ++ [.loadMem top "sp" (a + 8 * ((rs.length + 1 : Nat) : Int)), .adc top (.imm 0)]
    ++ storeChain (r0 :: rs ++ [top]) a

/-- The subtract of the `rs.length + 1` term words at `t` from the `rs.length + 2`
    accumulator words at `a`. -/
def accSubG (r0 : String) (rs : List String) (top : String) (a t : Int) : List (JInstr 64) :=
  [.loadMem r0 "sp" a, .loadMem "lo" "sp" t, .sub r0 (.reg "lo")] ++ sbbChain rs (a + 8) (t + 8)
    ++ [.loadMem top "sp" (a + 8 * ((rs.length + 1 : Nat) : Int)), .sbb top (.imm 0)]
    ++ storeChain (r0 :: rs ++ [top]) a

/-- The clear of the `n` words from `sp[a]` through the register `r`. -/
def zeroAcc (r : String) (n : Nat) (a : Int) : List (JInstr 64) :=
  .mov r (.imm 0) :: storeChain (List.replicate n r) a

/-! ## 3. The sign-gated add-back of the modulus

The arithmetic shift of the top accumulator word gives a mask in `y`, the masked
limbs are stored in the term words (before the carry chain, since `AND` clears `CF`),
and an accumulate adds them. -/

/-- The masked limb stores `sp[t + 8i] ← Lᵢ & y`. -/
def maskChain : List Nat → Int → List (JInstr 64)
  | [], _ => []
  | L :: Ls, t =>
      [.mov "lo" (.imm L), .and_ "lo" (.reg "y"), .storeMem "sp" t (.reg "lo")]
        ++ maskChain Ls (t + 8)

/-- The mask prefix of the add-back: `y ← sar(sp[a + 8·n], 63)` for `n` limbs, then the
    masked limbs at `t`. -/
def condAddMaskG (limbs : List Nat) (a t : Int) : List (JInstr 64) :=
  [.loadMem "hi" "sp" (a + 8 * (limbs.length : Int)), .mov "y" (.reg "hi"), .sar "y" (.imm 63)]
    ++ maskChain limbs t

/-- The sign-gated add-back of the modulus with limbs `limbs`. -/
def condAddPG (limbs : List Nat) (r0 : String) (rs : List String) (top : String) (a t : Int) :
    List (JInstr 64) :=
  condAddMaskG limbs a t ++ accAddG r0 rs top a t

/-! ## 4. The trial subtract of the modulus

The accumulator words are loaded into the window and `y`, the modulus limbs are
subtracted from copies with one borrow chain that runs through the top word, and
`CMOVB` restores the originals when the final borrow is set. The trial words are kept
either in registers or in the term words. -/

/-- Where the trial subtract keeps its trial words. -/
inductive TrialLayout where
  /-- In the registers `ds`, one per limb. -/
  | regs (ds : List String)
  /-- In the term words. -/
  | staged

/-- The `SBB` steps of the register trial: `dᵢ ← rᵢ − Lᵢ − CF`. -/
def trialRegsTail : List String → List String → List Nat → List (JInstr 64)
  | r :: rs, d :: ds, L :: Ls =>
      [.mov d (.reg r), .mov "hi" (.imm L), .sbb d (.reg "hi")] ++ trialRegsTail rs ds Ls
  | _, _, _ => []

/-- The register trial: `d₀ ← r₀ − L₀`, then the `SBB` steps. -/
def trialRegs : List String → List String → List Nat → List (JInstr 64)
  | r :: rs, d :: ds, L :: Ls =>
      [.mov d (.reg r), .mov "hi" (.imm L), .sub d (.reg "hi")] ++ trialRegsTail rs ds Ls
  | _, _, _ => []

/-- The restores `dᵢ ← rᵢ` on borrow. -/
def cmovChain : List String → List String → List (JInstr 64)
  | d :: ds, r :: rs => .cmovb d (.reg r) :: cmovChain ds rs
  | _, _ => []

/-- The `SBB` steps of the staged trial: `sp[t + 8i] ← rᵢ − Lᵢ − CF` through `lo`. -/
def trialStagedTail : List String → List Nat → Int → List (JInstr 64)
  | r :: rs, L :: Ls, t =>
      [.mov "lo" (.reg r), .mov "hi" (.imm L), .sbb "lo" (.reg "hi"), .storeMem "sp" t (.reg "lo")]
        ++ trialStagedTail rs Ls (t + 8)
  | _, _, _ => []

/-- The staged trial: `sp[t] ← r₀ − L₀`, then the `SBB` steps. -/
def trialStaged : List String → List Nat → Int → List (JInstr 64)
  | r :: rs, L :: Ls, t =>
      [.mov "lo" (.reg r), .mov "hi" (.imm L), .sub "lo" (.reg "hi"), .storeMem "sp" t (.reg "lo")]
        ++ trialStagedTail rs Ls (t + 8)
  | _, _, _ => []

/-- The staged restores `sp[a + 8i] ← (CF ? rᵢ : sp[t + 8i])` through `hi`. -/
def restoreStaged : List String → Int → Int → List (JInstr 64)
  | [], _, _ => []
  | r :: rs, t, a =>
      [.loadMem "hi" "sp" t, .cmovb "hi" (.reg r), .storeMem "sp" a (.reg "hi")]
        ++ restoreStaged rs (t + 8) (a + 8)

/-- The trial subtract of the modulus with limbs `limbs` from the `rs.length + 2`
    accumulator words at `a`, window `r0 :: rs`, top word through `y`, term words at
    `t` (read only by the staged layout). -/
def condSubP (L : TrialLayout) (limbs : List Nat) (r0 : String) (rs : List String)
    (a t : Int) : List (JInstr 64) :=
  let top : Int := a + 8 * ((rs.length + 1 : Nat) : Int)
  loadChain (r0 :: rs ++ ["y"]) a ++
  match L with
  | .regs ds =>
      trialRegs (r0 :: rs) ds limbs ++ [.sbb "y" (.imm 0)] ++ cmovChain ds (r0 :: rs)
        ++ [.loadMem r0 "sp" top, .cmovb "y" (.reg r0)] ++ storeChain (ds ++ ["y"]) a
  | .staged =>
      trialStaged (r0 :: rs) limbs t ++ [.sbb "y" (.imm 0)] ++ restoreStaged (r0 :: rs) t a
        ++ [.loadMem r0 "sp" top, .cmovb "y" (.reg r0), .storeMem "sp" top (.reg "y")]

/-! ## 5. The dual-carry schoolbook product

Row `j` over the window `r₀, r₁, …, r_{n-1}`: `yd ← y[yo]`, column `0` accumulates
`yd · x[0]` into `r₀, r₁` and stores the finished word `r₀` at `sp[so]`, columns
`1 … n−2` accumulate `yd · x[k]` into `rₖ, rₖ₊₁`, the last column writes the high
product word into `r₀`, and the two pending carries are folded into `r₀`. Row `0`
fills the window on a single `CF` chain. -/

/-- Columns `1 … n−1` of a dual-carry row over `r :: rs`. -/
def rowTail (r0 : String) : List String → Int → List (JInstr 64)
  | [], _ => []
  | [r], xo => [.mulxMem r0 "lo" (.reg "yd") "x" xo, .adcx r (.reg "lo")]
  | r :: r' :: rs, xo =>
      [.mulxMem "hi" "lo" (.reg "yd") "x" xo, .adcx r (.reg "lo"), .adox r' (.reg "hi")]
        ++ rowTail r0 (r' :: rs) (xo + 8)

/-- A dual-carry row over the window `r0 :: r1 :: rs`, multiplier `y[yo]`, finished
    word stored at `sp[so]`. -/
def rowG (r0 r1 : String) (rs : List String) (yo so : Int) : List (JInstr 64) :=
  [ .xor_ "zr" (.reg "zr"), .loadMem "yd" "y" yo
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0, .adcx r0 (.reg "lo"), .adox r1 (.reg "hi")
  , .storeMem "sp" so (.reg r0) ]
  ++ rowTail r0 (r1 :: rs) 8 ++ [.adox r0 (.reg "zr"), .adcx r0 (.reg "zr")]

/-- Columns `1 … n−1` of the first row over `r :: rs`. -/
def row0Tail (r0 : String) : List String → Int → List (JInstr 64)
  | [], _ => []
  | [r], xo => [.mulxMem r0 "lo" (.reg "yd") "x" xo, .adcx r (.reg "lo")]
  | r :: r' :: rs, xo =>
      [.mulxMem r' "lo" (.reg "yd") "x" xo, .adcx r (.reg "lo")]
        ++ row0Tail r0 (r' :: rs) (xo + 8)

/-- The first schoolbook row over the window `r0 :: r1 :: rs`. -/
def row0G (r0 r1 : String) (rs : List String) (yo so : Int) : List (JInstr 64) :=
  [ .mov "zr" (.imm 0), .xor_ "zr" (.reg "zr"), .loadMem "yd" "y" yo
  , .mulxMem r1 r0 (.reg "yd") "x" 0, .storeMem "sp" so (.reg r0) ]
  ++ row0Tail r0 (r1 :: rs) 8 ++ [.adcx r0 (.reg "zr")]

/-- Rows `j, j+1, …, j+k−1`: row `i` over the window `w` rotated left by `i`, multiplier
    `y[8i]`, finished word at `sp[8i]`. -/
def schoolbookRows (w : List String) (j : Nat) : Nat → List (JInstr 64)
  | 0 => []
  | k + 1 =>
      (match w.rotateLeft j with
        | r0 :: r1 :: rs => rowG r0 r1 rs (8 * (j : Int)) (8 * (j : Int))
        | _ => [])
        ++ schoolbookRows w (j + 1) k

/-- The `n × n` schoolbook product of `x[0..n-1]` and `y[0..n-1]` into `sp[0..2n-1]`
    over the window `r0 :: r1 :: rs` (`n = rs.length + 2`): the first row, rows
    `1 … n−1`, and the stores of the `n` high words. -/
def schoolbook (r0 r1 : String) (rs : List String) : List (JInstr 64) :=
  row0G r0 r1 rs 0 0 ++ schoolbookRows (r0 :: r1 :: rs) 1 (rs.length + 1)
    ++ storeChain (r0 :: r1 :: rs) (8 * ((rs.length + 2 : Nat) : Int))

/-! ## 6. The whole block -/

/-- The data of a Solinas field-multiply kernel over `n = rs.length + 2` limbs. -/
structure SolinasShape where
  /-- The window registers `r0 :: r1 :: rs`. -/
  r0 : String
  r1 : String
  rs : List String
  /-- Byte offset of the `n` term words in the scratch frame. -/
  termOff : Nat
  /-- Byte offset of the `n + 1` accumulator words in the scratch frame. -/
  accOff : Nat
  /-- The Solinas terms: half-word indices (most significant first) and the signed
      multiplicity with which each is accumulated. -/
  terms : List (List Nat × Int)
  /-- The modulus limbs, least significant first. -/
  modLimbs : List Nat
  /-- The number of sign-gated add-backs. -/
  addBacks : Nat
  /-- The number of trial subtracts. -/
  trialSubs : Nat
  /-- Where the trial subtract keeps its trial words. -/
  trial : TrialLayout

namespace SolinasShape

variable (S : SolinasShape)

/-- The accumulate of the term words into the accumulator. -/
def accAdd : List (JInstr 64) := accAddG S.r0 (S.r1 :: S.rs) "hi" S.accOff S.termOff

/-- The subtract of the term words from the accumulator. -/
def accSub : List (JInstr 64) := accSubG S.r0 (S.r1 :: S.rs) "hi" S.accOff S.termOff

/-- The sign-gated add-back of the modulus. -/
def condAdd : List (JInstr 64) := condAddPG S.modLimbs S.r0 (S.r1 :: S.rs) "hi" S.accOff S.termOff

/-- The trial subtract of the modulus. -/
def condSub : List (JInstr 64) := condSubP S.trial S.modLimbs S.r0 (S.r1 :: S.rs) S.accOff S.termOff

end SolinasShape

/-- `k` copies of the block `b`. -/
def repeatBlock (b : List (JInstr 64)) : Nat → List (JInstr 64)
  | 0 => []
  | k + 1 => b ++ repeatBlock b k

/-- The term `idx` assembled at the term words, then accumulated `c` times (`c ≥ 0`) or
    subtracted `−c` times (`c < 0`). -/
def termStep (S : SolinasShape) (idx : List Nat) (c : Int) : List (JInstr 64) :=
  buildTerm S.termOff idx
    ++ if 0 ≤ c then repeatBlock S.accAdd c.toNat else repeatBlock S.accSub c.natAbs

/-- The term steps of the terms `ts`. -/
def termSteps (S : SolinasShape) : List (List Nat × Int) → List (JInstr 64)
  | [] => []
  | (idx, c) :: ts => termStep S idx c ++ termSteps S ts

/-- The loads of consecutive words from `sp[a]` into the registers `rs`, each stored to
    the corresponding word of `z` from `z[o]`. -/
def outChain : List String → Int → Int → List (JInstr 64)
  | [], _, _ => []
  | r :: rs, a, o => [.loadMem r "sp" a, .storeMem "z" o (.reg r)] ++ outChain rs (a + 8) (o + 8)

/-- The reduce of a Solinas kernel: clear the accumulator, the term steps, the
    add-backs, the trial subtracts, and the store of the `n` low accumulator words to
    `z`. -/
def solinasReduce (S : SolinasShape) : List (JInstr 64) :=
  zeroAcc S.r0 (S.rs.length + 3) S.accOff ++ termSteps S S.terms
    ++ repeatBlock S.condAdd S.addBacks ++ repeatBlock S.condSub S.trialSubs
    ++ outChain (S.r0 :: S.r1 :: S.rs) S.accOff 0

/-- The Solinas field multiply of `S`: the schoolbook product into the scratch frame,
    then the reduce. -/
def solinasMulBlock (S : SolinasShape) : List (JInstr 64) :=
  schoolbook S.r0 S.r1 S.rs ++ solinasReduce S

end CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasKernel
