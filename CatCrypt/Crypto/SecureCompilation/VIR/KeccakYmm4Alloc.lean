/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.YmmSelect
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit

/-!
# Four-way Keccak-p[1600,24] over allocated YMM registers

The 24-round permutation of four independent Keccak states at once, one state
per 64-bit lane of each `%ymm` register, written as a `List YmmInstr` over
virtual lane names and placed in registers by `YmmRegAlloc`. No register or
stack slot is chosen by hand: the program names values, the allocator decides
which live in registers, and the rest are spilled to 32-byte frame cells, a cell
being shared by spilled names whose live ranges are disjoint. The AVX2 render
allocates over `%ymm0 .. %ymm12`; the selected render, which needs AVX-512VL,
allocates over `%ymm0 .. %ymm12` and `%ymm16 .. %ymm31`.

Names are single-assignment per round (`a{r}_{x}{y}` is lane `(x, y)` entering
round `r`), so each value's live range is at most about a round. One name reused
across all 24 rounds would be live for the whole permutation, and every such
name would conflict with every other.

ρ∘π and χ are emitted one χ row at a time: the five `B` lanes a row reads are
computed immediately before it, which keeps fewer `B` lanes live at once than
computing all 25 first.

## Layout and ABI

`keccak_f1600_x4(uint64_t *out, const uint64_t *in)` with the state in
struct-of-arrays order: word `4·i + s` is lane `i = x + 5y` of state `s`, so lane
`i` of all four states is the 32 bytes at offset `32·i`. The round constants are
a `.rodata` table of 24 rows, each constant repeated in all four lanes, addressed
through `%rcx`.

## Main definitions

* `keccakYmm4Body`: the permutation over virtual names.
* `keccakYmm4Program`: the body, optionally passed through `YmmSelect.selectYmm`.
* `keccakYmm4Asm`: allocation, materialization and the AT&T text.
* `keccakYmm4Stats`: instruction and memory-access counts of the rendered kernel.
* `keccakYmm4Checks`: EVEX spellability and frame-cell disjointness of the kernel.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakYmm4Alloc

open CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
open CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.YmmSelect
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
open CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-! ## 1. Names -/

/-- FIPS 202 lane index. -/
def li (x y : Nat) : Nat := x + 5 * y

/-- Lane `(x, y)` entering round `r`. -/
def aN (r x y : Nat) : String := s!"a{r}_{x}{y}"
/-- Lane `(x, y)` after θ in round `r`. -/
def eN (r x y : Nat) : String := s!"e{r}_{x}{y}"
/-- Column parity `C[x]` of round `r`. -/
def cN (r x : Nat) : String := s!"c{r}_{x}"
/-- θ correction `D[x]` of round `r`. -/
def dN (r x : Nat) : String := s!"d{r}_{x}"
/-- ρ∘π output lane `B[x, y]` of round `r`. -/
def bN (r x y : Nat) : String := s!"b{r}_{x}{y}"

/-- The lane `(x, y)` whose ρ-rotation lands at `B[x', y']` under π, the inverse
    of `(x, y) ↦ (y, 2x + 3y mod 5)`: `y = x'` and `x = 3·(y' − 3x') mod 5`,
    3 being the inverse of 2 modulo 5. -/
def piSrc (x' y' : Nat) : Nat × Nat := ((3 * ((y' + 15 - 3 * x') % 5)) % 5, x')

/-! ## 2. The round -/

/-- `dst := src` rotated left by `k`, as the shift-shift-or triple over fresh
    temporaries `tag ++ "l"` and `tag ++ "r"`. A rotation by a multiple of 64 is a
    move. `YmmSelect.selectYmm` recognises the triple. -/
def rotl (dst src : String) (k : Nat) (tag : String) : List YmmInstr :=
  if k % 64 == 0 then [.ymov dst src]
  else
    [ .alu (.vpsllq k) (tag ++ "l") [src]
    , .alu (.vpsrlq (64 - k)) (tag ++ "r") [src]
    , .alu .vpor dst [tag ++ "l", tag ++ "r"] ]

/-- θ: the five column parities, the five corrections, and the correction
    folded into every lane. -/
def theta (r : Nat) : List YmmInstr :=
  let cs := (List.range 5).flatMap (fun x =>
    [ .alu .vpxor s!"c{r}_{x}_0" [aN r x 0, aN r x 1]
    , .alu .vpxor s!"c{r}_{x}_1" [s!"c{r}_{x}_0", aN r x 2]
    , .alu .vpxor s!"c{r}_{x}_2" [s!"c{r}_{x}_1", aN r x 3]
    , .alu .vpxor (cN r x) [s!"c{r}_{x}_2", aN r x 4] ])
  let ds := (List.range 5).flatMap (fun x =>
    rotl s!"q{r}_{x}" (cN r ((x + 1) % 5)) 1 s!"qt{r}_{x}"
      ++ [ .alu .vpxor (dN r x) [cN r ((x + 4) % 5), s!"q{r}_{x}"] ])
  let es := (List.range 25).map (fun i =>
    let x := i % 5; let y := i / 5
    .alu .vpxor (eN r x y) [aN r x y, dN r x])
  cs ++ ds ++ es

/-- ρ∘π and χ, one χ row at a time. Lane `(0, 0)` of the χ output is written to
    `z{r}` so that ι can produce `a{r+1}_00`. -/
def rhoPiChi (r : Nat) : List YmmInstr :=
  (List.range 5).flatMap (fun y' =>
    let bs := (List.range 5).flatMap (fun x' =>
      let p := piSrc x' y'
      rotl (bN r x' y') (eN r p.1 p.2) (rhoOffset (li p.1 p.2)) s!"rp{r}_{x'}{y'}")
    let chis := (List.range 5).flatMap (fun x' =>
      let out := if x' == 0 && y' == 0 then s!"z{r}" else aN (r + 1) x' y'
      [ .alu .vpandn s!"n{r}_{x'}{y'}" [bN r ((x' + 1) % 5) y', bN r ((x' + 2) % 5) y']
      , .alu .vpxor out [bN r x' y', s!"n{r}_{x'}{y'}"] ])
    bs ++ chis)

/-- The base register of the round-constant table. -/
def rcBase : String := "%rcx"

/-- ι: the round constant, broadcast to all four lanes, XORed into lane (0, 0). -/
def iota (r : Nat) : List YmmInstr :=
  [ .yload s!"rc{r}" ⟨rcBase, (32 * r : Nat)⟩
  , .alu .vpxor (aN (r + 1) 0 0) [s!"z{r}", s!"rc{r}"] ]

/-- One round. -/
def round (r : Nat) : List YmmInstr := theta r ++ rhoPiChi r ++ iota r

/-- The 25 lanes loaded from the input. -/
def loadState : List YmmInstr :=
  (List.range 25).map (fun i => .yload (aN 0 (i % 5) (i / 5)) ⟨"%rsi", (32 * i : Nat)⟩)

/-- The 25 lanes stored to the output. -/
def storeState : List YmmInstr :=
  (List.range 25).map (fun i => .ystore ⟨"%rdi", (32 * i : Nat)⟩ (aN 24 (i % 5) (i / 5)))

/-- The permutation over virtual names. -/
def keccakYmm4Body : List YmmInstr :=
  loadState ++ (List.range 24).flatMap round ++ storeState

/-- The program handed to the allocator: the body, or the body after vector
    instruction selection, which fuses the rotate triples into `vprolq` and the
    χ pairs into `vpternlogq`. -/
def keccakYmm4Program (select : Bool) : List YmmInstr :=
  if select then selectYmm keccakYmm4Body else keccakYmm4Body

/-- Instruction selection leaves the memory the body writes unchanged: the
    program, selected or not, ends with the memory `keccakYmm4Body` ends with,
    and so stores the same output lanes. -/
theorem keccakYmm4Program_mem (select : Bool) (s : YmmState) :
    (ymmRun (keccakYmm4Program select) s).mem = (ymmRun keccakYmm4Body s).mem := by
  cases select
  · rfl
  · exact (selectYmm_sound keccakYmm4Body s).1

/-! ## 3. Allocation and the rendered kernel -/

/-- The candidate scratch registers for spilled operands, withheld from
    allocation from the front as `ymmAllocFewestScratch` needs them.
    `vpternlogq` reads three names, so at most three are needed. -/
def scratchRegs : List String := ["%ymm13", "%ymm14", "%ymm15"]

/-- The register file of a render: the sixteen AVX2 registers, or the
    thirty-two AVX-512VL registers for the selected program, which already
    requires AVX-512VL for `vprolq` and `vpternlogq`. -/
def regFile (select : Bool) : List String :=
  if select then evexYmmFile else ymmFile

/-- The live ranges of the program. -/
def ranges (select : Bool) : List LiveRange :=
  ymmLiveRanges (keccakYmm4Program select)

/-- The allocation of the program: linear scan over `regFile` withholding the
    fewest scratch registers its spills need, frame cells reused across
    disjoint live ranges. Returns the withheld registers and the decisions. -/
def allocation (select : Bool) : List String × List (String × Slot) :=
  ymmAllocFewestScratch (regFile select) [] scratchRegs 0
    (keccakYmm4Program select) (ranges select)

/-- The scratch registers the allocation withholds. -/
def scratchUsed (select : Bool) : List String := (allocation select).1

/-- The allocator's decisions for the program. -/
def decisions (select : Bool) : List (String × Slot) := (allocation select).2

/-- The program with every name placed in a physical register. -/
def materialized (select : Bool) : List YmmInstr :=
  let a := allocation select
  ymmMaterialize a.2 a.1 (keccakYmm4Program select)

/-- Bytes of stack frame the spilled values occupy. -/
def frameBytes (select : Bool) : Nat := frameExtent 0 (decisions select)

/-- The symbol the kernel exports. -/
def symbol : String := "keccak_f1600_x4"

/-- The round-constant table: 24 rows of the constant repeated four times. -/
def rcTable : List String :=
  (List.range 24).map (fun r =>
    let c := toString (roundConst r)
    "\t.quad\t" ++ c ++ ", " ++ c ++ ", " ++ c ++ ", " ++ c)

/-- The AT&T text of the kernel. The frame is allocated below `%rsp`, aligned to
    32 bytes, and restored from `%r10`, which no vector instruction touches;
    `%rax` returns the output pointer. -/
def keccakYmm4Asm (select : Bool) : String :=
  let body := (materialized select).map renderYmmInstrEvex
  let pre :=
    [ "\t.att_syntax", "\t.text", "\t.p2align\t5"
    , "\t.globl\t" ++ symbol, "\t.type\t" ++ symbol ++ ", @function"
    , symbol ++ ":"
    , "\tmovq\t%rsp, %r10"
    , "\tsubq\t$" ++ toString (frameBytes select + 32) ++ ", %rsp"
    , "\tandq\t$-32, %rsp"
    , "\tleaq\t.LKRC(%rip), " ++ rcBase ]
  let post :=
    [ "\tmovq\t%r10, %rsp", "\tvzeroupper", "\tmovq\t%rdi, %rax", "\tret"
    , "\t.size\t" ++ symbol ++ ", .-" ++ symbol
    , "\t.section\t.rodata", "\t.p2align\t5", ".LKRC:" ] ++ rcTable ++
    [ "\t.section\t.note.GNU-stack,\"\",@progbits" ]
  String.intercalate "\n" (pre ++ body ++ post) ++ "\n"

/-! ## 4. Counts of the rendered kernel -/

/-- Whether an instruction touches memory at `%rsp`: a spill or a reload. -/
def isStackAccess : YmmInstr → Bool
  | .yload _ m  => m.base == ymmFrameBase
  | .ystore m _ => m.base == ymmFrameBase
  | _ => false

/-- `(instructions, stack accesses, spilled names, resident names, scratch
    registers needed, every name physical)` of the kernel. -/
def keccakYmm4Stats (select : Bool) : Nat × Nat × Nat × Nat × Nat × Bool :=
  let m := materialized select
  let d := decisions select
  ( m.length, (m.filter isStackAccess).length, spillCount d, residentCount d
  , ymmScratchNeeded d (keccakYmm4Program select), ymmAllPhysicalIn (regFile select) m )

/-- `(the withheld scratch registers cover the spills, every instruction has an
    EVEX spelling, frame cells are shared only across disjoint live ranges)` for
    the kernel. -/
def keccakYmm4Checks (select : Bool) : Bool × Bool × Bool :=
  let a := allocation select
  ( ymmScratchNeeded a.2 (keccakYmm4Program select) ≤ a.1.length
  , (materialized select).all evexSpellable
  , slotsReuseDisjoint (ranges select) a.2 )

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakYmm4Alloc
