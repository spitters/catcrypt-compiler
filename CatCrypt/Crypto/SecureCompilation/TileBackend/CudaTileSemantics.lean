/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.TileBackend.TileDialectLower
public import CatCrypt.Crypto.SecureCompilation.TileBackend.TileDialectLower
public import CatCrypt.Crypto.SecureCompilation.TileBackend.TileArithCorrect
import Std.Data.String.ToInt
import Std.Data.String.ToNat

/-!
# The `cuda_tile` text of the tile backend and its meaning

`ComToTileIR.emitTileFuncAt n w` prints a `TileModel.TileOp` block as a kernel in
the NVIDIA CUDA Tile IR (`cuda_tile` MLIR dialect). This module gives that text
fragment an AST (`Func`), a printer (`Func.print`), a parser (`parse`) and a
semantics (`Func.run`) in which each operation means what the CUDA Tile IR
specification (https://docs.nvidia.com/cuda/tile-ir/latest/sections/operations.html)
states. The semantics (`Mn.sem`, `Sgn.sem`, `Instr.exec`, `Func.run`) is the
trusted part.

A kernel reads its input tiles through pointer arguments and writes its result
through a third, so `Func.run` is a function from a memory of `i w` elements and
three pointers to the final memory.

## Main results

* `emitTileFuncAt_eq_print`: `emitTileFuncAt n w name body res` is the printed text
  of `toAst n w name body res`, for every block and shape; `emitTileFunc_eq_print`
  at `8xi64`.
* `parse_print`: `parse f.print = some f` for every AST whose kernel name consists
  of symbol characters; `print_injective`.
* `mulhs_eq_mulhu_sub`: the signed high half is the unsigned high half minus the
  two sign corrections, the identity the emitted `mulhs` sequence computes.
* `run_toAst`: for a block satisfying `SupportedFunc` at a shape satisfying
  `ShapeOk`, the kernel launched on a memory holding the tiles of registers `a` and
  `b` of a state stores the value `runTileBlock` leaves in the result register and
  leaves the rest of memory unchanged. `emitTileFunc?_eq_some`: the checked emitter
  accepts every such block.
* `parse_bbMulTileComIR`, `bbMulAst_run`, `bbMulTileComIR_correct`: the emitted
  BabyBear text parses to `bbMulAst`, which stores `bbMulWord` of the loaded lanes,
  hence `x · y mod p` for lanes below `p`.

## Scope

* The lane-moving ops `permxv`, `bcast`, `hadd`, `shuffle`, `blend`, the immediate
  `shl`, `sar`, `rotl`, `rotr` and `mulhu` have no printed form; a block with one is
  not `Supported`, and `emitTileFunc?` rejects it.
* `Func.run` is the effect of one tile block. Memory is addressed in elements, and
  pointer arithmetic is on unbounded naturals: the specification's undefined
  results on pointer overflow (§9.3.13) are not modelled.
* The text is not checked by the `cuda-tile` toolchain in this package.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.CudaTileSemantics

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
  (Tile TileState TileOp evalTileOp runTileBlock bbMulWord bbMulInit)
open CatCrypt.Crypto.SecureCompilation.TileBackend.ComToTileIR
  (St emitTileOp emitTileFuncAt emitTileFunc tileTyAt ptrTyAt ptrTileTyAt idxTyAt constLine binLine
    shriLine loadPrologue kernelOpen storeHead storeTail laneMoving emitTileFunc?)

/-! ## 1. Syntax -/

/-- An SSA operand of a body line: the loaded tiles `%a`, `%b`, an op result
    `%v<k>`, or `%undef` (the text printed for a register that no earlier op or
    load defines). -/
inductive Opnd where
  | a
  | b
  | v (k : Nat)
  | undef
  deriving DecidableEq, Repr

/-- The mnemonics of the two-operand forms `%r = cuda_tile.<mn> %x, %y : ty`. -/
inductive Mn where
  | addi
  | subi
  | muli
  | andi
  | ori
  | xori
  | shli
  | mulhii
  deriving DecidableEq, Repr

/-- The signedness keyword of `cuda_tile.shri`. -/
inductive Sgn where
  | signed
  | unsigned
  deriving DecidableEq, Repr

/-- One body line. -/
inductive Instr where
  /-- `%v<res> = cuda_tile.constant <i w: val> : ty` -/
  | const (res : Nat) (val : Int)
  /-- `%v<res> = cuda_tile.<mn> %x, %y : ty` -/
  | bin (mn : Mn) (res : Nat) (x y : Opnd)
  /-- `%v<res> = cuda_tile.shri %x, %y <sg> : ty` -/
  | shri (sg : Sgn) (res : Nat) (x y : Opnd)
  deriving DecidableEq, Repr

/-- A kernel over the tile type `ty = !cuda_tile.tile<n x i w>`: the module and
    entry `name` with pointer arguments `%pa`, `%pb`, `%pr`, the loads of `%a` and
    `%b`, the body lines, and the store of `ret` through `%pr`. -/
structure Func where
  name : String
  n : Nat
  w : Nat
  body : List Instr
  ret : Opnd
  deriving DecidableEq, Repr

/-! ## 2. Printer -/

/-- The text of an operand. -/
def Opnd.print : Opnd → String
  | .a => "%a"
  | .b => "%b"
  | .v k => "%v" ++ toString k
  | .undef => "%undef"

/-- The text of a mnemonic. -/
def Mn.name : Mn → String
  | .addi => "addi"
  | .subi => "subi"
  | .muli => "muli"
  | .andi => "andi"
  | .ori => "ori"
  | .xori => "xori"
  | .shli => "shli"
  | .mulhii => "mulhii"

/-- The text of a signedness keyword. -/
def Sgn.name : Sgn → String
  | .signed => "signed"
  | .unsigned => "unsigned"

/-- The result name `%v<k>`. -/
def vName (k : Nat) : String := "%v" ++ toString k

/-- The text of one body line at tile type `tileTyAt n w`. -/
def Instr.print (n w : Nat) : Instr → String
  | .const r k => constLine n w (vName r) k
  | .bin mn r x y => binLine n w mn.name (vName r) x.print y.print
  | .shri sg r x y => shriLine n w sg.name (vName r) x.print y.print

/-- The text of a kernel. -/
def Func.print (f : Func) : String :=
  kernelOpen f.n f.w f.name ++ String.join (f.body.map fun i => i.print f.n f.w ++ "\n")
    ++ storeHead ++ f.ret.print ++ storeTail f.n f.w

/-! ## 3. Translation of a `TileOp` block -/

/-- Translation state: the register-to-operand map, the next result index, and the
    lines emitted so far, in order. -/
structure TSt where
  map : List (String × Opnd)
  ctr : Nat
  out : List Instr

/-- The operand a register reads: its bound operand, or `undef`. -/
def TSt.opnd (s : TSt) (nm : String) : Opnd := (s.map.lookup nm).getD .undef

/-- Emit one line with result `%v<ctr>` and bind register `d` to it. -/
def TSt.push (s : TSt) (d : String) (i : Instr) : TSt :=
  { map := (d, .v s.ctr) :: s.map, ctr := s.ctr + 1, out := s.out ++ [i] }

/-- The lines `emitTileOp n w` prints for one op, as AST. -/
def trOp (w : Nat) (s : TSt) : TileOp → TSt
  | .const d k => s.push d (.const s.ctr k)
  | .add d a b => s.push d (.bin .addi s.ctr (s.opnd a) (s.opnd b))
  | .sub d a b => s.push d (.bin .subi s.ctr (s.opnd a) (s.opnd b))
  | .mul d a b => s.push d (.bin .muli s.ctr (s.opnd a) (s.opnd b))
  | .and d a b => s.push d (.bin .andi s.ctr (s.opnd a) (s.opnd b))
  | .orr d a b => s.push d (.bin .ori s.ctr (s.opnd a) (s.opnd b))
  | .xorr d a b => s.push d (.bin .xori s.ctr (s.opnd a) (s.opnd b))
  | .shll d a b => s.push d (.bin .shli s.ctr (s.opnd a) (s.opnd b))
  | .shrr d a b => s.push d (.shri .unsigned s.ctr (s.opnd a) (s.opnd b))
  | .andn d a b =>
      { map := (d, .v (s.ctr + 2)) :: s.map, ctr := s.ctr + 3,
        out := s.out ++ [.const s.ctr (-1), .bin .xori (s.ctr + 1) (s.opnd a) (.v s.ctr),
          .bin .andi (s.ctr + 2) (.v (s.ctr + 1)) (s.opnd b)] }
  | .shr d a imm =>
      { map := (d, .v (s.ctr + 1)) :: s.map, ctr := s.ctr + 2,
        out := s.out ++ [.const s.ctr imm, .shri .unsigned (s.ctr + 1) (s.opnd a) (.v s.ctr)] }
  | .mulhs d a b =>
      { map := (d, .v (s.ctr + 7)) :: s.map, ctr := s.ctr + 8,
        out := s.out ++ [.const s.ctr (w - 1 : Nat),
          .shri .signed (s.ctr + 1) (s.opnd a) (.v s.ctr),
          .shri .signed (s.ctr + 2) (s.opnd b) (.v s.ctr),
          .bin .mulhii (s.ctr + 3) (s.opnd a) (s.opnd b),
          .bin .andi (s.ctr + 4) (.v (s.ctr + 1)) (s.opnd b),
          .bin .andi (s.ctr + 5) (.v (s.ctr + 2)) (s.opnd a),
          .bin .subi (s.ctr + 6) (.v (s.ctr + 3)) (.v (s.ctr + 4)),
          .bin .subi (s.ctr + 7) (.v (s.ctr + 6)) (.v (s.ctr + 5))] }
  | .permxv d _ _ => { s with map := (d, .undef) :: s.map }
  | .bcast d _ _ => { s with map := (d, .undef) :: s.map }
  | .hadd d _ => { s with map := (d, .undef) :: s.map }
  | .shl d _ _ => { s with map := (d, .undef) :: s.map }
  | .sar d _ _ => { s with map := (d, .undef) :: s.map }
  | .rotl d _ _ => { s with map := (d, .undef) :: s.map }
  | .rotr d _ _ => { s with map := (d, .undef) :: s.map }
  | .mulhu d _ _ => { s with map := (d, .undef) :: s.map }
  | .shuffle d _ _ _ => { s with map := (d, .undef) :: s.map }
  | .blend d _ _ _ => { s with map := (d, .undef) :: s.map }

/-- The initial translation state: registers `a`, `b` bound to the loaded tiles. -/
def TSt.init : TSt := ⟨[("a", .a), ("b", .b)], 0, []⟩

/-- The AST of the kernel `emitTileFuncAt n w name body res` prints. -/
def toAst (n w : Nat) (name : String) (body : List TileOp) (res : String) : Func :=
  { name, n, w, body := (body.foldl (trOp w) TSt.init).out,
    ret := (body.foldl (trOp w) TSt.init).opnd res }

/-! ## 4. The emitter prints the AST -/

theorem lookup_cons_self {α : Type} (nm : String) (o : α) (l : List (String × α)) :
    List.lookup nm ((nm, o) :: l) = some o := by
  simp [List.lookup]

theorem lookup_cons_ne {α : Type} {nm k : String} (o : α) (l : List (String × α))
    (h : nm ≠ k) : List.lookup nm ((k, o) :: l) = List.lookup nm l := by
  have : (nm == k) = false := by simpa using h
  simp [List.lookup, this]

/-- The emitter state and the translation state agree: the emitter's register map
    is the printed operand map, the counters are equal, and the emitted lines are
    the printed AST lines. -/
def Rel (n w : Nat) (s : St) (t : TSt) : Prop :=
  s.map = t.map.map (fun p => (p.1, p.2.print)) ∧ s.ctr = t.ctr ∧
    s.lines.reverse = t.out.map (Instr.print n w)

theorem lookup_map_print (l : List (String × Opnd)) (nm : String) :
    (l.map (fun p => (p.1, p.2.print))).lookup nm = (l.lookup nm).map Opnd.print := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, o⟩ := p
    by_cases h : nm = k
    · subst h; simp only [List.map_cons, lookup_cons_self, Option.map_some]
    · simp only [List.map_cons, lookup_cons_ne _ _ h, ih]

theorem Rel.opnd {n w : Nat} {s : St} {t : TSt} (h : Rel n w s t) (nm : String) :
    (s.map.lookup nm).getD "%undef" = (t.opnd nm).print := by
  simp only [TSt.opnd, h.1, lookup_map_print]
  cases t.map.lookup nm <;> rfl

theorem Rel.step {n w : Nat} {s : St} {t : TSt} (h : Rel n w s t) (op : TileOp) :
    Rel n w (emitTileOp n w s op) (trOp w t op) := by
  obtain ⟨hm, hc, hl⟩ := h
  have ho := Rel.opnd ⟨hm, hc, hl⟩
  cases op <;>
    simp only [emitTileOp, emitTileOp.binOp, trOp, TSt.push, St.fresh, St.emit, St.bind,
      St.opnd, ho] <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    simp [hm, hc, hl, Instr.print, vName, Mn.name, Sgn.name, Opnd.print]

theorem foldl_rel {n w : Nat} (body : List TileOp) :
    ∀ (s : St) (t : TSt), Rel n w s t →
      Rel n w (body.foldl (emitTileOp n w) s) (body.foldl (trOp w) t) := by
  induction body with
  | nil => intro s t h; exact h
  | cons op body ih => intro s t h; exact ih _ _ (h.step op)

/-- **The emitter prints the AST.** `emitTileFuncAt n w name body res` is the
    printed text of `toAst n w name body res`, for every `TileOp` block and result
    register. -/
theorem emitTileFuncAt_eq_print (n w : Nat) (name : String) (body : List TileOp)
    (res : String) : emitTileFuncAt n w name body res = (toAst n w name body res).print := by
  have h := foldl_rel (n := n) (w := w) body St.init TSt.init
    ⟨rfl, rfl, rfl⟩
  unfold emitTileFuncAt toAst Func.print
  simp only [h.2.2, St.opnd, h.opnd res, List.map_map, Function.comp_def]

/-- `emitTileFunc name body res` is the printed text of `toAst 8 64 name body res`. -/
theorem emitTileFunc_eq_print (name : String) (body : List TileOp) (res : String) :
    emitTileFunc name body res = (toAst 8 64 name body res).print :=
  emitTileFuncAt_eq_print 8 64 name body res

/-! ## 5. Semantics -/

/-- The values of the SSA operands; `none` is an operand with no value. -/
abbrev Env (n w : Nat) := Opnd → Option (Tile n w)

/-- Define operand `o` to be the tile `t`. -/
def Env.set {n w : Nat} (ρ : Env n w) (o : Opnd) (t : Tile n w) : Env n w :=
  fun o' => if o' = o then some t else ρ o'

/-- The environment after the loads: `%a` is `x`, `%b` is `y`, no body result has a
    value. -/
def Env.init {n w : Nat} (x y : Tile n w) : Env n w
  | .a => some x
  | .b => some y
  | _ => none

/-- The high `w` bits of the `2w`-bit product of `x` and `y` read as unsigned. -/
def mulhu {w : Nat} (x y : BitVec w) : BitVec w := BitVec.ofNat w (x.toNat * y.toNat / 2 ^ w)

/-- The lane function of a two-operand mnemonic on `i w` lanes.

    Operations of the CUDA Tile IR specification
    (https://docs.nvidia.com/cuda/tile-ir/latest/sections/operations.html):
    * `addi` (§9.8.3, `#cuda-tile-addi`), `subi` (§9.8.15, `#cuda-tile-subi`),
      `muli` (§9.8.9, `#cuda-tile-muli`): the sum, difference and low product.
      The specification states "The default semantics are wrap-around semantics
      on overflow or underflow"; with the `overflow` attribute absent (its default
      is `none`) no no-wrap assumption is made, so each is the operation modulo
      `2^w`.
    * `mulhii` (§9.8.10, `#cuda-tile-mulhii`): "the most significant N bits of the
      2N-bit product of two N-bit integer tiles", "only defined for unsigned
      integers" (`mulhu`).
    * `andi` (§9.9.1), `ori` (§9.9.2), `xori` (§9.9.3): bitwise and, or, xor.
    * `shli` (§9.8.13, `#cuda-tile-shli`): `x << y`, zero-filled, with `y` read
      as unsigned. The specification does not state the result for `y ≥ w`; this
      semantics gives `0` (the lane function is `BitVec` shift by `y.toNat`), the
      result of the PTX `shl` instruction, which clamps shift amounts greater
      than the register width to the width. -/
def Mn.sem (w : Nat) : Mn → BitVec w → BitVec w → BitVec w
  | .addi => (· + ·)
  | .subi => (· - ·)
  | .muli => (· * ·)
  | .andi => (· &&& ·)
  | .ori => (· ||| ·)
  | .xori => (· ^^^ ·)
  | .shli => fun x y => x <<< y.toNat
  | .mulhii => mulhu

/-- The lane function of `shri` (§9.8.14, `#cuda-tile-shri`): `x >> y` with `y`
    read as unsigned; "When `unsigned`, higher-order bits are zero-filled; when
    `signed`, the higher-order bits are filled with the sign bit." For `y ≥ w` the
    result is the fill (not stated in the specification; the PTX `shr`
    instruction clamps the shift amount to the width). -/
def Sgn.sem {w : Nat} : Sgn → BitVec w → BitVec w → BitVec w
  | .signed => fun x y => x.sshiftRight y.toNat
  | .unsigned => fun x y => x >>> y.toNat

/-- One body line; `none` where a literal is out of range or an operand has no
    value.

    `constant` (§9.3.3, `#cuda-tile-constant`, "creates a tile initialized by
    $value"): the scalar literal `<i w: k>` at a tile type of shape `n` is the
    splat, every lane `BitVec.ofInt w k`; the `cuda-tile` parser accepts `k` in the
    range `[-2^(w-1), 2^w)` ("integer constant out of range for type" outside
    it), and this semantics is `none` outside that range. -/
def Instr.exec {n w : Nat} (ρ : Env n w) : Instr → Option (Env n w)
  | .const r k =>
      if -(2 ^ w : Int) ≤ 2 * k ∧ k < 2 ^ w then some (ρ.set (.v r) fun _ => BitVec.ofInt w k)
      else none
  | .bin mn r x y =>
      (ρ x).bind fun p => (ρ y).bind fun q => some (ρ.set (.v r) fun i => mn.sem w (p i) (q i))
  | .shri sg r x y =>
      (ρ x).bind fun p => (ρ y).bind fun q => some (ρ.set (.v r) fun i => sg.sem (p i) (q i))

/-- Run body lines in order. -/
def execBody {n w : Nat} (ρ : Env n w) (l : List Instr) : Option (Env n w) :=
  l.foldlM Instr.exec ρ

/-- The shapes the kernel text is specified at: `n` a power of two at most `2^31`
    (tile dimensions are powers of two, §5 of the specification; the `iota` values
    `0, …, n-1` fit `i32`, §9.3.11, and are nonnegative as signed offsets,
    §9.3.13), and `w` one of `8, 16, 32, 64`. -/
def ShapeOk (n w : Nat) : Bool :=
  (List.range 32).any (fun k => 2 ^ k == n) && [8, 16, 32, 64].contains w

/-- The `n` elements from address `p`. -/
def loadTile {w : Nat} (n : Nat) (mem : Nat → BitVec w) (p : Nat) : Tile n w :=
  fun i => mem (p + i)

/-- Memory with the `n` elements from address `p` replaced by the lanes of `t`. -/
def storeTile {n w : Nat} (mem : Nat → BitVec w) (p : Nat) (t : Tile n w) : Nat → BitVec w :=
  fun q => if h : p ≤ q ∧ q < p + n then t ⟨q - p, by omega⟩ else mem q

/-- The kernel's effect on a memory of `i w` elements, launched with pointer
    arguments `pa`, `pb`, `pr`: the final memory, or `none`.

    Memory is `Nat → BitVec w`, addressed in elements (a pointer aligned to the
    element size, as the loads and stores require, names an element), and the
    value is the effect of one tile block. The lines around the body mean:
    * `cuda_tile.module` (§9.3.12) and `cuda_tile.entry` (§9.3.4) with scalar
      pointer arguments of type `!cuda_tile.tile<ptr<i w>>`; the entry returns no
      value and ends in `cuda_tile.return` (§9.5.7).
    * `iota` (§9.3.11): the tile `[0, …, n-1]`.
    * `reshape` (§9.3.17) of the scalar pointer to shape `1`, `broadcast` (§9.3.1)
      to shape `n`, and `offset` (§9.3.13, `ptr_i + offset_i × bitwidth`, one
      element per step): the pointers `p + i`.
    * `load_ptr_tko weak` (`#cuda-tile-load-ptr-tko`, Memory operations): the
      gather of the elements at those pointers, `loadTile n mem p`.
    * `store_ptr_tko weak` (`#cuda-tile-store-ptr-tko`, Memory operations): the
      scatter of the stored tile to `pr + i`, `storeTile mem pr`.
    The stored tile is the value of `ret` after the body. -/
def Func.run (f : Func) (mem : Nat → BitVec f.w) (pa pb pr : Nat) :
    Option (Nat → BitVec f.w) :=
  if ShapeOk f.n f.w then
    (execBody (Env.init (loadTile f.n mem pa) (loadTile f.n mem pb)) f.body).bind fun ρ =>
      (ρ f.ret).map (storeTile mem pr)
  else none

/-! ## 6. Semantic preservation -/

/-- The literal `-1` at width `w` is the all-ones vector. -/
theorem ofInt_neg_one (w : Nat) : BitVec.ofInt w (-1) = BitVec.allOnes w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_allOnes]
  have hk : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  generalize 2 ^ w = K at hk ⊢
  rw [show (-1 : Int) = ((K - 1 : Nat) : Int) + (-1) * (K : Int) by omega,
    Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

theorem natMod_eq_of_intSub {X Y W : Nat} (k : Int) (h : (X : Int) - Y = W * k) :
    X % W = Y % W := by
  have : (X : Int) % W = (Y : Int) % W :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd ⟨k, h⟩)
  exact_mod_cast this

theorem toNat_truncate_sshiftRight (w : Nat) (P : BitVec (2 * w)) :
    ((P.sshiftRight w).truncate w).toNat = P.toNat / 2 ^ w % 2 ^ w := by
  have : (P.sshiftRight w).truncate w = P.extractLsb' w w := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_sshiftRight, hi, show ¬ 2 * w ≤ i by omega,
      show w + i < 2 * w by omega]
  rw [this, BitVec.extractLsb'_toNat]
  simp [Nat.shiftRight_eq_div_pow]

theorem toNat_sshiftRight_msb_and (w : Nat) (hw : 1 ≤ w) (a b : BitVec w) :
    (a.sshiftRight (w - 1) &&& b).toNat = if a.msb then b.toNat else 0 := by
  have : a.sshiftRight (w - 1) = if a.msb then BitVec.allOnes w else 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hmsb : a.msb = a.getLsbD (w - 1) := BitVec.msb_eq_getLsbD_last a
    rw [BitVec.getLsbD_sshiftRight]
    have hc : (if w - 1 + i < w then a.getLsbD (w - 1 + i) else a.msb) = a.msb := by
      split
      · rw [show i = 0 by omega, Nat.add_zero, hmsb]
      · rfl
    rw [hc]
    cases a.msb <;> simp [hi, show ¬ w ≤ i by omega]
  rw [this]
  split <;> simp

/-- **The signed high half from the unsigned one.** For `w ≥ 1`, the high `w` bits
    of the signed product are `mulhu a b - (a >>s (w-1) & b) - (b >>s (w-1) & a)`
    modulo `2^w`. -/
theorem mulhs_eq_mulhu_sub (w : Nat) (hw : 1 ≤ w) (a b : BitVec w) :
    ((a.signExtend (2 * w) * b.signExtend (2 * w)).sshiftRight w).truncate w
      = mulhu a b - (a.sshiftRight (w - 1) &&& b) - (b.sshiftRight (w - 1) &&& a) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_truncate_sshiftRight, BitVec.toNat_mul, BitVec.toNat_signExtend,
    BitVec.toNat_signExtend, BitVec.toNat_sub, BitVec.toNat_sub, mulhu, BitVec.toNat_ofNat,
    toNat_sshiftRight_msb_and w hw, toNat_sshiftRight_msb_and w hw,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have hA := a.isLt
  have hB := b.isLt
  generalize a.toNat = A at *
  generalize b.toNat = B at *
  have hW2 : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
  rw [hW2, Nat.mod_mul_right_div_self]
  have hWp : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  generalize 2 ^ w = W at *
  have hAW : A < W * W := by nlinarith
  have hBW : B < W * W := by nlinarith
  have hH : A * B / W < W := Nat.div_lt_of_lt_mul (by nlinarith)
  rw [Nat.mod_eq_of_lt hAW, Nat.mod_eq_of_lt hBW, Nat.mod_eq_of_lt hH, Nat.mod_mod,
    Nat.add_mod_mod, ← Nat.mul_sub_one]
  have hW0 : 0 < W := hWp
  generalize a.msb = ca
  generalize b.msb = cb
  cases ca <;> cases cb <;>
    simp only [Bool.false_eq_true, if_false, if_true, Nat.add_zero, Nat.sub_zero]
  · exact natMod_eq_of_intSub (-2) (by push_cast; ring)
  · rw [show A * (B + W * (W - 1)) = A * B + W * ((W - 1) * A) by ring,
      Nat.add_mul_div_left _ _ hW0]
    exact natMod_eq_of_intSub ((A : Int) - 2)
      (by push_cast [Nat.cast_sub hWp, Nat.cast_sub hA.le]; ring)
  · rw [show (A + W * (W - 1)) * B = A * B + W * ((W - 1) * B) by ring,
      Nat.add_mul_div_left _ _ hW0]
    exact natMod_eq_of_intSub ((B : Int) - 2)
      (by push_cast [Nat.cast_sub hWp, Nat.cast_sub hB.le]; ring)
  · rw [show (A + W * (W - 1)) * (B + W * (W - 1))
        = A * B + W * ((W - 1) * B + (W - 1) * A + W * (W - 1) * (W - 1)) by ring,
      Nat.add_mul_div_left _ _ hW0]
    exact natMod_eq_of_intSub ((A : Int) + B - 2 + ((W : Int) - 1) ^ 2)
      (by push_cast [Nat.cast_sub hWp, Nat.cast_sub hA.le, Nat.cast_sub hB.le]; ring)

theorem execBody_nil {n w : Nat} (ρ : Env n w) : execBody ρ [] = some ρ := rfl

theorem execBody_append {n w : Nat} (ρ : Env n w) (l l' : List Instr) :
    execBody ρ (l ++ l') = (execBody ρ l).bind fun ρ' => execBody ρ' l' := by
  simp only [execBody, List.foldlM_append]
  rfl

theorem execBody_cons {n w : Nat} (ρ : Env n w) (i : Instr) (l : List Instr) :
    execBody ρ (i :: l) = (i.exec ρ).bind fun ρ' => execBody ρ' l := rfl

/-- Register `nm` is bound in the translation state. -/
def TSt.bound (s : TSt) (nm : String) : Bool := (s.map.lookup nm).isSome

/-- The op has a printed form whose meaning is the tile model's, its literals are
    in range, and the registers it reads are bound. -/
def opOk (w : Nat) (s : TSt) : TileOp → Bool
  | .const _ k => decide (k < 2 ^ w)
  | .add _ a b | .sub _ a b | .mul _ a b | .and _ a b | .orr _ a b | .xorr _ a b
  | .shll _ a b | .shrr _ a b => s.bound a && s.bound b
  | .andn _ a b | .mulhs _ a b => decide (1 ≤ w) && s.bound a && s.bound b
  | .shr _ a imm => decide (imm < 2 ^ w) && s.bound a
  | .permxv .. | .bcast .. | .hadd .. | .shl .. | .sar .. | .rotl .. | .rotr .. | .mulhu ..
  | .shuffle .. | .blend .. => false

/-- Every op of the block satisfies `opOk` in the state the translation reaches it
    in. -/
def Supported (w : Nat) : TSt → List TileOp → Bool
  | _, [] => true
  | s, op :: ops => opOk w s op && Supported w (trOp w s op) ops

/-- The environment `ρ` holds, at the operand of every bound register, the value
    of that register in `st`, and every bound result index is below the counter. -/
structure Agree {n w : Nat} (t : TSt) (ρ : Env n w) (st : TileState n w) : Prop where
  val : ∀ nm o, t.map.lookup nm = some o → ρ o = some (st.get nm)
  fresh : ∀ nm k, t.map.lookup nm = some (.v k) → k < t.ctr

theorem Agree.opnd {n w : Nat} {t : TSt} {ρ : Env n w} {st : TileState n w}
    (h : Agree t ρ st) {nm : String} (hb : t.bound nm = true) :
    ρ (t.opnd nm) = some (st.get nm) := by
  simp only [TSt.bound, Option.isSome_iff_exists] at hb
  obtain ⟨o, ho⟩ := hb
  simp only [TSt.opnd, ho, Option.getD_some]
  exact h.val nm o ho

theorem Agree.opnd_ne {n w : Nat} {t : TSt} {ρ : Env n w} {st : TileState n w}
    (h : Agree t ρ st) (nm : String) {j : Nat} (hj : t.ctr ≤ j) : t.opnd nm ≠ .v j := by
  intro he
  simp only [TSt.opnd] at he
  cases hl : t.map.lookup nm with
  | none => simp [hl] at he
  | some o =>
    simp only [hl, Option.getD_some] at he
    subst he
    have := h.fresh nm j hl
    omega

theorem Env.set_ne {n w : Nat} (ρ : Env n w) {o o' : Opnd} (t : Tile n w) (h : o' ≠ o) :
    ρ.set o t o' = ρ o' := by
  simp [Env.set, h]

theorem Env.set_self {n w : Nat} (ρ : Env n w) (o : Opnd) (t : Tile n w) :
    ρ.set o t o = some t := by
  simp [Env.set]

theorem Agree.bind {n w : Nat} {t : TSt} {ρ ρ' : Env n w} {st : TileState n w}
    (h : Agree t ρ st) (d : String) {k c : Nat} (hk : t.ctr ≤ k) (hkc : k < c)
    (lanes : Tile n w) (hρ : ∀ o, (∀ i, t.ctr ≤ i → o ≠ .v i) → ρ' o = ρ o)
    (hv : ρ' (.v k) = some lanes) (out : List Instr) :
    Agree ⟨(d, .v k) :: t.map, c, out⟩ ρ' (st.set d lanes) := by
  constructor
  · intro nm o ho
    by_cases hnm : nm = d
    · subst hnm
      simp only [lookup_cons_self, Option.some.injEq] at ho
      subst ho
      simp [hv, TileState.set, TileState.get]
    · simp only [lookup_cons_ne _ _ hnm] at ho
      rw [hρ o]
      · simp only [TileState.get, TileState.set, hnm, if_false]
        exact h.val nm o ho
      · intro i hi he
        subst he
        have := h.fresh nm i ho
        omega
  · intro nm j ho
    show j < c
    by_cases hnm : nm = d
    · subst hnm
      simp only [lookup_cons_self, Option.some.injEq, Opnd.v.injEq] at ho
      omega
    · simp only [lookup_cons_ne _ _ hnm] at ho
      have := h.fresh nm j ho
      omega

/-- The invariant of the translation: the lines emitted so far run from `ρ0` to an
    environment that agrees with `st`. -/
def Inv {n w : Nat} (ρ0 : Env n w) (t : TSt) (st : TileState n w) : Prop :=
  ∃ ρ, execBody ρ0 t.out = some ρ ∧ Agree t ρ st

theorem Inv.push {n w : Nat} {ρ0 ρ : Env n w} {t : TSt} {st : TileState n w}
    (hρ : execBody ρ0 t.out = some ρ) (hA : Agree t ρ st) (d : String)
    (i : Instr) (lanes : Tile n w) (hex : i.exec ρ = some (ρ.set (.v t.ctr) lanes)) :
    Inv ρ0 (t.push d i) (st.set d lanes) := by
  refine ⟨ρ.set (.v t.ctr) lanes, ?_, ?_⟩
  · simp only [TSt.push, execBody_append, hρ, Option.bind_some, execBody_cons, hex,
      execBody_nil]
  · exact hA.bind d le_rfl (Nat.lt_succ_self _) lanes
      (fun o ho => Env.set_ne ρ lanes (ho t.ctr le_rfl)) (Env.set_self ..) _

theorem Inv.step {n w : Nat} {ρ0 : Env n w} {t : TSt} {st : TileState n w}
    (h : Inv ρ0 t st) (op : TileOp) (hok : opOk w t op = true) :
    Inv ρ0 (trOp w t op) (evalTileOp st op) := by
  obtain ⟨ρ, hρ, hA⟩ := h
  cases op with
  | const d k =>
    simp only [opOk, decide_eq_true_eq] at hok
    refine Inv.push hρ hA d _ (fun _ => BitVec.ofNat w k) ?_
    have h0 : (0 : Int) ≤ 2 ^ w := by positivity
    have h1 : -(2 ^ w : Int) ≤ 2 * (k : Int) := by omega
    have h2 : (k : Int) < 2 ^ w := by exact_mod_cast hok
    simp [Instr.exec, h1, h2, BitVec.ofInt_natCast]
  | add d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i + st.get b i)
      (by simp [Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | sub d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i - st.get b i)
      (by simp [Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | mul d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i * st.get b i)
      (by simp [Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | and d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i &&& st.get b i)
      (by simp [Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | orr d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i ||| st.get b i)
      (by simp [Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | xorr d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i ^^^ st.get b i)
      (by simp [Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | shll d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i <<< (st.get b i).toNat)
      (by simp [Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | shrr d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i >>> (st.get b i).toNat)
      (by simp [Instr.exec, Sgn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | andn d a b =>
    simp only [opOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hw, ha⟩, hb⟩ := hok
    have hp : (2 : Int) ≤ 2 ^ w := by
      have : (2 : Int) ^ 1 ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) hw
      simpa using this
    have hc : -(2 ^ w : Int) ≤ 2 * (-1) ∧ (-1 : Int) < 2 ^ w := ⟨by omega, by omega⟩
    have na0 := hA.opnd_ne a (le_refl t.ctr)
    have nb0 := hA.opnd_ne b (le_refl t.ctr)
    have nb1 := hA.opnd_ne b (Nat.le_succ t.ctr)
    let e1 := ρ.set (.v t.ctr) (fun _ => BitVec.ofInt w (-1))
    let e2 := e1.set (.v (t.ctr + 1)) (fun i => st.get a i ^^^ BitVec.ofInt w (-1))
    let e3 := e2.set (.v (t.ctr + 2))
      (fun i => (st.get a i ^^^ BitVec.ofInt w (-1)) &&& st.get b i)
    refine ⟨e3, ?_, ?_⟩
    · simp only [trOp, execBody_append, hρ, Option.bind_some, execBody_cons, execBody_nil,
        Instr.exec, Mn.sem, hc, and_self, if_true, e3, e2, e1, Env.set_ne _ _ na0,
        Env.set_ne _ _ nb0, Env.set_ne _ _ nb1, Env.set_self, hA.opnd ha, hA.opnd hb]
    · refine hA.bind d (k := t.ctr + 2) (by omega) (by omega)
        (fun i => (~~~ st.get a i) &&& st.get b i) ?_ ?_ _
      · intro o ho
        simp only [e3, e2, e1, Env.set_ne _ _ (ho _ (Nat.le_add_right t.ctr 2)),
          Env.set_ne _ _ (ho _ (Nat.le_succ t.ctr)), Env.set_ne _ _ (ho _ (le_refl t.ctr))]
      · simp only [e3, Env.set_self, ofInt_neg_one, BitVec.xor_allOnes]
  | shr d a imm =>
    simp only [opOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨himm, ha⟩ := hok
    have h0 : (0 : Int) ≤ 2 ^ w := by positivity
    have hc : -(2 ^ w : Int) ≤ 2 * (imm : Int) ∧ (imm : Int) < 2 ^ w :=
      ⟨by omega, by exact_mod_cast himm⟩
    have na0 := hA.opnd_ne a (le_refl t.ctr)
    let e1 := ρ.set (.v t.ctr) (fun _ => BitVec.ofInt w imm)
    let e2 := e1.set (.v (t.ctr + 1)) (fun i => st.get a i >>> (BitVec.ofInt w imm).toNat)
    refine ⟨e2, ?_, ?_⟩
    · simp only [trOp, execBody_append, hρ, Option.bind_some, execBody_cons, execBody_nil,
        Instr.exec, Sgn.sem, hc, and_self, if_true, e2, e1, Env.set_ne _ _ na0, Env.set_self,
        hA.opnd ha]
    · refine hA.bind d (k := t.ctr + 1) (by omega) (by omega)
        (fun i => st.get a i >>> imm) ?_ ?_ _
      · intro o ho
        simp only [e2, e1, Env.set_ne _ _ (ho _ (Nat.le_succ t.ctr)),
          Env.set_ne _ _ (ho _ (le_refl t.ctr))]
      · simp only [e2, Env.set_self, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt himm]
  | mulhs d a b =>
    simp only [opOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hw, ha⟩, hb⟩ := hok
    have hlt : w - 1 < 2 ^ w := lt_of_le_of_lt (Nat.sub_le w 1) Nat.lt_two_pow_self
    have h0 : (0 : Int) ≤ 2 ^ w := by positivity
    have hc : -(2 ^ w : Int) ≤ 2 * ((w - 1 : Nat) : Int) ∧ ((w - 1 : Nat) : Int) < 2 ^ w :=
      ⟨by omega, by exact_mod_cast hlt⟩
    have hK : (BitVec.ofInt w ((w - 1 : Nat) : Int)).toNat = w - 1 := by
      rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have na : ∀ k, t.opnd a ≠ .v (t.ctr + k) := fun k => hA.opnd_ne a (Nat.le_add_right _ k)
    have nb : ∀ k, t.opnd b ≠ .v (t.ctr + k) := fun k => hA.opnd_ne b (Nat.le_add_right _ k)
    have na0 := hA.opnd_ne a (le_refl t.ctr)
    have nb0 := hA.opnd_ne b (le_refl t.ctr)
    let K := BitVec.ofInt w ((w - 1 : Nat) : Int)
    let A := st.get a
    let B := st.get b
    let e1 := ρ.set (.v t.ctr) (fun _ => K)
    let e2 := e1.set (.v (t.ctr + 1)) (fun i => (A i).sshiftRight K.toNat)
    let e3 := e2.set (.v (t.ctr + 2)) (fun i => (B i).sshiftRight K.toNat)
    let e4 := e3.set (.v (t.ctr + 3)) (fun i => mulhu (A i) (B i))
    let e5 := e4.set (.v (t.ctr + 4)) (fun i => (A i).sshiftRight K.toNat &&& B i)
    let e6 := e5.set (.v (t.ctr + 5)) (fun i => (B i).sshiftRight K.toNat &&& A i)
    let e7 := e6.set (.v (t.ctr + 6))
      (fun i => mulhu (A i) (B i) - ((A i).sshiftRight K.toNat &&& B i))
    let e8 := e7.set (.v (t.ctr + 7))
      (fun i => mulhu (A i) (B i) - ((A i).sshiftRight K.toNat &&& B i)
        - ((B i).sshiftRight K.toNat &&& A i))
    refine ⟨e8, ?_, ?_⟩
    · simp only [trOp, execBody_append, hρ, Option.bind_some, execBody_cons, execBody_nil,
        Instr.exec, hc, and_self, if_true]
      simp [e8, e7, e6, e5, e4, e3, e2, e1, Env.set, na, nb, na0, nb0, hA.opnd ha, hA.opnd hb,
        Sgn.sem, Mn.sem, A, B, K]
    · refine hA.bind d (k := t.ctr + 7) (by omega) (by omega)
        (fun i => (((st.get a i).signExtend (2 * w) * (st.get b i).signExtend (2 * w)).sshiftRight
          w).truncate w) ?_ ?_ _
      · intro o ho
        simp [e8, e7, e6, e5, e4, e3, e2, e1, Env.set, ho]
      · simp only [e8, Env.set_self, Option.some.injEq]
        funext i
        rw [mulhs_eq_mulhu_sub w hw, hK]
  | permxv => simp [opOk] at hok
  | bcast => simp [opOk] at hok
  | hadd => simp [opOk] at hok
  | shl => simp [opOk] at hok
  | sar => simp [opOk] at hok
  | rotl => simp [opOk] at hok
  | rotr => simp [opOk] at hok
  | mulhu => simp [opOk] at hok
  | shuffle => simp [opOk] at hok
  | blend => simp [opOk] at hok

theorem Inv.foldl {n w : Nat} {ρ0 : Env n w} :
    ∀ (body : List TileOp) (t : TSt) (st : TileState n w), Inv ρ0 t st →
      Supported w t body = true → Inv ρ0 (body.foldl (trOp w) t) (runTileBlock st body)
  | [], _, _, h, _ => h
  | op :: ops, t, st, h, hs => by
    simp only [Supported, Bool.and_eq_true] at hs
    exact Inv.foldl ops (trOp w t op) (evalTileOp st op) (h.step op hs.1) hs.2

theorem Inv.init {n w : Nat} (st : TileState n w) :
    Inv (Env.init (st.get "a") (st.get "b")) TSt.init st := by
  refine ⟨_, execBody_nil _, ?_, ?_⟩
  · intro nm o ho
    by_cases h1 : nm = "a"
    · subst h1
      simp only [TSt.init, lookup_cons_self, Option.some.injEq] at ho
      subst ho; rfl
    · by_cases h2 : nm = "b"
      · subst h2
        simp only [TSt.init, lookup_cons_ne _ _ h1, lookup_cons_self, Option.some.injEq] at ho
        subst ho; rfl
      · simp only [TSt.init] at ho
        rw [lookup_cons_ne _ _ h1, lookup_cons_ne _ _ h2] at ho
        exact absurd ho (by simp [List.lookup])
  · intro nm k ho
    by_cases h1 : nm = "a"
    · subst h1
      simp [TSt.init] at ho
    · by_cases h2 : nm = "b"
      · subst h2
        simp [TSt.init, lookup_cons_ne _ _ h1] at ho
      · simp only [TSt.init] at ho
        rw [lookup_cons_ne _ _ h1, lookup_cons_ne _ _ h2] at ho
        exact absurd ho (by simp [List.lookup])

/-- The block `body` is supported and its result register `res` is bound. -/
def SupportedFunc (w : Nat) (body : List TileOp) (res : String) : Bool :=
  Supported w TSt.init body && (body.foldl (trOp w) TSt.init).bound res

/-- **Semantic preservation.** For a supported block at a specified shape, the
    kernel `toAst n w name body res`, launched on a memory holding the tiles of
    registers `a` and `b` of a state `st` at `pa` and `pb`, stores at `pr` the value
    `runTileBlock` leaves in register `res`, and changes no other element. -/
theorem run_toAst {n w : Nat} (name : String) (body : List TileOp) (res : String)
    (hs : SupportedFunc w body res = true) (hshape : ShapeOk n w = true)
    (st : TileState n w) (mem : Nat → BitVec w) (pa pb pr : Nat)
    (ha : loadTile n mem pa = st.get "a") (hb : loadTile n mem pb = st.get "b") :
    (toAst n w name body res).run mem pa pb pr
      = some (storeTile mem pr ((runTileBlock st body).get res)) := by
  simp only [SupportedFunc, Bool.and_eq_true] at hs
  obtain ⟨ρ, hρ, hA⟩ := Inv.foldl body TSt.init st (Inv.init st) hs.1
  simp only [Func.run, toAst, hshape, if_true, ha, hb]
  rw [hρ, Option.bind_some, hA.opnd hs.2, Option.map_some]

theorem supported_laneMoving {w : Nat} :
    ∀ (t : TSt) (body : List TileOp), Supported w t body = true →
      body.any laneMoving = false
  | _, [], _ => rfl
  | t, op :: ops, h => by
    simp only [Supported, Bool.and_eq_true] at h
    have ih := supported_laneMoving (trOp w t op) ops h.2
    cases op <;> simp_all [opOk, laneMoving]

/-- For a supported block, the checked emitter returns the printed kernel. -/
theorem emitTileFunc?_eq_some {n w : Nat} (name : String) (body : List TileOp) (res : String)
    (hs : SupportedFunc w body res = true) :
    emitTileFunc? n w name body res = some (toAst n w name body res).print := by
  simp only [SupportedFunc, Bool.and_eq_true] at hs
  simp only [emitTileFunc?, supported_laneMoving _ _ hs.1, Bool.false_eq_true,
    if_false, emitTileFuncAt_eq_print]

/-! ## 7. Parser -/

/-- Strip the prefix `p`. -/
def expect : List Char → List Char → Option (List Char)
  | [], s => some s
  | c :: p, d :: s => if c = d then expect p s else none
  | _ :: _, [] => none

theorem expect_append (p s : List Char) : expect p (p ++ s) = some s := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [expect, ih]

/-- The longest prefix whose characters satisfy `p`, and the rest. -/
def span (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: s => if p c then (c :: (span p s).1, (span p s).2) else ([], c :: s)

theorem span_append (p : Char → Bool) (l : List Char) (c : Char) (r : List Char)
    (hl : ∀ x ∈ l, p x = true) (hc : p c = false) : span p (l ++ c :: r) = (l, c :: r) := by
  induction l with
  | nil => simp [span, hc]
  | cons x l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hl
    simp [span, hl.1, ih hl.2]

/-- A decimal natural number. -/
def parseNat (s : List Char) : Option (Nat × List Char) :=
  (String.ofList (span Char.isDigit s).1).toNat?.map fun k => (k, (span Char.isDigit s).2)

/-- A character of an integer literal. -/
def isIntChar (c : Char) : Bool := c == '-' || c.isDigit

/-- A decimal integer, optionally negative. -/
def parseInt (s : List Char) : Option (Int × List Char) :=
  (String.ofList (span isIntChar s).1).toInt?.map fun k => (k, (span isIntChar s).2)

/-- A character of a symbol name. -/
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$' || c == '.'

/-- An operand. -/
def parseOpnd : List Char → Option (Opnd × List Char)
  | '%' :: s =>
    match span Char.isAlphanum s with
    | (['a'], r) => some (.a, r)
    | (['b'], r) => some (.b, r)
    | (['u', 'n', 'd', 'e', 'f'], r) => some (.undef, r)
    | ('v' :: ds, r) => (String.ofList ds).toNat?.map fun k => (.v k, r)
    | _ => none
  | _ => none

/-- The mnemonics, in a list. -/
def Mn.all : List Mn := [.addi, .subi, .muli, .andi, .ori, .xori, .shli, .mulhii]

/-- The mnemonic with the given characters. -/
def Mn.ofChars (cs : List Char) : Option Mn := Mn.all.find? fun m => m.name.toList == cs

/-- The signedness keyword with the given characters. -/
def Sgn.ofChars (cs : List Char) : Option Sgn :=
  [Sgn.signed, .unsigned].find? fun g => g.name.toList == cs

/-- One body line, from its leading spaces to the end of its type. -/
def parseInstr (n w : Nat) (s : List Char) : Option (Instr × List Char) := do
  let s ← expect "    ".toList s
  let s ← expect "%v".toList s
  let (r, s) ← parseNat s
  let s ← expect " = cuda_tile.".toList s
  let (tok, s) := span Char.isLower s
  if tok = "constant".toList then do
    let s ← expect " <i".toList s
    let s ← expect (toString w).toList s
    let s ← expect ": ".toList s
    let (k, s) ← parseInt s
    let s ← expect "> : ".toList s
    let s ← expect (tileTyAt n w).toList s
    pure (.const r k, s)
  else if tok = "shri".toList then do
    let s ← expect " ".toList s
    let (x, s) ← parseOpnd s
    let s ← expect ", ".toList s
    let (y, s) ← parseOpnd s
    let s ← expect " ".toList s
    let (g, s) := span Char.isLower s
    let sg ← Sgn.ofChars g
    let s ← expect " : ".toList s
    let s ← expect (tileTyAt n w).toList s
    pure (.shri sg r x y, s)
  else do
    let mn ← Mn.ofChars tok
    let s ← expect " ".toList s
    let (x, s) ← parseOpnd s
    let s ← expect ", ".toList s
    let (y, s) ← parseOpnd s
    let s ← expect " : ".toList s
    let s ← expect (tileTyAt n w).toList s
    pure (.bin mn r x y, s)

/-- The body lines, each followed by a newline, then the store line and the end of
    the kernel. `fuel` bounds the number of lines. -/
def parseBody (n w : Nat) : Nat → List Char → Option (List Instr × Opnd)
  | 0, _ => none
  | fuel + 1, s =>
    match expect storeHead.toList s with
    | some s => do
      let (o, s) ← parseOpnd s
      let s ← expect (storeTail n w).toList s
      if s = [] then pure ([], o) else none
    | none => do
      let (i, s) ← parseInstr n w s
      let s ← expect "\n".toList s
      let (is, o) ← parseBody n w fuel s
      pure (i :: is, o)

/-- The pointer type `!cuda_tile.tile<ptr<i w>>`. -/
def parsePtrTy (s : List Char) : Option (Nat × List Char) := do
  let s ← expect "!cuda_tile.tile<ptr<i".toList s
  let (w, s) ← parseNat s
  let s ← expect ">>".toList s
  pure (w, s)

/-- The index tile type `!cuda_tile.tile<n x i32>`. -/
def parseIdxTy (s : List Char) : Option (Nat × List Char) := do
  let s ← expect "!cuda_tile.tile<".toList s
  let (n, s) ← parseNat s
  let s ← expect "xi32>".toList s
  pure (n, s)

/-- A kernel, from the characters of its text. -/
def parseFunc (s : List Char) : Option Func := do
  let s ← expect "cuda_tile.module @".toList s
  let (nm, s) := span isIdChar s
  let s ← expect " {\n  cuda_tile.entry @".toList s
  let s ← expect nm s
  let s ← expect "(%pa: ".toList s
  let (w, s) ← parsePtrTy s
  let s ← expect ", %pb: ".toList s
  let s ← expect (ptrTyAt w).toList s
  let s ← expect ", %pr: ".toList s
  let s ← expect (ptrTyAt w).toList s
  let s ← expect ") {\n    %iota = cuda_tile.iota : ".toList s
  let (n, s) ← parseIdxTy s
  let s ← expect (loadPrologue n w).toList s
  let (body, ret) ← parseBody n w s.length s
  pure ⟨String.ofList nm, n, w, body, ret⟩

/-- Parse the text of a kernel. -/
def parse (s : String) : Option Func := parseFunc s.toList

/-! ### Round trip -/

theorem parseNat_cons (k : Nat) (c : Char) (r : List Char) (hc : c.isDigit = false) :
    parseNat (Nat.toDigits 10 k ++ c :: r) = some (k, c :: r) := by
  have hd : ∀ x ∈ Nat.toDigits 10 k, x.isDigit = true :=
    fun x hx => Nat.isDigit_of_mem_toDigits (by omega) (by omega) hx
  have h := Nat.toNat?_repr k
  rw [← String.ofList_toList (s := Nat.repr k), Nat.toList_repr] at h
  simp only [parseNat, span_append _ _ c r hd hc, h, Option.map_some]

theorem parseInt_cons (k : Int) (c : Char) (r : List Char) (hc : isIntChar c = false) :
    parseInt ((Int.repr k).toList ++ c :: r) = some (k, c :: r) := by
  have hd : ∀ x ∈ (Int.repr k).toList, isIntChar x = true := by
    intro x hx
    rw [Int.repr_eq_if] at hx
    split at hx
    · simp only [Nat.toList_repr] at hx
      simp [isIntChar, Nat.isDigit_of_mem_toDigits (by omega) (by omega) hx]
    · simp only [String.toList_append, Nat.toList_repr, List.mem_append] at hx
      rcases hx with hx | hx
      · simp at hx; simp [isIntChar, hx]
      · simp [isIntChar, Nat.isDigit_of_mem_toDigits (by omega) (by omega) hx]
  have h := Int.toInt?_repr k
  rw [← String.ofList_toList (s := Int.repr k)] at h
  simp only [parseInt, span_append _ _ c r hd hc, h, Option.map_some]

theorem parseOpnd_cons (o : Opnd) (c : Char) (r : List Char) (hc : c.isAlphanum = false) :
    parseOpnd (o.print.toList ++ c :: r) = some (o, c :: r) := by
  cases o with
  | a => simp [Opnd.print, parseOpnd, span, hc]
  | b => simp [Opnd.print, parseOpnd, span, hc]
  | undef => simp [Opnd.print, parseOpnd, span, hc]
  | v k =>
    have hd : ∀ x ∈ Nat.toDigits 10 k, x.isAlphanum = true := fun x hx => by
      simp [Char.isAlphanum, Nat.isDigit_of_mem_toDigits (by omega) (by omega) hx]
    have h := Nat.toNat?_repr k
    rw [← String.ofList_toList (s := Nat.repr k), Nat.toList_repr] at h
    have hs : span Char.isAlphanum ('v' :: (Nat.toDigits 10 k ++ c :: r))
        = ('v' :: Nat.toDigits 10 k, c :: r) := by
      rw [← List.cons_append, span_append _ _ c r _ hc]
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨by decide, hd⟩
    simp only [Opnd.print, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr]
    simp only [show ("%v" : String).toList = ['%', 'v'] by simp, List.cons_append,
      List.nil_append, parseOpnd, hs, h, Option.map_some]

/-- `l` is nonempty and its first character does not satisfy `p`. -/
def startsOff (p : Char → Bool) : List Char → Bool
  | [] => false
  | c :: _ => !p c

theorem parseNat_off (k : Nat) (l r : List Char) (h : startsOff Char.isDigit l = true) :
    parseNat (Nat.toDigits 10 k ++ (l ++ r)) = some (k, l ++ r) := by
  cases l with
  | nil => simp [startsOff] at h
  | cons c l => simpa [startsOff] using parseNat_cons k c (l ++ r) (by simpa [startsOff] using h)

theorem parseInt_off (k : Int) (l r : List Char) (h : startsOff isIntChar l = true) :
    parseInt ((Int.repr k).toList ++ (l ++ r)) = some (k, l ++ r) := by
  cases l with
  | nil => simp [startsOff] at h
  | cons c l => simpa [startsOff] using parseInt_cons k c (l ++ r) (by simpa [startsOff] using h)

theorem parseOpnd_off (o : Opnd) (l r : List Char) (h : startsOff Char.isAlphanum l = true) :
    parseOpnd (o.print.toList ++ (l ++ r)) = some (o, l ++ r) := by
  cases l with
  | nil => simp [startsOff] at h
  | cons c l =>
    simpa [startsOff] using parseOpnd_cons o c (l ++ r) (by simpa [startsOff] using h)

theorem span_off (p : Char → Bool) (l l' r : List Char) (hl : l.all p = true)
    (h : startsOff p l' = true) : span p (l ++ (l' ++ r)) = (l, l' ++ r) := by
  cases l' with
  | nil => simp [startsOff] at h
  | cons c l' =>
    simp only [List.all_eq_true] at hl
    simpa using span_append p l c (l' ++ r) hl (by simpa [startsOff] using h)

theorem Mn.ofChars_name (mn : Mn) : Mn.ofChars mn.name.toList = some mn := by
  cases mn <;> simp [Mn.ofChars, Mn.all, Mn.name]

theorem Mn.name_lower (mn : Mn) : mn.name.toList.all Char.isLower = true := by
  cases mn <;> decide

theorem Mn.name_ne (mn : Mn) :
    mn.name.toList ≠ "constant".toList ∧ mn.name.toList ≠ "shri".toList := by
  cases mn <;> simp [Mn.name]

theorem Sgn.ofChars_name (sg : Sgn) : Sgn.ofChars sg.name.toList = some sg := by
  cases sg <;> simp [Sgn.ofChars, Sgn.name]

theorem Sgn.name_lower (sg : Sgn) : sg.name.toList.all Char.isLower = true := by
  cases sg <;> decide

set_option simprocs false in
/-- **The parser reads back a printed line**, followed by any text. -/
theorem parseInstr_print (n w : Nat) (i : Instr) (r : List Char) :
    parseInstr n w ((i.print n w).toList ++ r) = some (i, r) := by
  have h0 := fun k => parseNat_off k " = cuda_tile.".toList
  cases i with
  | const k v =>
    simp only [Instr.print, constLine, vName, String.toList_append, List.append_assoc,
      Nat.toString_eq_repr, Nat.toList_repr, Int.toString_eq_repr, parseInstr,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, expect_append, h0 k _ (by decide),
      span_off Char.isLower "constant".toList " <i".toList _ (by decide) (by decide),
      parseInt_off v "> : ".toList _ (by decide), if_true]
  | bin mn k x y =>
    simp only [Instr.print, binLine, vName, String.toList_append, List.append_assoc,
      Nat.toString_eq_repr, Nat.toList_repr, parseInstr,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, expect_append, h0 k _ (by decide),
      span_off Char.isLower mn.name.toList " ".toList _ (Mn.name_lower mn) (by decide),
      (Mn.name_ne mn).1, (Mn.name_ne mn).2, if_false, Mn.ofChars_name,
      parseOpnd_off x ", ".toList _ (by decide), parseOpnd_off y " : ".toList _ (by decide)]
  | shri sg k x y =>
    simp only [Instr.print, shriLine, vName, String.toList_append, List.append_assoc,
      Nat.toString_eq_repr, Nat.toList_repr, parseInstr,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, expect_append, h0 k _ (by decide),
      span_off Char.isLower "shri".toList " ".toList _ (by decide) (by decide),
      show "shri".toList ≠ "constant".toList by decide, if_false, if_true,
      parseOpnd_off x ", ".toList _ (by decide), parseOpnd_off y " ".toList _ (by decide),
      span_off Char.isLower sg.name.toList " : ".toList _ (Sgn.name_lower sg) (by decide),
      Sgn.ofChars_name]

theorem expect_self (p : List Char) : expect p p = some [] := by
  simpa using expect_append p []

theorem parsePtrTy_ptrTyAt (w : Nat) (r : List Char) :
    parsePtrTy ((ptrTyAt w).toList ++ r) = some (w, r) := by
  unfold ptrTyAt
  simp only [String.toList_append, List.append_assoc, Nat.toString_eq_repr,
    Nat.toList_repr, parsePtrTy, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    expect_append, parseNat_off w ">>".toList _ (by decide)]

theorem parseIdxTy_idxTyAt (n : Nat) (r : List Char) :
    parseIdxTy ((idxTyAt n).toList ++ r) = some (n, r) := by
  unfold idxTyAt
  simp only [String.toList_append, List.append_assoc, Nat.toString_eq_repr,
    Nat.toList_repr, parseIdxTy, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    expect_append, parseNat_off n "xi32>".toList _ (by decide)]

/-- The characters after the loads: each body line followed by a newline, then the
    store line and the end of the kernel. -/
def bodyText (n w : Nat) : List Instr → Opnd → List Char
  | [], o => storeHead.toList ++ (o.print.toList ++ (storeTail n w).toList)
  | i :: is, o => (i.print n w).toList ++ ("\n".toList ++ bodyText n w is o)

theorem expect_storeHead_line (n w : Nat) (i : Instr) (r : List Char) :
    expect storeHead.toList ((i.print n w).toList ++ r) = none := by
  have hs : storeHead.toList = "    %t".toList ++ "r = cuda_tile.store_ptr_tko weak %pr3, ".toList := by
    rw [← String.toList_append]; rfl
  have h : ∀ X Y, expect ("    %t".toList ++ Y) ("    ".toList ++ ("%v".toList ++ X)) = none := by
    intro X Y; simp [expect]
  rw [hs]
  cases i <;> simp only [Instr.print, constLine, binLine, shriLine, vName,
    String.toList_append, List.append_assoc, h]

theorem startsOff_storeTail (n w : Nat) :
    startsOff Char.isAlphanum (storeTail n w).toList = true := by
  simp [storeTail, startsOff]

theorem parseBody_bodyText (n w : Nat) :
    ∀ (body : List Instr) (o : Opnd) (fuel : Nat), body.length < fuel →
      parseBody n w fuel (bodyText n w body o) = some (body, o)
  | [], o, fuel + 1, _ => by
    have ho := parseOpnd_off o (storeTail n w).toList [] (startsOff_storeTail n w)
    simp only [List.append_nil] at ho
    simp only [bodyText, parseBody, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      expect_append, expect_self, ho, if_true]
  | i :: is, o, fuel + 1, h => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at h
    simp only [bodyText, parseBody, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      expect_append, expect_storeHead_line, parseInstr_print, parseBody_bodyText n w is o fuel h]

theorem length_bodyText (n w : Nat) (body : List Instr) (o : Opnd) :
    body.length < (bodyText n w body o).length := by
  induction body with
  | nil => simp [bodyText, storeHead]
  | cons i is ih => simp only [bodyText, List.length_cons, List.length_append]; simp; omega

theorem print_toList (f : Func) :
    f.print.toList = (kernelOpen f.n f.w f.name).toList ++ bodyText f.n f.w f.body f.ret := by
  have key : ∀ body : List Instr,
      (String.join (body.map fun i => i.print f.n f.w ++ "\n")).toList
          ++ (storeHead.toList ++ (f.ret.print.toList ++ (storeTail f.n f.w).toList))
        = bodyText f.n f.w body f.ret := by
    intro body
    induction body with
    | nil => simp [bodyText]
    | cons i is ih =>
      simp only [List.map_cons, String.join_cons, String.toList_append, List.append_assoc,
        bodyText, ← ih]
  unfold Func.print
  simp only [String.toList_append, List.append_assoc, key]

/-- **The parser inverts the printer.** For every AST whose kernel name consists of
    symbol characters, parsing its printed text returns it. -/
theorem parse_print (f : Func) (hname : f.name.toList.all isIdChar = true) :
    parse f.print = some f := by
  have hlen := length_bodyText f.n f.w f.body f.ret
  unfold parse parseFunc
  rw [print_toList]
  unfold kernelOpen
  simp only [String.toList_append, List.append_assoc, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, expect_append,
    span_off isIdChar f.name.toList " {\n  cuda_tile.entry @".toList _ hname (by decide),
    parsePtrTy_ptrTyAt, parseIdxTy_idxTyAt,
    parseBody_bodyText f.n f.w f.body f.ret _ hlen, String.ofList_toList]

/-- The printed text determines the AST, for kernel names of symbol characters. -/
theorem print_injective {f g : Func} (hf : f.name.toList.all isIdChar = true)
    (hg : g.name.toList.all isIdChar = true) (h : f.print = g.print) : f = g := by
  have := parse_print f hf
  rw [h, parse_print g hg] at this
  exact (Option.some.inj this).symm

/-! ## 8. The BabyBear multiply -/

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileDialectLower
  (lowerCom lowerComK lowerExpr constOf countOk binE constE varLevel bbName bbName_injective
    bbMulTileCom bbMulTileComIR bbMulTileCom_lowered_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialectModelTie (toTileOp)

theorem bbName_beq (i j : Nat) : (bbName i == bbName j) = decide (i = j) := by
  rw [Bool.eq_iff_iff]
  simp [bbName_injective.eq_iff]

/-- The block `lowerCom` produces for the 8-lane BabyBear multiply, over the
    register names `bbName`: `bbName 1 = "a"`, `bbName 0 = "b"`, and the binding at
    level `k + 2` writes `bbName (k + 2) = "t" ++ toString k`. -/
def bbMulBlk : List TileOp :=
  [ .const (bbName 2) 2290649223, .const (bbName 3) 2013265921, .const (bbName 4) 0,
    .const (bbName 5) 30, .const (bbName 6) 32, .const (bbName 7) 63,
    .mul (bbName 8) (bbName 1) (bbName 0), .shrr (bbName 9) (bbName 8) (bbName 5),
    .mul (bbName 10) (bbName 9) (bbName 2), .shrr (bbName 11) (bbName 10) (bbName 6),
    .mul (bbName 12) (bbName 11) (bbName 3), .sub (bbName 13) (bbName 8) (bbName 12),
    .sub (bbName 14) (bbName 13) (bbName 3), .shrr (bbName 15) (bbName 14) (bbName 7),
    .sub (bbName 16) (bbName 4) (bbName 15), .and (bbName 17) (bbName 16) (bbName 3),
    .add (bbName 18) (bbName 14) (bbName 17) ]

theorem lowerCom_bbMulTileCom :
    lowerCom 8 64 bbName (bbMulTileCom 8) = some (bbMulBlk, bbName 18) := by
  simp [lowerCom, lowerComK, lowerExpr, constOf, countOk, Function.update, bbMulTileCom, binE,
    constE, varLevel, toTileOp, bbMulBlk]

/-- The AST of `bbMulTileComIR`. -/
def bbMulAst : Func := toAst 8 64 "bb_mul_tile_com" bbMulBlk (bbName 18)

/-- **The emitted BabyBear text parses to `bbMulAst`.** -/
theorem parse_bbMulTileComIR : parse bbMulTileComIR = some bbMulAst := by
  have h : bbMulTileComIR = emitTileFunc "bb_mul_tile_com" bbMulBlk (bbName 18) := by
    unfold bbMulTileComIR
    rw [lowerCom_bbMulTileCom]
  rw [h, emitTileFunc_eq_print]
  exact parse_print _ (by decide)

theorem TSt.init_bbName : TSt.init = ⟨[(bbName 1, .a), (bbName 0, .b)], 0, []⟩ := rfl

theorem bbMulBlk_supported : SupportedFunc 64 bbMulBlk (bbName 18) = true := by
  simp [SupportedFunc, Supported, opOk, trOp, TSt.push, TSt.bound, TSt.init_bbName, bbMulBlk,
    List.lookup, bbName_beq]

theorem shapeOk_eight_sixtyFour : ShapeOk 8 64 = true := by decide

/-- **The BabyBear kernel stores `bbMulWord` lane by lane.** Launched on any memory
    with pointer arguments `pa`, `pb`, `pr`, the kernel `bbMulAst` stores at `pr + i`
    the value `bbMulWord` of the elements at `pa + i` and `pb + i`, for `i < 8`. -/
theorem bbMulAst_run (mem : Nat → BitVec 64) (pa pb pr : Nat) :
    bbMulAst.run mem pa pb pr
      = some (storeTile mem pr fun i : Fin 8 => bbMulWord (mem (pa + i)) (mem (pb + i))) := by
  have h := run_toAst (n := 8) (w := 64) "bb_mul_tile_com" bbMulBlk (bbName 18)
    bbMulBlk_supported shapeOk_eight_sixtyFour
    (bbMulInit (loadTile 8 mem pa) (loadTile 8 mem pb)) mem pa pb pr rfl rfl
  rw [bbMulTileCom_lowered_denote _ _ lowerCom_bbMulTileCom] at h
  exact h

/-- **End to end.** The emitted `cuda_tile` text of the BabyBear multiply parses to
    `bbMulAst`; launched on any memory, it writes at `pr + i`, for `i < 8`,
    `x · y mod p` for the elements `x`, `y` at `pa + i`, `pb + i` whenever both are
    below `p = 2013265921`, and leaves every other element unchanged. -/
theorem bbMulTileComIR_correct :
    parse bbMulTileComIR = some bbMulAst ∧ ∀ (mem : Nat → BitVec 64) (pa pb pr : Nat),
      ∃ mem', bbMulAst.run mem pa pb pr = some mem' ∧
        (∀ i : Fin 8, (mem (pa + i)).toNat < 2013265921 → (mem (pb + i)).toNat < 2013265921 →
          (mem' (pr + i)).toNat = (mem (pa + i)).toNat * (mem (pb + i)).toNat % 2013265921) ∧
        ∀ q, q < pr ∨ pr + 8 ≤ q → mem' q = mem q := by
  refine ⟨parse_bbMulTileComIR, fun mem pa pb pr => ⟨_, bbMulAst_run mem pa pb pr, ?_, ?_⟩⟩
  · intro i hx hy
    have hi : pr ≤ pr + i ∧ pr + i < pr + 8 := ⟨Nat.le_add_right _ _, by omega⟩
    simp only [storeTile, hi, and_self, dif_pos, Nat.add_sub_cancel_left]
    exact CatCrypt.Crypto.SecureCompilation.TileBackend.TileArithCorrect.bbMulWord_toNat _ _ hx hy
  · intro q hq
    have : ¬ (pr ≤ q ∧ q < pr + 8) := by omega
    simp only [storeTile, this, dif_neg, not_false_eq_true]
    rfl

end CatCrypt.Crypto.SecureCompilation.TileBackend.CudaTileSemantics

end
