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

`ComToTileIR.emitTileFunc` prints a `TileModel.TileOp` block as text in the syntax
of the NVIDIA `cuda_tile` MLIR dialect. This module gives that text fragment an
AST (`Func`), a printer (`Func.print`), a parser (`parse`) and a semantics on
`Fin n → BitVec w` lanes (`Func.run`) in which each operation means what the CUDA
Tile IR specification
(https://docs.nvidia.com/cuda/tile-ir/latest/sections/operations.html) states.
The semantics (`Mn.sem`, `Instr.exec`, `Func.run`) is the trusted part.

## Main results

* `emitTileFunc_eq_print`: `emitTileFunc name body res` is the printed text of
  `toAst 8 64 name body res`, for every block.
* `parse_print`: `parse f.print = some f` for every AST whose function name consists
  of symbol characters; `print_injective`.
* `run_readShr_toAst`: for a block satisfying `SupportedFunc`, the AST with its
  right shifts read as `shri … unsigned`, evaluated on the tiles in registers `a`
  and `b` of a state, returns the value `runTileBlock` leaves in the result
  register. `run_toAst`: the same without that reading, for blocks without `shr`
  and `shrr`.
* `parse_bbMulTileComIR`, `bbMulAst_readShr_run`, `bbMulTileComIR_correct`: the
  emitted BabyBear text parses to `bbMulAst`, whose value with right shifts read
  as `shri … unsigned` is `bbMulWord` in every lane, hence `x i · y i mod p` for
  lanes below `p`.
* `bbMulAst_run_eq_none`: under the specification semantics without that reading
  the BabyBear text has no value, since it contains `shrui` lines.

## Where the printed text departs from the specification

* The emitter prints `func.func @name(…) -> ty { … return … }`. The
  specification's kernel is `cuda_tile.entry` (§9.3.4), which returns no value.
  `Func.run` reads the text as a function from its two arguments to the returned
  tile.
* Constants are printed `dense<k>`; the `cuda-tile` parser expects the typed form
  `<i64: k>`. `Instr.exec` reads `dense<k>` as that splat.
* `shrr` is printed as `shrui`, which is not an operation of the specification,
  and `shr` as `shri` without the required signedness keyword. `Func.readShr`
  reads both as `shri … unsigned`.
* `mulhs` is printed as `mulhi`, which is not an operation of the specification;
  the specified `mulhii` is unsigned, `mulhs` is signed.
* `permxv`, `bcast` and `hadd` are printed as `permute`, `broadcast` and `reduce`,
  whose specified meanings (a static permutation of dimensions, expansion of
  size-one dimensions, a reduction by a region that removes a dimension) are not
  the model's lane gather, lane splat and sum in every lane. They have no meaning
  here.
* The emitter prints the tile type `8xi64` whatever shape the block was lowered
  at. The element widths and power-of-two shapes the specification allows are not
  checked by `Func.run`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.CudaTileSemantics

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
  (Tile TileState TileOp evalTileOp runTileBlock bbMulWord bbMulInit)
open CatCrypt.Crypto.SecureCompilation.TileBackend.ComToTileIR
  (St emitTileOp emitTileFunc tileTy)

/-! ## 1. Syntax -/

/-- An SSA operand as `emitTileOp` prints it: the function arguments `%a`, `%b`,
    an op result `%v<k>`, or `%undef` (the text printed for a register that no
    earlier op or argument defines). -/
inductive Opnd where
  | a
  | b
  | v (k : Nat)
  | undef
  deriving DecidableEq, Repr

/-- The mnemonics of the two-operand forms `%r = cuda_tile.<mn> %x, %y : ty`
    that `emitTileOp` prints. `shrui` and `mulhi` are printed by the emitter
    but are not operations of the CUDA Tile IR specification. -/
inductive Mn where
  | addi
  | subi
  | muli
  | andi
  | ori
  | xori
  | shli
  | shri
  | shrui
  | mulhi
  deriving DecidableEq, Repr

/-- One line of the function body. `shriU` is the specification form
    `cuda_tile.shri %x, %y unsigned`, which `emitTileOp` does not print; it is
    the target of `Func.readShr`. -/
inductive Instr where
  /-- `%v<res> = cuda_tile.constant dense<val> : ty` -/
  | const (res : Nat) (val : Int)
  /-- `%v<res> = cuda_tile.<mn> %x, %y : ty` -/
  | bin (mn : Mn) (res : Nat) (x y : Opnd)
  /-- `%v<res> = cuda_tile.shri %x, %y unsigned : ty` -/
  | shriU (res : Nat) (x y : Opnd)
  /-- `%v<res> = cuda_tile.permute %x, %y : ty` -/
  | permute (res : Nat) (x y : Opnd)
  /-- `%v<res> = cuda_tile.broadcast %x {lane = k} : ty` -/
  | broadcast (res : Nat) (x : Opnd) (lane : Nat)
  /-- `%v<res> = cuda_tile.reduce %x {op = "add"} : ty` -/
  | reduceAdd (res : Nat) (x : Opnd)
  deriving DecidableEq, Repr

/-- A function `func.func @name(%a: ty, %b: ty) -> ty { body; return ret : ty }`
    over the tile type `ty = !cuda_tile.tile<n x i w>`. -/
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
  | .shri => "shri"
  | .shrui => "shrui"
  | .mulhi => "mulhi"

/-- The tile type `!cuda_tile.tile<n x i w>`. -/
def tyStr (n w : Nat) : String :=
  "!cuda_tile.tile<" ++ toString n ++ "xi" ++ toString w ++ ">"

/-- The result name `%v<k>`. -/
def vName (k : Nat) : String := "%v" ++ toString k

/-- The text of one body line at tile type `tyStr n w`. -/
def Instr.print (n w : Nat) : Instr → String
  | .const r k =>
      "  " ++ vName r ++ " = cuda_tile." ++ "constant" ++ " dense<" ++ toString k ++ "> : "
        ++ tyStr n w
  | .bin mn r x y =>
      "  " ++ vName r ++ " = cuda_tile." ++ mn.name ++ " " ++ x.print ++ ", " ++ y.print
        ++ " : " ++ tyStr n w
  | .shriU r x y =>
      "  " ++ vName r ++ " = cuda_tile." ++ "shri" ++ " " ++ x.print ++ ", " ++ y.print
        ++ " unsigned : " ++ tyStr n w
  | .permute r x y =>
      "  " ++ vName r ++ " = cuda_tile." ++ "permute" ++ " " ++ x.print ++ ", " ++ y.print
        ++ " : " ++ tyStr n w
  | .broadcast r x k =>
      "  " ++ vName r ++ " = cuda_tile." ++ "broadcast" ++ " " ++ x.print ++ " {lane = "
        ++ toString k ++ "} : " ++ tyStr n w
  | .reduceAdd r x =>
      "  " ++ vName r ++ " = cuda_tile." ++ "reduce" ++ " " ++ x.print ++ " {op = \"add\"} : "
        ++ tyStr n w

/-- The function header line. -/
def Func.header (f : Func) : String :=
  "func.func @" ++ f.name ++ "(%a: " ++ tyStr f.n f.w ++ ", %b: " ++ tyStr f.n f.w ++ ") -> "
    ++ tyStr f.n f.w ++ " {"

/-- The return line. -/
def Func.footer (f : Func) : String := "  return " ++ f.ret.print ++ " : " ++ tyStr f.n f.w

/-- The text of a function: its lines joined by newlines, with a final newline. -/
def Func.print (f : Func) : String :=
  String.intercalate "\n" (f.header :: (f.body.map (Instr.print f.n f.w) ++ [f.footer, "}"]))
    ++ "\n"

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

/-- The lines `emitTileOp` prints for one op, as AST. -/
def trOp (s : TSt) : TileOp → TSt
  | .const d k => s.push d (.const s.ctr k)
  | .add d a b => s.push d (.bin .addi s.ctr (s.opnd a) (s.opnd b))
  | .sub d a b => s.push d (.bin .subi s.ctr (s.opnd a) (s.opnd b))
  | .mul d a b => s.push d (.bin .muli s.ctr (s.opnd a) (s.opnd b))
  | .and d a b => s.push d (.bin .andi s.ctr (s.opnd a) (s.opnd b))
  | .orr d a b => s.push d (.bin .ori s.ctr (s.opnd a) (s.opnd b))
  | .xorr d a b => s.push d (.bin .xori s.ctr (s.opnd a) (s.opnd b))
  | .shll d a b => s.push d (.bin .shli s.ctr (s.opnd a) (s.opnd b))
  | .shrr d a b => s.push d (.bin .shrui s.ctr (s.opnd a) (s.opnd b))
  | .mulhs d a b => s.push d (.bin .mulhi s.ctr (s.opnd a) (s.opnd b))
  | .andn d a b =>
      { map := (d, .v (s.ctr + 2)) :: s.map, ctr := s.ctr + 3,
        out := s.out ++ [.const s.ctr (-1), .bin .xori (s.ctr + 1) (s.opnd a) (.v s.ctr),
          .bin .andi (s.ctr + 2) (.v (s.ctr + 1)) (s.opnd b)] }
  | .shr d a imm =>
      { map := (d, .v (s.ctr + 1)) :: s.map, ctr := s.ctr + 2,
        out := s.out ++ [.const s.ctr imm, .bin .shri (s.ctr + 1) (s.opnd a) (.v s.ctr)] }
  | .permxv d idx a => s.push d (.permute s.ctr (s.opnd a) (s.opnd idx))
  | .bcast d a k => s.push d (.broadcast s.ctr (s.opnd a) k)
  | .hadd d a => s.push d (.reduceAdd s.ctr (s.opnd a))

/-- The initial translation state: registers `a`, `b` bound to the arguments. -/
def TSt.init : TSt := ⟨[("a", .a), ("b", .b)], 0, []⟩

/-- The AST of the function `emitTileFunc name body res` prints, at tile type
    `tyStr n w`. -/
def toAst (n w : Nat) (name : String) (body : List TileOp) (res : String) : Func :=
  { name, n, w, body := (body.foldl trOp TSt.init).out, ret := (body.foldl trOp TSt.init).opnd res }

/-! ## 4. The emitter prints the AST -/

/-- `tyStr 8 64` is the emitter's tile type. -/
theorem tyStr_eight_sixtyFour : tyStr 8 64 = tileTy := by
  have h8 : Nat.repr 8 = "8" := by
    apply String.toList_inj.mp
    simp [Nat.toList_repr, Nat.toDigits_of_lt_base]
  have h64 : Nat.repr 64 = "64" := by
    apply String.toList_inj.mp
    simp [Nat.toList_repr, Nat.toDigits_of_lt_base, Nat.toDigits_of_base_le]
  unfold tyStr tileTy
  change "!cuda_tile.tile<" ++ Nat.repr 8 ++ "xi" ++ Nat.repr 64 ++ ">" = _
  simp only [h8, h64, String.reduceAppend]

/-- `Int.repr` of a natural number cast to `Int` is its `Nat.repr`. -/
@[simp] theorem repr_natCast (k : Nat) : Int.repr (k : Int) = Nat.repr k := by
  simp [Int.repr_eq_if]

/-- The characters of `toString (-1 : Int)`. -/
theorem toList_repr_neg_one : (Int.repr (-1)).toList = ['-', '1'] := by
  simp [Int.repr_eq_if, Nat.toList_repr, Nat.toDigits_of_lt_base]

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
def Rel (s : St) (t : TSt) : Prop :=
  s.map = t.map.map (fun p => (p.1, p.2.print)) ∧ s.ctr = t.ctr ∧
    s.lines.reverse = t.out.map (Instr.print 8 64)

theorem lookup_map_print (l : List (String × Opnd)) (nm : String) :
    (l.map (fun p => (p.1, p.2.print))).lookup nm = (l.lookup nm).map Opnd.print := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, o⟩ := p
    by_cases h : nm = k
    · subst h; simp only [List.map_cons, lookup_cons_self, Option.map_some]
    · simp only [List.map_cons, lookup_cons_ne _ _ h, ih]

theorem Opnd.print_v (k : Nat) : (Opnd.v k).print = "%v" ++ toString k := rfl

theorem Rel.opnd {s : St} {t : TSt} (h : Rel s t) (nm : String) :
    (s.map.lookup nm).getD "%undef" = (t.opnd nm).print := by
  simp only [TSt.opnd, h.1, lookup_map_print]
  cases t.map.lookup nm <;> rfl

theorem Rel.step {s : St} {t : TSt} (h : Rel s t) (op : TileOp) :
    Rel (emitTileOp s op) (trOp t op) := by
  obtain ⟨hm, hc, hl⟩ := h
  have ho := Rel.opnd ⟨hm, hc, hl⟩
  cases op <;>
    simp only [emitTileOp, emitTileOp.binOp, trOp, TSt.push, St.fresh, St.emit, St.bind,
      St.opnd, ho] <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    simp only [hm, hc, hl, List.map_cons, List.reverse_cons, List.map_append, List.map_nil,
      List.cons.injEq, List.append_assoc, List.cons_append, List.nil_append,
      List.append_cancel_left_eq, and_true, Opnd.print_v] <;>
    (simp only [← String.toList_inj]
     simp [String.toList_append, Instr.print, vName, Mn.name, Opnd.print_v,
       tyStr_eight_sixtyFour, toList_repr_neg_one])

theorem foldl_rel (body : List TileOp) :
    ∀ (s : St) (t : TSt), Rel s t → Rel (body.foldl emitTileOp s) (body.foldl trOp t) := by
  induction body with
  | nil => intro s t h; exact h
  | cons op body ih => intro s t h; exact ih _ _ (h.step op)

/-- **The emitter prints the AST.** `emitTileFunc name body res` is the printed
    text of `toAst 8 64 name body res`, for every `TileOp` block and result
    register. -/
theorem emitTileFunc_eq_print (name : String) (body : List TileOp) (res : String) :
    emitTileFunc name body res = (toAst 8 64 name body res).print := by
  have h := foldl_rel body ⟨[("a", "%a"), ("b", "%b")], 0, []⟩ TSt.init ⟨rfl, rfl, rfl⟩
  unfold emitTileFunc toAst Func.print Func.header Func.footer
  simp only [tyStr_eight_sixtyFour, ← h.2.2, St.opnd, h.opnd res, List.cons_append,
    List.nil_append]

/-! ## 5. Semantics -/

/-- The values of the SSA operands; `none` is an operand with no value. -/
abbrev Env (n w : Nat) := Opnd → Option (Tile n w)

/-- Define operand `o` to be the tile `t`. -/
def Env.set {n w : Nat} (ρ : Env n w) (o : Opnd) (t : Tile n w) : Env n w :=
  fun o' => if o' = o then some t else ρ o'

/-- The environment at function entry: `%a` is `x`, `%b` is `y`, nothing else has a
    value. -/
def Env.init {n w : Nat} (x y : Tile n w) : Env n w
  | .a => some x
  | .b => some y
  | _ => none

/-- The lane function of a two-operand mnemonic on `i w` lanes, `none` for the
    mnemonics this semantics gives no meaning to.

    Operations of the CUDA Tile IR specification
    (https://docs.nvidia.com/cuda/tile-ir/latest/sections/operations.html):
    * `addi` (§9.8.3, `#cuda-tile-addi`), `subi` (§9.8.15, `#cuda-tile-subi`),
      `muli` (§9.8.9, `#cuda-tile-muli`): the sum, difference and low product.
      The specification states "The default semantics are wrap-around semantics
      on overflow or underflow"; with the `overflow` attribute absent (its default
      is `none`) no no-wrap assumption is made, so each is the operation modulo
      `2^w`.
    * `andi` (§9.9.1), `ori` (§9.9.2), `xori` (§9.9.3): bitwise and, or, xor.
    * `shli` (§9.8.13, `#cuda-tile-shli`): `x << y`, zero-filled, with `y` read
      as unsigned. The specification does not state the result for `y ≥ w`; this
      semantics gives `0` (the lane function is `BitVec` shift by `y.toNat`), the
      result of the PTX `shl` instruction, which clamps shift amounts greater
      than the register width to the width.

    No meaning (`none`):
    * `shri` printed without a signedness keyword: §9.8.14 (`#cuda-tile-shri`)
      makes `signedness` a required parameter (the assembly format is
      `shri %lhs, %rhs signed|unsigned`), so this text has no specified meaning.
      The specified form with `unsigned` is `Instr.shriU`.
    * `shrui`: not an operation of the specification (it is the MLIR `arith`
      dialect spelling of a logical right shift).
    * `mulhi`: not an operation of the specification. The specified high
      multiply is `mulhii` (§9.8.10), which is "only defined for unsigned
      integers", whereas the tile model's `mulhs` is the signed high half. -/
def Mn.sem (w : Nat) : Mn → Option (BitVec w → BitVec w → BitVec w)
  | .addi => some (· + ·)
  | .subi => some (· - ·)
  | .muli => some (· * ·)
  | .andi => some (· &&& ·)
  | .ori => some (· ||| ·)
  | .xori => some (· ^^^ ·)
  | .shli => some (fun x y => x <<< y.toNat)
  | .shri => none
  | .shrui => none
  | .mulhi => none

/-- One body line. The meaning is the specification's, and `none` where the text
    has no specified meaning or reads an operand with no value.

    * `constant` (§9.3.3, `#cuda-tile-constant`, "creates a tile initialized by
      $value"): every lane is `BitVec.ofInt w k`, for a literal `k` in the range
      `[-2^(w-1), 2^w)` of an MLIR signless `iw` literal, `none` outside it. The
      emitter prints the value as `dense<k>`; the `cuda-tile` parser expects the
      typed form `<i64: k>`, and this semantics reads `dense<k>` as that splat.
    * `shri … unsigned` (§9.8.14): `x >> y` with zero fill, `y` read as unsigned;
      for `y ≥ w` the result is `0` (not stated in the specification; the PTX
      `shr` instruction clamps the shift amount to the width).
    * `permute` (§9.3.15, `#cuda-tile-permute`) permutes the dimensions of a tile
      by a static attribute array, `broadcast` (§9.3.1, `#cuda-tile-broadcast`)
      expands dimensions of size one, and `reduce` (§9.3.16,
      `#cuda-tile-reduce`) takes a `dim`, identities and a combining region and
      removes the reduced dimension. None of the three is a lane gather, a lane
      splat or a sum broadcast to every lane, and the printed forms
      (`permute %a, %idx`, `broadcast %a {lane = k}`, `reduce %a {op = "add"}`)
      are not their assembly formats, so they have no meaning here. -/
def Instr.exec {n w : Nat} (ρ : Env n w) : Instr → Option (Env n w)
  | .const r k =>
      if -(2 ^ w : Int) ≤ 2 * k ∧ k < 2 ^ w then some (ρ.set (.v r) fun _ => BitVec.ofInt w k)
      else none
  | .bin mn r x y =>
      (mn.sem w).bind fun f => (ρ x).bind fun p => (ρ y).bind fun q =>
        some (ρ.set (.v r) fun i => f (p i) (q i))
  | .shriU r x y =>
      (ρ x).bind fun p => (ρ y).bind fun q => some (ρ.set (.v r) fun i => p i >>> (q i).toNat)
  | .permute .. => none
  | .broadcast .. => none
  | .reduceAdd .. => none

/-- Run body lines in order. -/
def execBody {n w : Nat} (ρ : Env n w) (l : List Instr) : Option (Env n w) :=
  l.foldlM Instr.exec ρ

/-- The function's value on arguments `x`, `y`: run the body from `Env.init x y`
    and read the returned operand. -/
def Func.run (f : Func) (x y : Tile f.n f.w) : Option (Tile f.n f.w) :=
  (execBody (Env.init x y) f.body).bind fun ρ => ρ f.ret

/-- Read a right shift without signedness (`shri` or `shrui`) as the specified
    `shri … unsigned`. -/
def Instr.readShr : Instr → Instr
  | .bin .shri r x y => .shriU r x y
  | .bin .shrui r x y => .shriU r x y
  | i => i

/-- `Instr.readShr` on every body line. -/
def Func.readShr (f : Func) : Func := { f with body := f.body.map Instr.readShr }

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

theorem execBody_nil {n w : Nat} (ρ : Env n w) : execBody ρ [] = some ρ := rfl

theorem execBody_append {n w : Nat} (ρ : Env n w) (l l' : List Instr) :
    execBody ρ (l ++ l') = (execBody ρ l).bind fun ρ' => execBody ρ' l' := by
  simp only [execBody, List.foldlM_append]
  rfl

theorem execBody_cons {n w : Nat} (ρ : Env n w) (i : Instr) (l : List Instr) :
    execBody ρ (i :: l) = (i.exec ρ).bind fun ρ' => execBody ρ' l := rfl

/-- Register `nm` is bound in the translation state. -/
def TSt.bound (s : TSt) (nm : String) : Bool := (s.map.lookup nm).isSome

/-- The op is one whose printed lines have a specified meaning equal to the tile
    model's, and the registers it reads are bound. -/
def opOk (w : Nat) (s : TSt) : TileOp → Bool
  | .const _ k => decide (k < 2 ^ w)
  | .add _ a b | .sub _ a b | .mul _ a b | .and _ a b | .orr _ a b | .xorr _ a b
  | .shll _ a b | .shrr _ a b => s.bound a && s.bound b
  | .andn _ a b => decide (1 ≤ w) && s.bound a && s.bound b
  | .shr _ a imm => decide (imm < 2 ^ w) && s.bound a
  | .mulhs .. | .permxv .. | .bcast .. | .hadd .. => false

/-- Every op of the block satisfies `opOk` in the state the translation reaches it
    in. -/
def Supported (w : Nat) : TSt → List TileOp → Bool
  | _, [] => true
  | s, op :: ops => opOk w s op && Supported w (trOp s op) ops

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
  ∃ ρ, execBody ρ0 (t.out.map Instr.readShr) = some ρ ∧ Agree t ρ st

theorem Inv.push {n w : Nat} {ρ0 ρ : Env n w} {t : TSt} {st : TileState n w}
    (hρ : execBody ρ0 (t.out.map Instr.readShr) = some ρ) (hA : Agree t ρ st) (d : String)
    (i : Instr) (lanes : Tile n w) (hex : i.readShr.exec ρ = some (ρ.set (.v t.ctr) lanes)) :
    Inv ρ0 (t.push d i) (st.set d lanes) := by
  refine ⟨ρ.set (.v t.ctr) lanes, ?_, ?_⟩
  · simp only [TSt.push, List.map_append, List.map_cons, List.map_nil, execBody_append, hρ,
      Option.bind_some, execBody_cons, hex, execBody_nil]
  · exact hA.bind d le_rfl (Nat.lt_succ_self _) lanes
      (fun o ho => Env.set_ne ρ lanes (ho t.ctr le_rfl)) (Env.set_self ..) _

theorem Inv.step {n w : Nat} {ρ0 : Env n w} {t : TSt} {st : TileState n w}
    (h : Inv ρ0 t st) (op : TileOp) (hok : opOk w t op = true) :
    Inv ρ0 (trOp t op) (evalTileOp st op) := by
  obtain ⟨ρ, hρ, hA⟩ := h
  cases op with
  | const d k =>
    simp only [opOk, decide_eq_true_eq] at hok
    refine Inv.push hρ hA d _ (fun _ => BitVec.ofNat w k) ?_
    have h0 : (0 : Int) ≤ 2 ^ w := by positivity
    have h1 : -(2 ^ w : Int) ≤ 2 * (k : Int) := by omega
    have h2 : (k : Int) < 2 ^ w := by exact_mod_cast hok
    simp [Instr.readShr, Instr.exec, h1, h2, BitVec.ofInt_natCast]
  | add d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i + st.get b i)
      (by simp [Instr.readShr, Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | sub d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i - st.get b i)
      (by simp [Instr.readShr, Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | mul d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i * st.get b i)
      (by simp [Instr.readShr, Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | and d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i &&& st.get b i)
      (by simp [Instr.readShr, Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | orr d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i ||| st.get b i)
      (by simp [Instr.readShr, Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | xorr d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i ^^^ st.get b i)
      (by simp [Instr.readShr, Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | shll d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i <<< (st.get b i).toNat)
      (by simp [Instr.readShr, Instr.exec, Mn.sem, hA.opnd hok.1, hA.opnd hok.2])
  | shrr d a b =>
    simp only [opOk, Bool.and_eq_true] at hok
    exact Inv.push hρ hA d _ (fun i => st.get a i >>> (st.get b i).toNat)
      (by simp [Instr.readShr, Instr.exec, hA.opnd hok.1, hA.opnd hok.2])
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
    let e3 := e2.set (.v (t.ctr + 2)) (fun i => (st.get a i ^^^ BitVec.ofInt w (-1)) &&& st.get b i)
    refine ⟨e3, ?_, ?_⟩
    · simp only [trOp, List.map_append, List.map_cons, List.map_nil, execBody_append, hρ,
        Option.bind_some, execBody_cons, execBody_nil, Instr.readShr, Instr.exec, Mn.sem, hc,
        and_self, if_true, e3, e2, e1, Env.set_ne _ _ na0, Env.set_ne _ _ nb0,
        Env.set_ne _ _ nb1, Env.set_self, hA.opnd ha, hA.opnd hb]
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
    · simp only [trOp, List.map_append, List.map_cons, List.map_nil, execBody_append, hρ,
        Option.bind_some, execBody_cons, execBody_nil, Instr.readShr, Instr.exec, hc,
        and_self, if_true, e2, e1, Env.set_ne _ _ na0, Env.set_self, hA.opnd ha]
    · refine hA.bind d (k := t.ctr + 1) (by omega) (by omega)
        (fun i => st.get a i >>> imm) ?_ ?_ _
      · intro o ho
        simp only [e2, e1, Env.set_ne _ _ (ho _ (Nat.le_succ t.ctr)),
          Env.set_ne _ _ (ho _ (le_refl t.ctr))]
      · simp only [e2, Env.set_self, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt himm]
  | mulhs => simp [opOk] at hok
  | permxv => simp [opOk] at hok
  | bcast => simp [opOk] at hok
  | hadd => simp [opOk] at hok

theorem Inv.foldl {n w : Nat} {ρ0 : Env n w} :
    ∀ (body : List TileOp) (t : TSt) (st : TileState n w), Inv ρ0 t st →
      Supported w t body = true → Inv ρ0 (body.foldl trOp t) (runTileBlock st body)
  | [], _, _, h, _ => h
  | op :: ops, t, st, h, hs => by
    simp only [Supported, Bool.and_eq_true] at hs
    exact Inv.foldl ops (trOp t op) (evalTileOp st op) (h.step op hs.1) hs.2

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
  Supported w TSt.init body && (body.foldl trOp TSt.init).bound res

/-- **Semantic preservation.** For a supported block, the function
    `toAst n w name body res`, with right shifts read as `shri … unsigned`,
    evaluated on the tiles held in registers `a` and `b` of any state `st`, returns
    the value `runTileBlock` leaves in register `res`. -/
theorem run_readShr_toAst {n w : Nat} (name : String) (body : List TileOp) (res : String)
    (hs : SupportedFunc w body res = true) (st : TileState n w) :
    (toAst n w name body res).readShr.run (st.get "a") (st.get "b")
      = some ((runTileBlock st body).get res) := by
  simp only [SupportedFunc, Bool.and_eq_true] at hs
  obtain ⟨ρ, hρ, hA⟩ := Inv.foldl body TSt.init st (Inv.init st) hs.1
  simp only [Func.run, Func.readShr, toAst]
  rw [hρ]
  exact hA.opnd hs.2

/-- Every line of the translation of a block without `shr` and `shrr` is fixed by
    `Instr.readShr`. -/
def NoShift : List TileOp → Bool
  | [] => true
  | .shr .. :: _ => false
  | .shrr .. :: _ => false
  | _ :: ops => NoShift ops

theorem readShr_foldl :
    ∀ (body : List TileOp) (t : TSt), (∀ i ∈ t.out, i.readShr = i) → NoShift body = true →
      ∀ i ∈ (body.foldl trOp t).out, i.readShr = i
  | [], _, h, _ => h
  | op :: ops, t, h, hn => by
    apply readShr_foldl ops (trOp t op) _ (by cases op <;> simp_all [NoShift])
    cases op <;> simp_all [NoShift, trOp, TSt.push, Instr.readShr, or_imp]

/-- For a block without `shr` and `shrr`, `Instr.readShr` fixes every line of
    `toAst`. -/
theorem map_readShr_toAst {n w : Nat} (name : String) (body : List TileOp) (res : String)
    (hn : NoShift body = true) :
    (toAst n w name body res).body.map Instr.readShr = (toAst n w name body res).body := by
  have h := readShr_foldl body TSt.init (by simp [TSt.init]) hn
  exact (List.map_congr_left h).trans (List.map_id _)

/-- **Semantic preservation, specification text.** For a supported block without
    `shr` and `shrr`, the function `toAst n w name body res` evaluated on the
    tiles in registers `a` and `b` of `st` returns the value `runTileBlock` leaves
    in `res`. -/
theorem run_toAst {n w : Nat} (name : String) (body : List TileOp) (res : String)
    (hs : SupportedFunc w body res = true) (hn : NoShift body = true) (st : TileState n w) :
    (toAst n w name body res).run (st.get "a") (st.get "b")
      = some ((runTileBlock st body).get res) := by
  have := run_readShr_toAst name body res hs st
  simp only [Func.run, Func.readShr] at this ⊢
  rwa [map_readShr_toAst name body res hn] at this

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
def Mn.all : List Mn := [.addi, .subi, .muli, .andi, .ori, .xori, .shli, .shri, .shrui, .mulhi]

/-- The mnemonic with the given characters. -/
def Mn.ofChars (cs : List Char) : Option Mn := Mn.all.find? fun m => m.name.toList == cs

/-- The operand list and type of a two-operand form, after the mnemonic. -/
def parseBinTail (n w : Nat) (s : List Char) : Option (Opnd × Opnd × Bool × List Char) := do
  let s ← expect " ".toList s
  let (x, s) ← parseOpnd s
  let s ← expect ", ".toList s
  let (y, s) ← parseOpnd s
  match expect " unsigned : ".toList s with
  | some s => do
    let s ← expect (tyStr n w).toList s
    pure (x, y, true, s)
  | none => do
    let s ← expect " : ".toList s
    let s ← expect (tyStr n w).toList s
    pure (x, y, false, s)

/-- One body line, from its leading spaces to the end of its type. -/
def parseInstr (n w : Nat) (s : List Char) : Option (Instr × List Char) := do
  let s ← expect "  ".toList s
  let s ← expect "%v".toList s
  let (r, s) ← parseNat s
  let s ← expect " = cuda_tile.".toList s
  let (tok, s) := span Char.isLower s
  if tok = "constant".toList then do
    let s ← expect " dense<".toList s
    let (k, s) ← parseInt s
    let s ← expect "> : ".toList s
    let s ← expect (tyStr n w).toList s
    pure (.const r k, s)
  else if tok = "broadcast".toList then do
    let s ← expect " ".toList s
    let (x, s) ← parseOpnd s
    let s ← expect " {lane = ".toList s
    let (k, s) ← parseNat s
    let s ← expect "} : ".toList s
    let s ← expect (tyStr n w).toList s
    pure (.broadcast r x k, s)
  else if tok = "reduce".toList then do
    let s ← expect " ".toList s
    let (x, s) ← parseOpnd s
    let s ← expect " {op = \"add\"} : ".toList s
    let s ← expect (tyStr n w).toList s
    pure (.reduceAdd r x, s)
  else if tok = "permute".toList then do
    let (x, y, u, s) ← parseBinTail n w s
    if u then none else pure (.permute r x y, s)
  else do
    let mn ← Mn.ofChars tok
    let (x, y, u, s) ← parseBinTail n w s
    if u then (if mn = .shri then pure (.shriU r x y, s) else none)
    else pure (.bin mn r x y, s)

/-- The body lines and the return line, each preceded by a newline, then the
    closing brace and the final newline. `fuel` bounds the number of lines. -/
def parseBody (n w : Nat) : Nat → List Char → Option (List Instr × Opnd)
  | 0, _ => none
  | fuel + 1, s => do
    let s ← expect "\n".toList s
    match expect "  return ".toList s with
    | some s => do
      let (o, s) ← parseOpnd s
      let s ← expect " : ".toList s
      let s ← expect (tyStr n w).toList s
      let s ← expect "\n".toList s
      let s ← expect "}".toList s
      let s ← expect "\n".toList s
      if s = [] then pure ([], o) else none
    | none => do
      let (i, s) ← parseInstr n w s
      let (is, o) ← parseBody n w fuel s
      pure (i :: is, o)

/-- The tile type `!cuda_tile.tile<n x i w>`. -/
def parseTy (s : List Char) : Option (Nat × Nat × List Char) := do
  let s ← expect "!cuda_tile.tile<".toList s
  let (n, s) ← parseNat s
  let s ← expect "xi".toList s
  let (w, s) ← parseNat s
  let s ← expect ">".toList s
  pure (n, w, s)

/-- A function, from the characters of its text. -/
def parseFunc (s : List Char) : Option Func := do
  let s ← expect "func.func @".toList s
  let (nm, s) := span isIdChar s
  let s ← expect "(%a: ".toList s
  let (n, w, s) ← parseTy s
  let s ← expect ", %b: ".toList s
  let s ← expect (tyStr n w).toList s
  let s ← expect ") -> ".toList s
  let s ← expect (tyStr n w).toList s
  let s ← expect " {".toList s
  let (body, ret) ← parseBody n w s.length s
  pure ⟨String.ofList nm, n, w, body, ret⟩

/-- Parse the text of a function. -/
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
    mn.name.toList ≠ "constant".toList ∧ mn.name.toList ≠ "broadcast".toList ∧
      mn.name.toList ≠ "reduce".toList ∧ mn.name.toList ≠ "permute".toList := by
  cases mn <;> simp [Mn.name]

theorem expect_unsigned_colon (r : List Char) : expect " unsigned : ".toList (" : ".toList ++ r) = none := by
  simp [expect]

theorem parseBinTail_plain (n w : Nat) (x y : Opnd) (r : List Char) :
    parseBinTail n w (" ".toList ++ (x.print.toList ++ (", ".toList ++ (y.print.toList ++
      (" : ".toList ++ ((tyStr n w).toList ++ r)))))) = some (x, y, false, r) := by
  simp only [parseBinTail, Option.bind_eq_bind, Option.bind_some, Option.pure_def, expect_append,
    parseOpnd_off x ", ".toList _ (by decide), parseOpnd_off y " : ".toList _ (by decide),
    expect_unsigned_colon]

theorem parseBinTail_unsigned (n w : Nat) (x y : Opnd) (r : List Char) :
    parseBinTail n w (" ".toList ++ (x.print.toList ++ (", ".toList ++ (y.print.toList ++
      (" unsigned : ".toList ++ ((tyStr n w).toList ++ r)))))) = some (x, y, true, r) := by
  simp only [parseBinTail, Option.bind_eq_bind, Option.bind_some, Option.pure_def, expect_append,
    parseOpnd_off x ", ".toList _ (by decide), parseOpnd_off y " unsigned : ".toList _ (by decide)]

/-- **The parser reads back a printed line**, followed by any text. -/
theorem parseInstr_print (n w : Nat) (i : Instr) (r : List Char) :
    parseInstr n w ((i.print n w).toList ++ r) = some (i, r) := by
  have h0 := fun k => parseNat_off k " = cuda_tile.".toList
  cases i with
  | const k v =>
    simp only [Instr.print, vName, String.toList_append, List.append_assoc,
      Nat.toString_eq_repr, Nat.toList_repr, Int.toString_eq_repr, parseInstr,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, expect_append, h0 k _ (by decide),
      span_off Char.isLower "constant".toList " dense<".toList _ (by decide) (by decide),
      parseInt_off v "> : ".toList _ (by decide), if_true]
  | bin mn k x y =>
    simp only [Instr.print, vName, String.toList_append, List.append_assoc,
      Nat.toString_eq_repr, Nat.toList_repr, parseInstr,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, expect_append, h0 k _ (by decide),
      span_off Char.isLower mn.name.toList " ".toList _ (Mn.name_lower mn) (by decide),
      (Mn.name_ne mn).1, (Mn.name_ne mn).2.1, (Mn.name_ne mn).2.2.1, (Mn.name_ne mn).2.2.2,
      if_false, Mn.ofChars_name, parseBinTail_plain, Bool.false_eq_true]
  | shriU k x y =>
    simp only [Instr.print, vName, String.toList_append, List.append_assoc,
      Nat.toString_eq_repr, Nat.toList_repr, parseInstr,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, expect_append, h0 k _ (by decide),
      span_off Char.isLower "shri".toList " ".toList _ (by decide) (by decide),
      show "shri".toList ≠ "constant".toList by decide,
      show "shri".toList ≠ "broadcast".toList by decide,
      show "shri".toList ≠ "reduce".toList by decide,
      show "shri".toList ≠ "permute".toList by decide,
      show Mn.ofChars "shri".toList = some .shri from Mn.ofChars_name .shri,
      if_false, if_true, parseBinTail_unsigned]
  | permute k x y =>
    simp only [Instr.print, vName, String.toList_append, List.append_assoc,
      Nat.toString_eq_repr, Nat.toList_repr, parseInstr,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, expect_append, h0 k _ (by decide),
      span_off Char.isLower "permute".toList " ".toList _ (by decide) (by decide),
      show "permute".toList ≠ "constant".toList by decide,
      show "permute".toList ≠ "broadcast".toList by decide,
      show "permute".toList ≠ "reduce".toList by decide,
      if_false, if_true, parseBinTail_plain, Bool.false_eq_true]
  | broadcast k x m =>
    simp only [Instr.print, vName, String.toList_append, List.append_assoc,
      Nat.toString_eq_repr, Nat.toList_repr, parseInstr,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, expect_append, h0 k _ (by decide),
      span_off Char.isLower "broadcast".toList " ".toList _ (by decide) (by decide),
      show "broadcast".toList ≠ "constant".toList by decide,
      parseOpnd_off x " {lane = ".toList _ (by decide),
      parseNat_off m "} : ".toList _ (by decide), if_false, if_true]
  | reduceAdd k x =>
    simp only [Instr.print, vName, String.toList_append, List.append_assoc,
      Nat.toString_eq_repr, Nat.toList_repr, parseInstr,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, expect_append, h0 k _ (by decide),
      span_off Char.isLower "reduce".toList " ".toList _ (by decide) (by decide),
      show "reduce".toList ≠ "constant".toList by decide,
      show "reduce".toList ≠ "broadcast".toList by decide,
      parseOpnd_off x " {op = \"add\"} : ".toList _ (by decide), if_false, if_true]

theorem expect_self (p : List Char) : expect p p = some [] := by
  simpa using expect_append p []

theorem parseTy_tyStr (n w : Nat) (r : List Char) :
    parseTy ((tyStr n w).toList ++ r) = some (n, w, r) := by
  unfold tyStr
  simp only [String.toList_append, List.append_assoc, Nat.toString_eq_repr,
    Nat.toList_repr, parseTy, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    expect_append, parseNat_off n "xi".toList _ (by decide),
    parseNat_off w ">".toList _ (by decide)]

/-- The characters after the header line: each body line and the return line,
    each after a newline, then a newline, the closing brace and a newline. -/
def bodyText (n w : Nat) : List Instr → Opnd → List Char
  | [], o => "\n".toList ++ ("  return ".toList ++ (o.print.toList ++ (" : ".toList ++
      ((tyStr n w).toList ++ ("\n".toList ++ ("}".toList ++ "\n".toList))))))
  | i :: is, o => "\n".toList ++ ((i.print n w).toList ++ bodyText n w is o)

theorem expect_return_line (n w : Nat) (i : Instr) (r : List Char) :
    expect "  return ".toList ((i.print n w).toList ++ r) = none := by
  have h : ∀ X, expect "  return ".toList ("  ".toList ++ ("%v".toList ++ X)) = none := by
    intro X; simp [expect]
  cases i <;> simp only [Instr.print, vName, String.toList_append, List.append_assoc, h]

theorem parseBody_bodyText (n w : Nat) :
    ∀ (body : List Instr) (o : Opnd) (fuel : Nat), body.length < fuel →
      parseBody n w fuel (bodyText n w body o) = some (body, o)
  | [], o, fuel + 1, _ => by
    simp only [bodyText, parseBody, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      expect_append, expect_self, parseOpnd_off o " : ".toList _ (by decide), if_true]
  | i :: is, o, fuel + 1, h => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at h
    simp only [bodyText, parseBody, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      expect_append, expect_return_line, parseInstr_print, parseBody_bodyText n w is o fuel h]

theorem length_bodyText (n w : Nat) (body : List Instr) (o : Opnd) :
    body.length < (bodyText n w body o).length := by
  induction body with
  | nil => simp [bodyText]
  | cons i is ih => simp only [bodyText, List.length_cons, List.length_append]; simp; omega

theorem toList_intercalate_newline (h : String) (l : List String) :
    (String.intercalate "\n" (h :: l)).toList
      = h.toList ++ (l.map fun x => "\n".toList ++ x.toList).flatten := by
  induction l generalizing h with
  | nil => simp [String.intercalate_singleton]
  | cons x l ih =>
    rw [String.intercalate_cons_cons, String.toList_append, String.toList_append, ih]
    simp [List.append_assoc]

theorem print_toList (f : Func) : f.print.toList = f.header.toList ++ bodyText f.n f.w f.body f.ret := by
  have key : ∀ body : List Instr,
      ((body.map (Instr.print f.n f.w) ++ [f.footer, "}"]).map
          fun x => "\n".toList ++ x.toList).flatten ++ "\n".toList
        = bodyText f.n f.w body f.ret := by
    intro body
    induction body with
    | nil =>
      simp only [List.nil_append, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, bodyText, Func.footer, String.toList_append, List.append_assoc,
        List.append_nil]
    | cons i is ih =>
      simp only [List.map_cons, List.cons_append, List.flatten_cons, bodyText, ← ih,
        List.append_assoc]
  rw [Func.print, String.toList_append, toList_intercalate_newline, List.append_assoc, key]

/-- **The parser inverts the printer.** For every AST whose function name consists
    of symbol characters, parsing its printed text returns it. -/
theorem parse_print (f : Func) (hname : f.name.toList.all isIdChar = true) :
    parse f.print = some f := by
  have hlen := length_bodyText f.n f.w f.body f.ret
  unfold parse parseFunc
  rw [print_toList]
  unfold Func.header
  simp only [String.toList_append, List.append_assoc, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, expect_append,
    span_off isIdChar f.name.toList "(%a: ".toList _ hname (by decide), parseTy_tyStr,
    parseBody_bodyText f.n f.w f.body f.ret _ hlen, String.ofList_toList]

/-- The printed text determines the AST, for function names of symbol characters. -/
theorem print_injective {f g : Func} (hf : f.name.toList.all isIdChar = true)
    (hg : g.name.toList.all isIdChar = true) (h : f.print = g.print) : f = g := by
  have := parse_print f hf
  rw [h, parse_print g hg] at this
  exact (Option.some.inj this).symm

/-! ## 8. The BabyBear multiply -/

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileDialectLower
  (lowerCom lowerExpr binE constE varLevel bbName bbName_injective bbMulTileCom bbMulTileComIR
    bbMulTileCom_lowered_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialectModelTie (toTileOp)

theorem bbName_beq (i j : Nat) : (bbName i == bbName j) = decide (i = j) := by
  rw [Bool.eq_iff_iff]
  simp [bbName_injective.eq_iff]

/-- A body with a line that has no meaning for any environment has no value. -/
theorem execBody_eq_none_of_mem {n w : Nat} {i : Instr} (hi : ∀ ρ : Env n w, i.exec ρ = none) :
    ∀ (l : List Instr) (ρ : Env n w), i ∈ l → execBody ρ l = none
  | [], _, h => absurd h List.not_mem_nil
  | j :: l, ρ, h => by
    rw [execBody_cons]
    rcases List.mem_cons.mp h with rfl | h
    · rw [hi]; rfl
    · cases j.exec ρ with
      | none => rfl
      | some ρ' => exact execBody_eq_none_of_mem hi l ρ' h

/-- A function whose body has a `shrui` line has no value on any arguments. -/
theorem run_eq_none_of_shrui (f : Func) {r : Nat} {x y : Opnd} (h : .bin .shrui r x y ∈ f.body)
    (a b : Tile f.n f.w) : f.run a b = none := by
  rw [Func.run, execBody_eq_none_of_mem (i := .bin .shrui r x y)
    (fun _ => by simp [Instr.exec, Mn.sem]) _ _ h]
  rfl

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
  simp [lowerCom, lowerExpr, bbMulTileCom, binE, constE, varLevel, toTileOp, bbMulBlk]

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

/-- The BabyBear text has `shrui` lines, so under the specification semantics it has
    no value on any arguments. -/
theorem bbMulAst_run_eq_none (x y : Tile 8 64) : bbMulAst.run x y = none := by
  refine run_eq_none_of_shrui bbMulAst (r := 7) (x := .v 6) (y := .v 3) ?_ x y
  simp [bbMulAst, toAst, trOp, TSt.push, TSt.opnd, TSt.init_bbName, bbMulBlk, List.lookup,
    bbName_beq]

/-- **The BabyBear text computes `bbMulWord` in every lane**, with its right shifts
    read as `shri … unsigned`. -/
theorem bbMulAst_readShr_run (x y : Tile 8 64) :
    bbMulAst.readShr.run x y = some fun i => bbMulWord (x i) (y i) := by
  have h := run_readShr_toAst (n := 8) (w := 64) "bb_mul_tile_com" bbMulBlk (bbName 18)
    bbMulBlk_supported (bbMulInit x y)
  rw [bbMulTileCom_lowered_denote x y lowerCom_bbMulTileCom] at h
  exact h

/-- **End to end.** The emitted `cuda_tile` text of the BabyBear multiply parses to
    `bbMulAst`; with its right shifts read as `shri … unsigned`, its value on `x`, `y`
    is a tile whose lane `i` is `x i · y i mod p` whenever `x i, y i < p = 2013265921`. -/
theorem bbMulTileComIR_correct :
    parse bbMulTileComIR = some bbMulAst ∧ ∀ x y : Tile 8 64, ∃ t : Tile 8 64,
      bbMulAst.readShr.run x y = some t ∧ ∀ i, (x i).toNat < 2013265921 →
        (y i).toNat < 2013265921 → (t i).toNat = (x i).toNat * (y i).toNat % 2013265921 :=
  ⟨parse_bbMulTileComIR, fun x y =>
    ⟨_, bbMulAst_readShr_run x y, fun _ hx hy =>
      CatCrypt.Crypto.SecureCompilation.TileBackend.TileArithCorrect.bbMulWord_toNat _ _ hx hy⟩⟩

end CatCrypt.Crypto.SecureCompilation.TileBackend.CudaTileSemantics

end
