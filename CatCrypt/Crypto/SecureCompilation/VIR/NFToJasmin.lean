/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
public import CatCrypt.Crypto.SecureCompilation.VIR.JazzAsmSem
public import CatCrypt.Crypto.SecureCompilation.VIR.SarCount
public import CatCrypt.Crypto.Jasmin.JazzUnit
public import CatCrypt.Crypto.Jasmin.JazzRoundTrip
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminSpillPass
public import Mathlib.Data.List.Dedup

/-!
# Structured programs to Jasmin compilation units

`nfToJasmin` maps a structured program `NFProg jasminDialect Γ [t]` of the region back
half to a Jasmin compilation unit `JazzUnit` with one `export fn`, by structural recursion
on the program (`nfToJasminBody`), with one equation per constructor as in `exportR`.

## Names

A variable of the unit is `mkV c k s`: the name `nameOf c k s` is the character `c`, the
decimal `k` and, unless `s` is `u64`, the suffix `_` followed by the decimal code
`encS s` of the type; its type is `s`. The binding at depth `d` is `mkV 'r' d s`, which is
`regName d` at type `u64`; argument `j` is `mkV 'a' j s`, which is `argName j` at type
`u64`; the counter of the loop numbered `n` is `mkV 'c' n u64`; scratch registers are
`mkV 't' k s`, the index of a zeroing loop at depth `d` is `mkV 'i' d int`, and the carry
flag is `cfVar`, named `cf`. A name determines its type (`goodV_inj`), so each name is
declared once at one type. The depths follow `exportR`: a counted loop at depth `d` keeps
its trip index at `d` and its carried tuple at the block `d + 1, …`, which the continuation
reads at `d, …` after a shift; an exit-flag loop and a branch keep their tuple at `d, …`;
parallel assignments stage through the names `D, D + 1, …` above the depth `D` at the
return of the region (`parMovesJ`).

The environment `env` maps the de Bruijn index of a variable of the context to its Jasmin
variable. A store `stackStore` or `stackStoreImm` writes its array operand in place and
binds the result to that operand's variable; `linearArrB` accepts the programs in which
the stored array is bound in the region of the store and is not read after it.

## Operations

The binding of an operation of the fragment of `RegionExportable` (`OpPlain`) is emitted
in two-address form, at the word size of its width, and a `reg 1` value held as a `0`/`1`
word of type `u64`. `jasminWidthsB` accepts the widths `8`, `16`, `32`, `64` of the x86
general-purpose registers, `32` and `64` for `andn` and `mulhi`, and `1` only for a value
that a comparison, a carry-out, a cast or a constant produces:

* `regArith op w`: `x = a; x = x OP b`; `andn` is `_, _, _, _, _, x = #ANDN_w(a, b)`.
* `regConst w n`: `x = n mod 2^w`.
* `shrImm w n`, `shlImm w n`: `x = a; x = x >> m` (`<<`) with `m = shiftMask w n`.
* `sarImm w n`: `x = a; x = x >>s m` with `m = sarCount w n = min n (w - 1)`.
  `BitVec.sshiftRight a n` is the shift by `sarCount w n` (`sshiftRight_sarCount` of
  `VIR/SarCount`), so every count is emitted and none is refused.
* `castW w w'`: `x = (w'u) a`, followed by `x = x & 1` when `w' = 1`.
* `stackLoad`, `stackStore`, `stackStoreImm`: `x = A[(uint) i]`, `A[(uint) i] = v`,
  `A[k] = v`, the stores in place.
* `stackZero w n`: `for i = 0 to n { x[i] = 0; }`.
* `mulhi w`: `_, x = #MULX_lo_hi_w(a, b)`, the low word first.
* `addCarryLo w`, `addCarryHi w`: the carry-in word is moved to the flag by
  `#ADD_64(cin, -1)`, the word is `#ADC_w(a, b, cf)`, and the carry-out is materialised by
  `#ADC_64(0, 0, cf)`.
* `cmp c w`, `cmpImm c w n`: the carry of `#NEG_w(a ^ b)` (`eq`, `ne`) or of `#CMP_w`
  (orderings), materialised by `#ADC_64(0, 0, cf)` and flipped by `^ 1` for the
  complemented codes.
* `select w`: the mask select `x = a; x = x ^ b; x = x & m; x = x ^ b` with `m = -c`.

The asm operations are operations of `JazzAsmSem.jazzOps` (`emitOp_asmOps`). A counted loop is `ctr = count; i = 0; while (ctr != 0) { body; moves;
i += 1; ctr -= 1 }`, an exit-flag loop `while { body; flag = …; moves } (flag != 0)`, a
branch `if (c != 0) { …; moves } else { …; moves }`, and a call `Ccall DoNotInline`.

## Erased units

`cmdErasedB` checks the fixed-point condition of the erasure `Cmd.erase` of the single
Jasmin printer (`JazzRoundTrip`): every assignment tag is `AT_none`, every call is
`DoNotInline`, every `VarInfo` is the default, an `_` result of an asm operation carries
the type `opnNoneTys` gives it (`u64` elsewhere), and no assignment has the right-hand side
`Parr_init`. A command that passes the check is its own erasure (`cmdErase_of`).

## Main definitions

* `JazzSig`, `JazzSig.Fits`, `JazzSig.fitsB`: the surface signature of the function and
  its agreement with the context.
* `nfToJasminBody`, `nfToJasmin`: the lowering of a region and of a whole program; the
  latter applies the spill pass `JasminSpill.spillUnit spillK` to the unit it builds.
* `linearArrB`: the programs whose in-place stores are not observed.
* `jasminWidthsB`: the programs whose words are those of the x86 general-purpose
  registers.
* `cmdErasedB`: the commands the erasure leaves unchanged.

## Main results

* `nfToJasmin_isSome`: `nfToJasmin` succeeds on every program of `RegionExportable` that
  `linearArrB` and `jasminWidthsB` accept, under `JazzSig.Fits`.
* `nfToJasmin_erase`: the erasure of every unit `nfToJasmin` returns is that unit without
  its extern signatures.
* `cmdErase_of`: a command that passes `cmdErasedB` is its own erasure.
* `emitOp_asmOps`: every asm operation the lowering emits is an operation of `jazzOps`.
* `erase_spillFn`: the spill pass keeps a function with an erased body its own erasure.
* `mkUnit_finish_wellFormed`: the unit of a lowered program before the spill pass is well
  formed; `JasminSpill.nfToJasmin_wellFormed` states it for every unit `nfToJasmin` returns.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (varIndex)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
  (RegionExportable BindMemN wordSig)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop (OpPlain)
open CatCrypt.Crypto.SecureCompilation.VIR.JazzAsmSem (jazzOps)
open CatCrypt.Crypto.Jasmin (SType WSize PExpr LVal InstrR Cmd FunDecl FunParam VarI GVar
  FunName AssgnTag SOp1 SOp2 SOpn AsmOp InlineInfo LoopDir ArrAccess VarInfo Range)
open CatCrypt.Crypto.Jasmin.Jazz (Storage PType Decl ExternSig JazzFn JazzUnit cmdVars
  instrVars pexprVars pexprsVars lvalVars lvalsVars cmdCalls instrCalls eraseInstr eraseExpr
  eraseExprs eraseLval eraseVarI eraseGVar isZeroInit opnName)
open CatCrypt.Crypto.Jasmin.JazzToInstrR (opnNoneTys retypeGo retypeOpnLvs)

/-- A Jasmin variable. -/
abbrev JVar := CatCrypt.Crypto.Jasmin.Var

/-! ## 1. Names -/

/-- The index of a word size. -/
def wsIdx : WSize → Nat
  | .U8 => 0 | .U16 => 1 | .U32 => 2 | .U64 => 3 | .U128 => 4 | .U256 => 5 | .U512 => 6

/-- The code of a type. -/
def encS : SType → Nat
  | .sbool => 0 | .sint => 1 | .sword ws => 2 + wsIdx ws | .sarr n => 9 + n

theorem encS_inj {s s' : SType} (h : encS s = encS s') : s = s' := by
  cases s <;> cases s' <;> simp only [encS] at h <;> first | rfl | omega | skip
  all_goals (rename_i a b; cases a <;> cases b <;> simp_all [wsIdx] <;> omega)

/-- The suffix of a name of type `s`: empty for `u64`, `_` and the code of `s` otherwise. -/
def sfx (s : SType) : String := if s = .sword .U64 then "" else "_" ++ toString (encS s)

/-- The name with the prefix `c`, the number `k` and the type `s`. -/
def nameOf (c : Char) (k : Nat) (s : SType) : String :=
  String.singleton c ++ toString k ++ sfx s

/-- The variable with the prefix `c`, the number `k` and the type `s`. -/
def mkV (c : Char) (k : Nat) (s : SType) : JVar := ⟨nameOf c k s, s⟩

/-- The carry flag `cf`. -/
def cfVar : JVar := ⟨"cf", .sbool⟩

/-- The `u64` type. -/
abbrev u64 : SType := .sword .U64

/-- The variable read for an index outside the environment. -/
def dfltV : JVar := mkV 't' 99 u64

/-- The variables of the lowering: the carry flag and the variables `mkV c k s`. -/
def GoodV (v : JVar) : Prop := v = cfVar ∨ ∃ c k s, v = mkV c k s

@[simp] theorem goodV_mkV (c : Char) (k : Nat) (s : SType) : GoodV (mkV c k s) :=
  Or.inr ⟨c, k, s, rfl⟩

@[simp] theorem goodV_cfVar : GoodV cfVar := Or.inl rfl

theorem toDigits_ten_inj {k k' : Nat} (h : Nat.toDigits 10 k = Nat.toDigits 10 k') :
    k = k' := by
  rw [← Nat.ofDigitChars_ten_toDigits (n := k), h, Nat.ofDigitChars_ten_toDigits]

theorem digits_split : ∀ (xs ys X Y : List Char), (∀ c ∈ xs, c.isDigit) →
    (∀ c ∈ ys, c.isDigit) → (X = [] ∨ X.head? = some '_') → (Y = [] ∨ Y.head? = some '_') →
    xs ++ X = ys ++ Y → xs = ys ∧ X = Y
  | [], [], _, _, _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], y :: ys, X, Y, _, hy, hX, _, h => by
      exfalso; subst h
      have := hy y (by simp)
      rcases hX with h | h <;> simp_all
  | x :: xs, [], X, Y, hx, _, _, hY, h => by
      exfalso; subst h
      have := hx x (by simp)
      rcases hY with h | h <;> simp_all
  | x :: xs, y :: ys, X, Y, hx, hy, hX, hY, h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := digits_split xs ys X Y (fun c hc => hx c (by simp [hc]))
        (fun c hc => hy c (by simp [hc])) hX hY h
      exact ⟨by rw [this.1], this.2⟩

theorem toList_nameOf (c : Char) (k : Nat) (s : SType) :
    (nameOf c k s).toList = c :: (Nat.toDigits 10 k ++
      (if s = .sword .U64 then [] else '_' :: Nat.toDigits 10 (encS s))) := by
  unfold nameOf sfx
  split <;> simp [String.toList_append, Nat.toString_eq_repr, Nat.toList_repr]

/-- A name determines its prefix, its number and its type. -/
theorem nameOf_inj {c c' : Char} {k k' : Nat} {s s' : SType}
    (h : nameOf c k s = nameOf c' k' s') : c = c' ∧ k = k' ∧ s = s' := by
  have h2 := congrArg String.toList h
  rw [toList_nameOf, toList_nameOf] at h2
  simp only [List.cons.injEq] at h2
  obtain ⟨rfl, h2⟩ := h2
  have hd : ∀ n, ∀ c ∈ Nat.toDigits 10 n, c.isDigit := fun n c hc =>
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  obtain ⟨h3, h4⟩ := digits_split _ _ _ _ (hd k) (hd k') (by split <;> simp)
    (by split <;> simp) h2
  refine ⟨rfl, toDigits_ten_inj h3, ?_⟩
  split at h4 <;> split at h4
  · subst_vars; rfl
  · simp at h4
  · simp at h4
  · simp only [List.cons.injEq, true_and] at h4
    exact encS_inj (toDigits_ten_inj h4)

theorem cf_ne_nameOf (c : Char) (k : Nat) (s : SType) : "cf" ≠ nameOf c k s := by
  intro h
  have h2 := congrArg String.toList h
  rw [toList_nameOf] at h2
  have hd : ∀ c ∈ Nat.toDigits 10 k, c.isDigit := fun c hc =>
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (n := k) (b := 10))
  rw [hx] at h2 hd
  have := hd x (by simp)
  simp at h2
  obtain ⟨_, rfl, _⟩ := h2
  simp_all

/-- Two variables of the lowering with the same name are equal. -/
theorem goodV_inj {v w : JVar} (hv : GoodV v) (hw : GoodV w) (h : v.vname = w.vname) :
    v = w := by
  rcases hv with rfl | ⟨c, k, s, rfl⟩ <;> rcases hw with rfl | ⟨c', k', s', rfl⟩
  · rfl
  · exact absurd h (cf_ne_nameOf c' k' s')
  · exact absurd h.symm (cf_ne_nameOf c k s)
  · obtain ⟨rfl, rfl, rfl⟩ := nameOf_inj h; rfl

/-! ## 2. Surface types -/

/-- The word size of a dialect width: `w` itself for a width of `WSize`, `U64` otherwise
(a `reg 1` value is a `0`/`1` word). -/
def wsOf (w : Nat) : WSize :=
  if w = 8 then .U8 else if w = 16 then .U16 else if w = 32 then .U32
  else if w = 128 then .U128 else if w = 256 then .U256 else if w = 512 then .U512
  else .U64

/-- The surface type of a dialect type. -/
def ptyOf : JasminTy → PType
  | .reg w => .word (wsOf w)
  | .stackArr w n => .arr (wsOf w) n
  | .inlineInt => .int
  | .bool => .bool

/-- The Jasmin type of a dialect type. -/
def styOf (t : JasminTy) : SType := (ptyOf t).toSType

/-- The surface type declared for a variable of type `s`: an array of `n` bytes is
`u64[n / 8]` when `8` divides `n` and `u8[n]` otherwise. -/
def canonP : SType → PType
  | .sword ws => .word ws
  | .sbool => .bool
  | .sint => .int
  | .sarr n => if n % 8 = 0 then .arr .U64 (n / 8) else .arr .U8 n

theorem canonP_toSType (s : SType) : (canonP s).toSType = s := by
  cases s with
  | sarr n =>
      simp only [canonP]
      split
      · simp only [PType.toSType, WSize.bytes]; congr 1; omega
      · simp [PType.toSType, WSize.bytes]
  | _ => rfl

/-- The storage class declared for a variable of type `s`. -/
def storOf : SType → Storage
  | .sword _ | .sbool => .reg
  | .sint => .inlineVar
  | .sarr _ => .stack

/-! ## 3. Instructions -/

/-- The default variable information. -/
def vi0 : VarInfo := {}

/-- The expression of a local variable. -/
def pv (v : JVar) : PExpr := .Pvar ⟨⟨v, vi0⟩, false⟩

/-- The l-value of a variable. -/
def lvv (v : JVar) : LVal := .Lvar ⟨v, vi0⟩

/-- An integer constant. -/
def cnst (z : Int) : PExpr := .Pconst z

/-- The assignment `x = e` at the type of `x`. -/
def asgn (x : JVar) (e : PExpr) : InstrR := .Cassgn (lvv x) .AT_none x.vtype e

/-- The name of the asm operation `base` at the word size `ws`. -/
def asmName (base : String) (ws : WSize) : String := base ++ "_" ++ toString ws.bits

/-- The l-values of the outputs `outs` of an asm operation with the output types `tys`
from position `k`: `_` at the type of its position (`u64` past the end) for `none`. -/
def outLvs (tys : List SType) : Nat → List (Option JVar) → List LVal
  | _, [] => []
  | k, none :: outs => .Lnone vi0 ((tys[k]?).getD u64) :: outLvs tys (k + 1) outs
  | k, some v :: outs => lvv v :: outLvs tys (k + 1) outs

/-- The asm operation `o` with the outputs `outs` and the operands `es`; each `_` output
has the type `opnNoneTys` gives it, as the parser types it. -/
def copn (o : String) (outs : List (Option JVar)) (es : List PExpr) : InstrR :=
  .Copn (outLvs (opnNoneTys o outs.length) 0 outs) .AT_none (.Oasm ⟨o⟩) es

/-- The `b5w_ty` outputs with the carry flag `cf` and the word `x`. -/
def outsCW (x : JVar) : List (Option JVar) := [none, some cfVar, none, none, none, some x]

/-- The `b5w_ty` outputs with the word `x` only. -/
def outsW (x : JVar) : List (Option JVar) := [none, none, none, none, none, some x]

/-- A scratch register of the word size `ws`. -/
def tmp (k : Nat) (ws : WSize) : JVar := mkV 't' k (.sword ws)

/-- The `SOp2` of a binary operation other than `andn`. -/
def binSop (ws : WSize) : JasminBinOp → SOp2
  | .add => .Oadd ws | .sub => .Osub ws | .mul => .Omul ws | .and => .Oland ws
  | .or => .Olor ws | .xor => .Olxor ws | .shl => .Olsl ws | .shr => .Olsr ws
  | .andn => .Oland ws

/-- The cast `x = (w'u) a` from the width `w`: a zero extension to a larger word size, an
assignment otherwise, and `x = x & 1` for `w' = 1`. -/
def castCode (x a : JVar) (w w' : Nat) : Cmd :=
  (if (wsOf w).bits < (wsOf w').bits then [asgn x (.Papp1 (.Ozeroext (wsOf w') (wsOf w)) (pv a))]
    else [asgn x (pv a)])
  ++ (if w' = 1 then [asgn x (.Papp2 (.Oland .U64) (pv x) (cnst 1))] else [])

/-- The materialisation of the carry flag into the `0`/`1` word `x`. -/
def matCF (x : JVar) : Cmd := [asgn x (cnst 0), copn "ADC_64" (outsW x) [pv x, pv x, pv cfVar]]

/-- The comparison `x = cmpBit c a b` at the word size `ws`. -/
def cmpCode (c : JasminCmp) (ws : WSize) (x : JVar) (ea eb : PExpr) : Cmd :=
  let t := tmp 0 ws
  let t' := tmp 1 ws
  let neq := [asgn t ea, asgn t (.Papp2 (.Olxor ws) (pv t) eb),
    copn (asmName "NEG" ws) (outsCW t) [pv t]]
  let below (e1 e2 : PExpr) := [asgn t e1, asgn t' e2,
    copn (asmName "CMP" ws) [none, some cfVar, none, none, none] [pv t, pv t']]
  let flip := [asgn x (.Papp2 (.Olxor .U64) (pv x) (cnst 1))]
  match c with
  | .ne => neq ++ matCF x
  | .eq => neq ++ matCF x ++ flip
  | .ult => below ea eb ++ matCF x
  | .uge => below ea eb ++ matCF x ++ flip
  | .ugt => below eb ea ++ matCF x
  | .ule => below eb ea ++ matCF x ++ flip

/-- The carry-in word `cin` moved to the carry flag. -/
def cinCode (cin : JVar) : InstrR := copn "ADD_64" (outsCW (tmp 0 .U64)) [pv cin, cnst (-1)]

/-- The code of the binding of `op` at depth `d` to the fresh variable `x`, on the
operand variables `as`, with the variable that holds the result: `x`, or the array
operand of an in-place store. `none` for an operation outside `OpPlain`. -/
def emitOp (op : JasminOp) (d : Nat) (x : JVar) (as : List JVar) : Option (Cmd × JVar) :=
  let a0 := as.getD 0 dfltV
  let a1 := as.getD 1 dfltV
  let a2 := as.getD 2 dfltV
  match op with
  | .regArith .andn w =>
      some ([copn (asmName "ANDN" (wsOf w)) (outsW x) [pv a0, pv a1]], x)
  | .regArith bop w =>
      some ([asgn x (pv a0), asgn x (.Papp2 (binSop (wsOf w) bop) (pv x) (pv a1))], x)
  | .regConst w n => some ([asgn x (cnst ((n % 2 ^ w : Nat) : Int))], x)
  | .shrImm w n =>
      some ([asgn x (pv a0), asgn x (.Papp2 (.Olsr (wsOf w)) (pv x) (cnst (shiftMask w n)))], x)
  | .shlImm w n =>
      some ([asgn x (pv a0), asgn x (.Papp2 (.Olsl (wsOf w)) (pv x) (cnst (shiftMask w n)))], x)
  | .sarImm w n =>
      some ([asgn x (pv a0), asgn x (.Papp2 (.Oasr (wsOf w)) (pv x) (cnst (sarCount w n)))], x)
  | .rorImm w n =>
      some ([asgn x (pv a0), copn (asmName "ROR" (wsOf w)) [none, none, some x]
        [pv x, cnst ((n % w : Nat) : Int)]], x)
  | .castW w w' => some (castCode x a0 w w', x)
  | .stackLoad w _ =>
      some ([asgn x (.Pget .AAscale (wsOf w) ⟨⟨a0, vi0⟩, false⟩
        (.Papp1 (.Oint_of_word .U64) (pv a1)))], x)
  | .stackStore w _ =>
      some ([.Cassgn (.Laset .AAscale (wsOf w) ⟨a0, vi0⟩ (.Papp1 (.Oint_of_word .U64) (pv a1)))
        .AT_none (.sword (wsOf w)) (pv a2)], a0)
  | .stackStoreImm w _ k =>
      some ([.Cassgn (.Laset .AAscale (wsOf w) ⟨a0, vi0⟩ (cnst k)) .AT_none (.sword (wsOf w))
        (pv a1)], a0)
  | .stackZero w n =>
      let j := mkV 'i' d .sint
      some ([.Cfor ⟨j, vi0⟩ ⟨.UpTo, 0, n⟩
        [.Cassgn (.Laset .AAscale (wsOf w) ⟨x, vi0⟩ (pv j)) .AT_none (.sword (wsOf w))
          (cnst 0)]], x)
  | .mulhi w => some ([copn (asmName "MULX_lo_hi" (wsOf w)) [none, some x] [pv a0, pv a1]], x)
  | .addCarryLo w =>
      some ([cinCode a2, asgn x (pv a0),
        copn (asmName "ADC" (wsOf w)) (outsCW x) [pv x, pv a1, pv cfVar]], x)
  | .addCarryHi w =>
      let t := tmp 1 (wsOf w)
      some ([cinCode a2, asgn t (pv a0),
        copn (asmName "ADC" (wsOf w)) (outsCW t) [pv t, pv a1, pv cfVar]] ++ matCF x, x)
  | .cmp c w => some (cmpCode c (wsOf w) x (pv a0) (pv a1), x)
  | .cmpImm c w n => some (cmpCode c (wsOf w) x (pv a0) (cnst ((n % 2 ^ w : Nat) : Int)), x)
  | .select w =>
      let m := tmp 0 (wsOf w)
      some (castCode m a0 64 w ++ [asgn m (.Papp1 (.Oneg (wsOf w)) (pv m)),
        asgn x (pv a1), asgn x (.Papp2 (.Olxor (wsOf w)) (pv x) (pv a2)),
        asgn x (.Papp2 (.Oland (wsOf w)) (pv x) (pv m)),
        asgn x (.Papp2 (.Olxor (wsOf w)) (pv x) (pv a2))], x)
  | _ => none

/-- The parallel assignment of the pairs `(target, source)` with the temporaries from the
depth `D`: the pairs whose target is not their source, directly when no source is a target,
and otherwise staged through `mkV 'r' (D + j)` at the type of the target. -/
def parMovesJ (D : Nat) (pairs : List (JVar × JVar)) : Cmd :=
  let ps := pairs.filter fun p => p.1 != p.2
  if ps.all (fun q => ps.all fun p => q.2 != p.1) then ps.map fun p => asgn p.1 (pv p.2)
  else (ps.zipIdx.map fun q => asgn (mkV 'r' (D + q.2) q.1.1.vtype) (pv q.1.2))
    ++ ps.zipIdx.map fun q => asgn q.1.1 (pv (mkV 'r' (D + q.2) q.1.1.vtype))

/-! ## 4. The lowering of a region -/

/-- The de Bruijn indices of an argument vector. -/
def hvIdxs {Γ : Ctxt jasminDialect} : {ts : List JasminTy} →
    HVector (fun t => Ctxt.Var Γ t) ts → List Nat
  | [], _ => []
  | _ :: _, .cons v rest => varIndex v :: hvIdxs rest

/-- The variables of an argument vector in the environment `env`. -/
def resolveHV (env : List JVar) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (hv : HVector (fun t => Ctxt.Var Γ t) ts) : List JVar :=
  (hvIdxs hv).map fun i => env.getD i dfltV

/-- The block of variables of the types `cs` at the depths from `base`, in the order of
`carriedRegs`: position `j` at depth `base + (cs.length - 1 - j)`. -/
def blockVars (base : Nat) (cs : List JasminTy) : List JVar :=
  cs.zipIdx.map fun p => mkV 'r' (base + (cs.length - 1 - p.2)) (styOf p.1)

/-- The lowering of a region: its code, the variables it returns, the depth at its
return, and the next unused loop number. -/
structure JOut where
  /-- The code. -/
  code : Cmd
  /-- The variables of the returned values. -/
  res : List JVar
  /-- The depth at the return. -/
  depth : Nat
  /-- The next unused loop number. -/
  next : Nat

/-- The lowering `r` with the code `c` placed in front. -/
def JOut.pre (c : Cmd) (r : JOut) : JOut := { r with code := c ++ r.code }

/-- The condition `v != 0`. -/
def nz (v : JVar) : PExpr := .Papp2 (.Oneq .U64) (pv v) (cnst 0)

/-- The assignments of the pairs `(target, source)` in order. -/
def seqMoves (ps : List (JVar × JVar)) : Cmd := ps.map fun p => asgn p.1 (pv p.2)

/-- The frame of a counted loop at depth `d` with the loop number `n` and the carried
types `cs`, around the lowered body `b`: the seeds `inits` of the carried block
`blockVars (d + 1) cs`, the trip index `mkV 'r' d` from `0` and the counter `mkV 'c' n`
from the count of index `ci`; the loop `while (ctr != 0)` runs the body, the parallel
assignment of its results to the carried block, and the advance; after the loop the
carried block moves down to `blockVars d cs`. -/
def forCode (env : List JVar) (d n : Nat) (cs : List JasminTy) (inits : List JVar) (ci : Nat)
    (b : JOut) : Cmd :=
  let car := blockVars (d + 1) cs
  let idx := mkV 'r' d u64
  let ctr := mkV 'c' n u64
  seqMoves (car.zip inits)
  ++ [asgn idx (cnst 0), asgn ctr (pv (env.getD ci dfltV)),
      InstrR.Cwhile [] (nz ctr)
        (b.code ++ parMovesJ b.depth (car.zip b.res)
          ++ [asgn idx (.Papp2 (.Oadd .U64) (pv idx) (cnst 1)),
              asgn ctr (.Papp2 (.Osub .U64) (pv ctr) (cnst 1))])]
  ++ seqMoves ((blockVars d cs).zip car).reverse

/-- The branch at depth `d` with the result types `rs` on the condition of index `ci`, with
the lowered branches `bt` and `be`, each followed by the parallel assignment of its results
to the block `blockVars d rs`. -/
def ifCode (env : List JVar) (d : Nat) (rs : List JasminTy) (ci : Nat) (bt be : JOut) :
    InstrR :=
  InstrR.Cif (nz (env.getD ci dfltV))
    (bt.code ++ parMovesJ (bt.depth + rs.length) ((blockVars d rs).zip bt.res))
    (be.code ++ parMovesJ (be.depth + rs.length) ((blockVars d rs).zip be.res))

/-- The frame of an exit-flag loop at depth `d` with the carried types `cs` around the
lowered body `b`: the seeds `inits` of the carried block `blockVars d cs`, and the loop
`while { body; flag = bit; moves } (flag != 0)`, the flag at `mkV 'r' (b.depth + cs.length)`. -/
def whileCode (d : Nat) (cs : List JasminTy) (inits : List JVar)
    (b : JOut) : Cmd :=
  let car := blockVars d cs
  let flag := mkV 'r' (b.depth + cs.length) u64
  seqMoves (car.zip inits)
  ++ [InstrR.Cwhile (b.code ++ asgn flag (pv (b.res.headD dfltV))
        :: parMovesJ b.depth (car.zip b.res.tail)) (nz flag) []]

/-- **The lowering of a region.** `env` maps the de Bruijn indices of the context to their
variables, `d` is the depth of the next binding and `n` the next unused loop number. A
binding outside `OpPlain` and a call at a signature outside `wordSig` are refused. -/
def nfToJasminBody (env : List JVar) :
    {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts →
    (d n : Nat) → Option JOut
  | _, _, .ret vs, d, n => some ⟨[], resolveHV env vs, d, n⟩
  | _, _, .var (t := t) e k, d, n =>
      (emitOp e.op d (mkV 'r' d (styOf t)) (resolveHV env e.args)).bind fun cx =>
      (nfToJasminBody (cx.2 :: env) k (d + 1) n).map (JOut.pre cx.1)
  | _, _, .forLoop (cs := cs) count inits body k, d, n =>
      (nfToJasminBody (blockVars (d + 1) cs ++ mkV 'r' d u64 :: env) body (d + 1 + cs.length)
        (n + 1)).bind fun b =>
      (nfToJasminBody (blockVars d cs ++ env) k (d + cs.length) b.next).map
        (JOut.pre (forCode env d n cs (resolveHV env inits) (varIndex count) b))
  | _, _, .ifThenElse (rs := rs) cond thn els k, d, n =>
      (nfToJasminBody env thn d n).bind fun bt =>
      (nfToJasminBody env els d bt.next).bind fun be =>
      (nfToJasminBody (blockVars d rs ++ env) k (d + rs.length) be.next).map
        (JOut.pre [ifCode env d rs (varIndex cond) bt be])
  | _, _, .whileLoop (cs := cs) inits body k, d, n =>
      (nfToJasminBody (blockVars d cs ++ env) body (d + cs.length) n).bind fun b =>
      (nfToJasminBody (blockVars d cs ++ env) k (d + cs.length) b.next).map
        (JOut.pre (whileCode d cs (resolveHV env inits) b))
  | _, _, .call (as := as) (rs := rs) f args k, d, n =>
      if wordSig as rs = true then
        (nfToJasminBody (blockVars d rs ++ env) k (d + rs.length) n).map
          (JOut.pre [InstrR.Ccall .DoNotInline ((blockVars d rs).map lvv) ⟨f⟩
            ((resolveHV env args).map pv)])
      else none

/-! ## 5. The in-place store check -/

/-- Whether the variable of de Bruijn index `i` is read by a program. -/
def usesIdx : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Nat → Bool
  | _, _, .ret vs, i => (hvIdxs vs).contains i
  | _, _, .var e k, i => (hvIdxs e.args).contains i || usesIdx k (i + 1)
  | _, _, .forLoop (cs := cs) count inits body k, i =>
      varIndex count == i || (hvIdxs inits).contains i
        || usesIdx body (i + cs.length + 1) || usesIdx k (i + cs.length)
  | _, _, .ifThenElse (rs := rs) cond thn els k, i =>
      varIndex cond == i || usesIdx thn i || usesIdx els i || usesIdx k (i + rs.length)
  | _, _, .whileLoop (cs := cs) inits body k, i =>
      (hvIdxs inits).contains i || usesIdx body (i + cs.length) || usesIdx k (i + cs.length)
  | _, _, .call (rs := rs) _ args k, i => (hvIdxs args).contains i || usesIdx k (i + rs.length)

/-- The index of the array operand of an in-place store. -/
def storeSrc? : JasminOp → List Nat → Option Nat
  | .stackStore _ _, a :: _ => some a
  | .stackStoreImm _ _ _, a :: _ => some a
  | _, _ => none

/-- The in-place store check, with `loc` the number of innermost variables of the context
bound in the current region: the array operand of every store is one of them and is not
read after the store. -/
def linGo : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Nat → Bool
  | _, _, .ret _, _ => true
  | _, _, .var e k, loc =>
      (match storeSrc? e.op (hvIdxs e.args) with
        | some a => decide (a < loc) && !usesIdx k (a + 1)
        | none => true) && linGo k (loc + 1)
  | _, _, .forLoop (cs := cs) _ _ body k, loc =>
      linGo body (cs.length + 1) && linGo k (loc + cs.length)
  | _, _, .ifThenElse (rs := rs) _ thn els k, loc =>
      linGo thn 0 && linGo els 0 && linGo k (loc + rs.length)
  | _, _, .whileLoop (cs := cs) _ body k, loc =>
      linGo body cs.length && linGo k (loc + cs.length)
  | _, _, .call (rs := rs) _ _ k, loc => linGo k (loc + rs.length)

/-- The programs whose in-place stores are not observed: the arguments of the function
are bound in its outermost region. -/
def linearArrB {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) : Bool :=
  linGo p Γ.length

/-! ## 5b. The word sizes of the x86 registers -/

/-- A width of an x86 general-purpose register: `8`, `16`, `32` or `64`. -/
def widthOkB (w : Nat) : Bool := w == 8 || w == 16 || w == 32 || w == 64

/-- The width of a register value: a width of `widthOkB`, or `1`, a comparison result or a
carry bit, held as a `0`/`1` word. -/
def bitOkB (w : Nat) : Bool := w == 1 || widthOkB w

/-- A width at which x86 has `ANDN` and `MULX`: `32` or `64`. -/
def bmiOkB (w : Nat) : Bool := w == 32 || w == 64

/-- A dialect type whose registers have a width of `bitOkB` and whose array elements have a
width of `widthOkB`. -/
def tyOkB : JasminTy → Bool
  | .reg w => bitOkB w
  | .stackArr w _ => widthOkB w
  | _ => true

/-- An operation whose widths are register widths of x86: a width of `widthOkB` for every
arithmetic, shift, rotate, memory, comparison, carry and select operation, a width of `bmiOkB` for
`andn` and `mulhi`, and widths of `bitOkB` for `castW`. A `reg 1` value is thus produced by
a comparison, a carry-out, a cast to width `1` or a constant, and read by `select`, a carry-in
or a cast, and no other operation computes at width `1`. -/
def opOkB : JasminOp → Bool
  | .regArith .andn w | .mulhi w => bmiOkB w
  | .regArith _ w | .shrImm w _ | .shlImm w _ | .sarImm w _ | .rorImm w _ | .stackLoad w _
  | .stackStore w _ | .stackStoreImm w _ _ | .stackZero w _ | .addCarryLo w
  | .addCarryHi w | .cmp _ w | .cmpImm _ w _ | .select w => widthOkB w
  | .castW w w' => bitOkB w && bitOkB w'
  | _ => true

/-- The width check of a program: the type of every binding, of every carried value and
of every call result, and every operation width. -/
def widthsGo : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var (t := t) e k => tyOkB t && opOkB e.op && widthsGo k
  | _, _, .forLoop (cs := cs) _ _ body k => cs.all tyOkB && widthsGo body && widthsGo k
  | _, _, .ifThenElse (rs := rs) _ thn els k =>
      rs.all tyOkB && widthsGo thn && widthsGo els && widthsGo k
  | _, _, .whileLoop (cs := cs) _ body k => cs.all tyOkB && widthsGo body && widthsGo k
  | _, _, .call (rs := rs) _ _ k => rs.all tyOkB && widthsGo k

/-- The programs whose words are those of the x86 general-purpose registers: the types of
the context and of the results and the program pass `widthsGo`. -/
def jasminWidthsB {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) : Bool :=
  Γ.all tyOkB && ts.all tyOkB && widthsGo p

/-- `wsOf w` is `U512` exactly at the width `512`. -/
theorem wsOf_eq_U512_iff (w : Nat) : wsOf w = .U512 ↔ w = 512 := by
  unfold wsOf
  constructor
  · intro h; repeat' split at h
    all_goals first | assumption | cases h
  · rintro rfl; rfl

/-- A width that passes `bitOkB` passes `widthOkB` or is `1`. -/
theorem bitOkB_iff {w : Nat} : bitOkB w = true ↔ w = 1 ∨ widthOkB w = true := by
  simp [bitOkB]

/-- A width that passes `bitOkB` has a word size other than `U512`. -/
theorem wsOf_ne_U512_of_bit {w : Nat} (h : bitOkB w = true) : wsOf w ≠ .U512 := by
  rw [Ne, wsOf_eq_U512_iff]
  simp only [bitOkB, widthOkB, Bool.or_eq_true, beq_iff_eq] at h
  omega

/-- A width that passes `widthOkB` has a word size other than `U512`. -/
theorem wsOf_ne_U512 {w : Nat} (h : widthOkB w = true) : wsOf w ≠ .U512 :=
  wsOf_ne_U512_of_bit (by simp [bitOkB, h])

/-- A width that passes `bmiOkB` passes `widthOkB`. -/
theorem widthOkB_of_bmi {w : Nat} (h : bmiOkB w = true) : widthOkB w = true := by
  simp only [bmiOkB, widthOkB, Bool.or_eq_true, beq_iff_eq] at h ⊢
  omega

/-- The Jasmin type of a dialect type that passes `tyOkB` is not a 512-bit word. -/
theorem styOf_ne_U512 {t : JasminTy} (h : tyOkB t = true) : styOf t ≠ .sword .U512 := by
  cases t with
  | reg w =>
      simp only [styOf, ptyOf, PType.toSType, ne_eq, SType.sword.injEq]
      exact wsOf_ne_U512_of_bit h
  | _ => simp [styOf, ptyOf, PType.toSType]

mutual
/-- The names of the asm operations of an instruction. -/
def instrAsmOps : InstrR → List String
  | .Copn _ _ o _ => [opnName o]
  | .Cif _ t e => cmdAsmOps t ++ cmdAsmOps e
  | .Cfor _ _ b => cmdAsmOps b
  | .Cwhile b _ a => cmdAsmOps b ++ cmdAsmOps a
  | _ => []

/-- The names of the asm operations of a command. -/
def cmdAsmOps : List InstrR → List String
  | [] => []
  | i :: is => instrAsmOps i ++ cmdAsmOps is
end

/-- At the word sizes of the x86 general-purpose registers, `asmName base` is the name
`opName base` of `JazzAsmSem` at the mirror word size. -/
theorem asmName_eq_opName (base : String) :
    asmName base .U8 = JazzAsmSem.opName base .U8 ∧
      asmName base .U16 = JazzAsmSem.opName base .U16 ∧
      asmName base .U32 = JazzAsmSem.opName base .U32 ∧
      asmName base .U64 = JazzAsmSem.opName base .U64 := by
  have h : (toString (8 : Nat), toString (16 : Nat), toString (32 : Nat), toString (64 : Nat)) =
      ("8", "16", "32", "64") := by
    simp [Nat.repr_of_ge, Nat.repr_of_lt, Nat.digitChar_eq_six.mpr rfl,
      Nat.digitChar_eq_four.mpr rfl, Nat.digitChar_eq_eight.mpr rfl,
      Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_three.mpr rfl,
      Nat.digitChar_eq_two.mpr rfl]
  simp only [Prod.mk.injEq] at h
  obtain ⟨h8, h16, h32, h64⟩ := h
  simp only [asmName, JazzAsmSem.opName, JazzAsmSem.wsName, WSize.bits, h8, h16, h32, h64,
    and_self]

/-- The names `asmName base (wsOf w)` of the operations of `jazzOps` at a width `w`: `ADD`,
`ADC`, `NEG`, `CMP` at a width of `widthOkB`, `ANDN` and `MULX_lo_hi` at a width of
`bmiOkB`. -/
theorem asmName_mem_jazzOps {w : Nat} (hw : widthOkB w = true) :
    asmName "ADD" (wsOf w) ∈ jazzOps ∧ asmName "ADC" (wsOf w) ∈ jazzOps ∧
      asmName "NEG" (wsOf w) ∈ jazzOps ∧ asmName "CMP" (wsOf w) ∈ jazzOps ∧
      (bmiOkB w = true → asmName "ANDN" (wsOf w) ∈ jazzOps ∧
        asmName "MULX_lo_hi" (wsOf w) ∈ jazzOps) := by
  have hm : ∀ {b : String} {ws : CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize},
      (b, ws) ∈ JazzAsmSem.jazzRows → JazzAsmSem.opName b ws ∈ jazzOps :=
    fun h => List.mem_map_of_mem (f := fun r => JazzAsmSem.opName r.1 r.2) h
  have hn := asmName_eq_opName
  simp only [widthOkB, Bool.or_eq_true, beq_iff_eq] at hw
  rcases hw with ((rfl | rfl) | rfl) | rfl
  · rw [show wsOf 8 = .U8 from rfl, (hn _).1, (hn _).1, (hn _).1, (hn _).1]
    exact ⟨hm (by simp [JazzAsmSem.jazzRows]), hm (by simp [JazzAsmSem.jazzRows]),
      hm (by simp [JazzAsmSem.jazzRows]), hm (by simp [JazzAsmSem.jazzRows]),
      fun hb => by simp [bmiOkB] at hb⟩
  · rw [show wsOf 16 = .U16 from rfl, (hn _).2.1, (hn _).2.1, (hn _).2.1, (hn _).2.1]
    exact ⟨hm (by simp [JazzAsmSem.jazzRows]), hm (by simp [JazzAsmSem.jazzRows]),
      hm (by simp [JazzAsmSem.jazzRows]), hm (by simp [JazzAsmSem.jazzRows]),
      fun hb => by simp [bmiOkB] at hb⟩
  · rw [show wsOf 32 = .U32 from rfl, (hn _).2.2.1, (hn _).2.2.1, (hn _).2.2.1, (hn _).2.2.1,
      (hn _).2.2.1, (hn _).2.2.1]
    exact ⟨hm (by simp [JazzAsmSem.jazzRows]), hm (by simp [JazzAsmSem.jazzRows]),
      hm (by simp [JazzAsmSem.jazzRows]), hm (by simp [JazzAsmSem.jazzRows]),
      fun _ => ⟨hm (by simp [JazzAsmSem.jazzRows]), hm (by simp [JazzAsmSem.jazzRows])⟩⟩
  · rw [show wsOf 64 = .U64 from rfl, (hn _).2.2.2, (hn _).2.2.2, (hn _).2.2.2, (hn _).2.2.2,
      (hn _).2.2.2, (hn _).2.2.2]
    exact ⟨hm (by simp [JazzAsmSem.jazzRows]), hm (by simp [JazzAsmSem.jazzRows]),
      hm (by simp [JazzAsmSem.jazzRows]), hm (by simp [JazzAsmSem.jazzRows]),
      fun _ => ⟨hm (by simp [JazzAsmSem.jazzRows]), hm (by simp [JazzAsmSem.jazzRows])⟩⟩

/-- The name `asmName "ROR" (wsOf w)` at a width `w` of `widthOkB` is an operation of
`jazzOps`. -/
theorem asmName_ror_mem_jazzOps {w : Nat} (hw : widthOkB w = true) :
    asmName "ROR" (wsOf w) ∈ jazzOps := by
  have hm : ∀ {b : String} {ws : CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize},
      (b, ws) ∈ JazzAsmSem.jazzRows → JazzAsmSem.opName b ws ∈ jazzOps :=
    fun h => List.mem_map_of_mem (f := fun r => JazzAsmSem.opName r.1 r.2) h
  have hn := asmName_eq_opName "ROR"
  simp only [widthOkB, Bool.or_eq_true, beq_iff_eq] at hw
  rcases hw with ((rfl | rfl) | rfl) | rfl
  · rw [show wsOf 8 = .U8 from rfl, hn.1]; exact hm (by simp [JazzAsmSem.jazzRows])
  · rw [show wsOf 16 = .U16 from rfl, hn.2.1]; exact hm (by simp [JazzAsmSem.jazzRows])
  · rw [show wsOf 32 = .U32 from rfl, hn.2.2.1]; exact hm (by simp [JazzAsmSem.jazzRows])
  · rw [show wsOf 64 = .U64 from rfl, hn.2.2.2]; exact hm (by simp [JazzAsmSem.jazzRows])

/-- **The asm operations of the lowering are operations of `jazzOps`**: every asm operation
name in the code `emitOp` emits for an operation that passes `opOkB` is in `jazzOps`. -/
theorem emitOp_asmOps {op : JasminOp} {d : Nat} {x : JVar} {as : List JVar} {c : Cmd}
    {y : JVar} (h : emitOp op d x as = some (c, y)) (hop : opOkB op = true) :
    ∀ o ∈ cmdAsmOps c, o ∈ jazzOps := by
  have hA : "ADD_64" ∈ jazzOps := by
    simp [jazzOps, JazzAsmSem.jazzRows, JazzAsmSem.opName, JazzAsmSem.wsName]
  have hC : "ADC_64" ∈ jazzOps := by
    simp [jazzOps, JazzAsmSem.jazzRows, JazzAsmSem.opName, JazzAsmSem.wsName]
  cases op
  all_goals try (cases ‹JasminDialect.JasminBinOp›)
  all_goals try (cases ‹JasminDialect.JasminCmp›)
  all_goals simp [emitOp] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals simp only [opOkB] at hop
  all_goals first
    | (have hm := asmName_mem_jazzOps (widthOkB_of_bmi hop))
    | (have hm := asmName_mem_jazzOps hop)
    | skip
  all_goals simp only [castCode, matCF, cmpCode, cinCode, copn, cmdAsmOps, instrAsmOps, asgn,
    opnName, List.cons_append, List.nil_append, List.append_nil, List.append_assoc]
  all_goals repeat' split
  all_goals simp only [cmdAsmOps, instrAsmOps, List.nil_append, List.append_nil,
    List.cons_append, List.mem_cons, or_false, forall_eq_or_imp, forall_eq,
    List.mem_nil_iff, false_imp_iff, implies_true]
  all_goals obtain ⟨_, h2, h3, h4, h5⟩ := hm
  all_goals first
    | exact (h5 hop).1 | exact (h5 hop).2 | exact ⟨hA, h2⟩ | exact ⟨hA, h2, hC⟩
    | exact ⟨h3, hC⟩ | exact ⟨h4, hC⟩ | exact asmName_ror_mem_jazzOps hop

/-! ## 6. Signatures and units -/

/-- The surface signature of a function over the argument context `Γ` with the result
type `t`: the source name, storage class and surface type of each parameter in argument
order, the storage class and surface type of the result, and, for a result written to a
`reg mut ptr` parameter, the position of that parameter. -/
structure JazzSig (Γ : Ctxt jasminDialect) (t : JasminTy) where
  /-- The parameters. -/
  params : List (String × Storage × PType)
  /-- The result. -/
  result : Storage × PType
  /-- The parameter that holds the result, if any. -/
  resultParam : Option Nat
  /-- One parameter per argument. -/
  params_length : params.length = Γ.length

/-- A signature fits its context: the surface type of each parameter has the Jasmin type
of its argument, and the result is either of register storage at the type of `t` or a
`reg mut ptr` parameter at that type. -/
def JazzSig.Fits {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t) : Prop :=
  (∀ q ∈ sig.params.zip Γ.reverse, q.1.2.2.toSType = styOf q.2) ∧
  match sig.resultParam with
  | none => sig.result.1.isReg = true ∧ sig.result.2.toSType = styOf t
  | some j => ∃ q, sig.params[j]? = some q ∧ q.2.2.toSType = styOf t ∧ q.2.1 = .regPtr true

/-- The Boolean check of `JazzSig.Fits`. -/
def JazzSig.fitsB {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t) : Bool :=
  (sig.params.zip Γ.reverse).all (fun q => q.1.2.2.toSType == styOf q.2) &&
  match sig.resultParam with
  | none => sig.result.1.isReg && sig.result.2.toSType == styOf t
  | some j =>
      match sig.params[j]? with
      | some q => q.2.2.toSType == styOf t && q.2.1 == .regPtr true
      | none => false

theorem JazzSig.fitsB_iff {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t) :
    sig.fitsB = true ↔ sig.Fits := by
  unfold JazzSig.fitsB JazzSig.Fits
  rw [Bool.and_eq_true, List.all_eq_true]
  refine and_congr (by simp) ?_
  cases sig.resultParam with
  | none => simp
  | some j =>
      cases h : sig.params[j]? with
      | none => simp [h]
      | some q => obtain ⟨a, s, b⟩ := q; simp only [h]; simp [and_comm]

/-- The parameters of a signature: the variable `mkV 'a' j` of each argument at the type
of its surface type, with its storage class and surface type. -/
def paramPairs {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t) :
    List (JVar × Storage × PType) :=
  (List.range sig.params.length).map fun j =>
    let q := (sig.params[j]?).getD ("", .reg, .word .U64)
    (mkV 'a' j q.2.2.toSType, q.2)

mutual
/-- The first call of `f` in an instruction, with its l-values and arguments. -/
def instrCallOf (f : String) : InstrR → Option (List LVal × List PExpr)
  | .Ccall _ lvs g args => if g.name = f then some (lvs, args) else none
  | .Cif _ t e => (cmdCallOf f t).or (cmdCallOf f e)
  | .Cfor _ _ b => cmdCallOf f b
  | .Cwhile b _ a => (cmdCallOf f b).or (cmdCallOf f a)
  | _ => none

/-- The first call of `f` in a command. -/
def cmdCallOf (f : String) : List InstrR → Option (List LVal × List PExpr)
  | [] => none
  | i :: is => (instrCallOf f i).or (cmdCallOf f is)
end

/-- The surface type and storage class of a call operand or result of type `s`: an array
is passed as a `reg mut ptr`. -/
def callTy (s : SType) : Storage × PType :=
  match s with
  | .sarr _ => (.regPtr true, canonP s)
  | _ => (.reg, canonP s)

/-- The type of an expression that is a variable, `u64` otherwise. -/
def exprTy : PExpr → SType
  | .Pvar x => x.gv.var.vtype
  | _ => u64

/-- The type of an l-value that is a variable, `u64` otherwise. -/
def lvalTy : LVal → SType
  | .Lvar x => x.var.vtype
  | _ => u64

/-- The extern signature of `f` read off its first call in `c`. -/
def externOf (c : Cmd) (f : String) : ExternSig :=
  match cmdCallOf f c with
  | some (lvs, args) =>
      { name := f, params := args.map (callTy ∘ exprTy), results := lvs.map (callTy ∘ lvalTy) }
  | none => { name := f, params := [], results := [] }

/-- The declaration of a variable at its type. -/
def declOf (v : JVar) : Decl :=
  { storage := storOf v.vtype, ty := canonP v.vtype, names := [v.vname] }

/-- The function of a body: the parameters `ps`, the results `res` with their storage
classes and surface types `resTys`, and a declaration of every other variable of the
body and the results, at its type. -/
def mkFn (fname : String) (ps : List (JVar × Storage × PType)) (body : Cmd)
    (res : List JVar) (resTys : List (Storage × PType)) : JazzFn :=
  let pvs := ps.map Prod.fst
  let locals := ((cmdVars body ++ res).dedup).filter fun v => !pvs.contains v
  let fd : FunDecl := ⟨⟨fname⟩, ps.map (fun p => ⟨⟨p.1, vi0⟩⟩), body,
    res.map (fun v => ⟨v, vi0⟩)⟩
  { kind := .exportFn, fd := fd, paramTys := ps.map Prod.snd, resultTys := resTys,
    decls := locals.map declOf }

/-- The unit of a function body: the function and the extern signature of each callee. -/
def mkUnit (fn : JazzFn) : JazzUnit :=
  { externs := (cmdCalls fn.fd.body).dedup.map (externOf fn.fd.body), fns := [fn] }

/-- The function of a lowered program: the result is moved to the result parameter `pj`,
which the function returns as a `reg mut ptr` at the parameter's surface type, or to the
result variable `mkV 'r' D` at the type of the signature's result. -/
def finish {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t) (fname : String)
    (r : JOut) : JazzFn :=
  let ps := paramPairs sig
  let rv := r.res.headD dfltV
  match sig.resultParam with
  | some j =>
      let pj := (ps.map Prod.fst).getD j dfltV
      mkFn fname ps (r.code ++ if pj == rv then [] else [asgn pj (pv rv)]) [pj]
        [(.regPtr true, ((ps.map Prod.snd).getD j (.reg, .word .U64)).2)]
  | none =>
      let rr := mkV 'r' r.depth sig.result.2.toSType
      mkFn fname ps (r.code ++ [asgn rr (pv rv)]) [rr] [sig.result]

/-- The number of registers the spill pass `JasminSpill.spillUnit` allots to the register
variables of a lowered function: the sixteen x86-64 general-purpose registers less `rsp`
and the three registers the parameters of the lowered functions occupy. -/
def spillK : Nat := 12

/-- **The lowering of a structured program to a Jasmin compilation unit**: the function
`fname`, an `export fn`, over the parameters of `sig`, followed by the spill pass
`JasminSpill.spillUnit spillK`, which keeps at most `spillK` register variables live at each
instruction of a straight-line body. `none` when `sig` does not fit, when `linearArrB` or
`jasminWidthsB` refuses, or when the lowering of the body refuses. -/
def nfToJasmin {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t) (fname : String)
    (p : NFProg jasminDialect Γ [t]) : Option JazzUnit :=
  if sig.fitsB && linearArrB p && jasminWidthsB p then
    (nfToJasminBody ((paramPairs sig).map Prod.fst).reverse p Γ.length 0).map fun r =>
      JasminSpill.spillUnit spillK (mkUnit (finish sig fname r))
  else none

/-! ## 7. Erased units -/

mutual
/-- Every variable information of an expression is the default. -/
def exprErasedB : PExpr → Bool
  | .Pconst _ | .Pbool _ | .Parr_init _ => true
  | .Pvar x => x.gv.info == vi0
  | .Pget _ _ x i => x.gv.info == vi0 && exprErasedB i
  | .Psub _ _ _ x i => x.gv.info == vi0 && exprErasedB i
  | .Pload _ x o => x.info == vi0 && exprErasedB o
  | .Papp1 _ e => exprErasedB e
  | .Papp2 _ a b => exprErasedB a && exprErasedB b
  | .PappN _ es => exprsErasedB es
  | .Pif _ c a b => exprErasedB c && exprErasedB a && exprErasedB b

/-- Every variable information of a list of expressions is the default. -/
def exprsErasedB : List PExpr → Bool
  | [] => true
  | e :: es => exprErasedB e && exprsErasedB es
end

/-- An erased l-value: default variable information, and an `_` of the type `ty`. -/
def lvalErasedB (ty : SType) : LVal → Bool
  | .Lnone i ty' => i == vi0 && ty' == ty
  | .Lvar x => x.info == vi0
  | .Lmem _ x o => x.info == vi0 && exprErasedB o
  | .Laset _ _ x i => x.info == vi0 && exprErasedB i
  | .Lasub _ _ _ x i => x.info == vi0 && exprErasedB i

/-- Erased l-values from position `k`: position `i` erased at the type `tys[i]`, `u64`
past the end. -/
def lvalsErasedB (tys : List SType) : Nat → List LVal → Bool
  | _, [] => true
  | k, lv :: lvs => lvalErasedB ((tys[k]?).getD u64) lv && lvalsErasedB tys (k + 1) lvs

/-- The array initialiser `Parr_init`. -/
def isArrInit : PExpr → Bool
  | .Parr_init _ => true
  | _ => false

mutual
/-- An erased instruction: the tag `AT_none`, the call `DoNotInline`, default variable
information, the `_` of an asm operation at its output type, and no `Parr_init`
assignment. -/
def instrErasedB : InstrR → Bool
  | .Cassgn lv tag _ e =>
      tag == .AT_none && lvalErasedB u64 lv && exprErasedB e && !isArrInit e
  | .Copn lvs tag (.Oasm o) es =>
      tag == .AT_none && lvalsErasedB (opnNoneTys o.name lvs.length) 0 lvs && exprsErasedB es
  | .Cif c t e => exprErasedB c && cmdErasedB t && cmdErasedB e
  | .Cfor v _ b => v.info == vi0 && cmdErasedB b
  | .Cwhile b c a => cmdErasedB b && exprErasedB c && cmdErasedB a
  | .Ccall ii lvs _ args => ii == .DoNotInline && lvalsErasedB [] 0 lvs && exprsErasedB args

/-- Every instruction of a command is erased. -/
def cmdErasedB : List InstrR → Bool
  | [] => true
  | i :: is => instrErasedB i && cmdErasedB is
end

theorem cmdErasedB_iff (c : Cmd) : cmdErasedB c = true ↔ ∀ i ∈ c, instrErasedB i = true := by
  induction c with
  | nil => simp [cmdErasedB]
  | cons i is ih => simp [cmdErasedB, ih]

theorem exprsErasedB_iff (es : List PExpr) :
    exprsErasedB es = true ↔ ∀ e ∈ es, exprErasedB e = true := by
  induction es with
  | nil => simp [exprsErasedB]
  | cons e es ih => simp [exprsErasedB, ih]

@[simp] theorem outLvs_erased (tys : List SType) : ∀ (k : Nat) (outs : List (Option JVar)),
    lvalsErasedB tys k (outLvs tys k outs) = true
  | _, [] => rfl
  | k, none :: outs => by simp [outLvs, lvalsErasedB, lvalErasedB, vi0, outLvs_erased]
  | k, some v :: outs => by
      simp [outLvs, lvalsErasedB, lvalErasedB, lvv, vi0, outLvs_erased]

theorem lvalsErasedB_map_lvv (tys : List SType) :
    ∀ (k : Nat) (vs : List JVar), lvalsErasedB tys k (vs.map lvv) = true
  | _, [] => rfl
  | k, v :: vs => by simp [lvalsErasedB, lvalErasedB, lvv, vi0, lvalsErasedB_map_lvv]

@[simp] theorem outLvs_length (tys : List SType) : ∀ (k : Nat) (outs : List (Option JVar)),
    (outLvs tys k outs).length = outs.length
  | _, [] => rfl
  | k, none :: outs => by simp [outLvs, outLvs_length]
  | k, some v :: outs => by simp [outLvs, outLvs_length]

@[simp] theorem exprErasedB_pv (v : JVar) : exprErasedB (pv v) = true := by
  simp [pv, exprErasedB]

@[simp] theorem instrErasedB_asgn_pv (x v : JVar) : instrErasedB (asgn x (pv v)) = true := by
  simp [asgn, pv, lvv, instrErasedB, exprErasedB, lvalErasedB, isArrInit]

theorem parMovesJ_erased (D : Nat) (ps : List (JVar × JVar)) :
    ∀ i ∈ parMovesJ D ps, instrErasedB i = true := by
  intro i hi
  simp only [parMovesJ] at hi
  split at hi
  · simp only [List.mem_map] at hi
    obtain ⟨p, _, rfl⟩ := hi
    simp
  · simp only [List.mem_append, List.mem_map] at hi
    rcases hi with ⟨q, _, rfl⟩ | ⟨q, _, rfl⟩ <;> simp

theorem seqMoves_erased (ps : List (JVar × JVar)) :
    ∀ i ∈ seqMoves ps, instrErasedB i = true := by
  intro i hi
  simp only [seqMoves, List.mem_map] at hi
  obtain ⟨p, _, rfl⟩ := hi
  simp

theorem pre_erased {c : Cmd} {r : JOut} (hc : ∀ i ∈ c, instrErasedB i = true)
    (hr : ∀ i ∈ r.code, instrErasedB i = true) :
    ∀ i ∈ (JOut.pre c r).code, instrErasedB i = true := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hc i hi
  · exact hr i hi

theorem forCode_erased (env : List JVar) (d n : Nat) (cs : List JasminTy) (inits : List JVar)
    (ci : Nat) {b : JOut} (hb : ∀ i ∈ b.code, instrErasedB i = true) :
    ∀ i ∈ forCode env d n cs inits ci b, instrErasedB i = true := by
  intro i hi
  simp only [forCode, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with ((hi | rfl | rfl | rfl) | hi)
  · exact seqMoves_erased _ i hi
  · simp [asgn, cnst, lvv, instrErasedB, exprErasedB, lvalErasedB, isArrInit, vi0]
  · simp
  · simp only [instrErasedB, cmdErasedB_iff, Bool.and_eq_true]
    refine ⟨⟨by simp, by simp [nz, pv, cnst, exprErasedB, vi0]⟩, ?_⟩
    intro i hi
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (hi | hi) | rfl | rfl
    · exact hb i hi
    · exact parMovesJ_erased _ _ i hi
    all_goals simp [asgn, pv, cnst, lvv, instrErasedB, exprErasedB, lvalErasedB, isArrInit,
      vi0]
  · exact seqMoves_erased _ i hi

theorem ifCode_erased (env : List JVar) (d : Nat) (rs : List JasminTy) (ci : Nat)
    {bt be : JOut} (ht : ∀ i ∈ bt.code, instrErasedB i = true)
    (he : ∀ i ∈ be.code, instrErasedB i = true) :
    instrErasedB (ifCode env d rs ci bt be) = true := by
  simp only [ifCode, instrErasedB, cmdErasedB_iff, Bool.and_eq_true, List.mem_append]
  refine ⟨⟨by simp [nz, pv, cnst, exprErasedB, vi0], ?_⟩, ?_⟩
  · rintro i (hi | hi)
    · exact ht i hi
    · exact parMovesJ_erased _ _ i hi
  · rintro i (hi | hi)
    · exact he i hi
    · exact parMovesJ_erased _ _ i hi

theorem whileCode_erased (d : Nat) (cs : List JasminTy) (inits : List JVar) {b : JOut}
    (hb : ∀ i ∈ b.code, instrErasedB i = true) :
    ∀ i ∈ whileCode d cs inits b, instrErasedB i = true := by
  intro i hi
  simp only [whileCode, List.mem_append, List.mem_singleton] at hi
  rcases hi with hi | rfl
  · exact seqMoves_erased _ i hi
  · simp only [instrErasedB, cmdErasedB_iff, Bool.and_eq_true, List.mem_append,
      List.mem_cons]
    refine ⟨⟨?_, by simp [nz, pv, cnst, exprErasedB, vi0]⟩, by simp⟩
    rintro i (hi | rfl | hi)
    · exact hb i hi
    · simp
    · exact parMovesJ_erased _ _ i hi

theorem emitOp_erased {op : JasminOp} {d : Nat} {x : JVar} {as : List JVar} {c : Cmd}
    {y : JVar} (h : emitOp op d x as = some (c, y)) : ∀ i ∈ c, instrErasedB i = true := by
  cases op
  all_goals try (cases ‹JasminBinOp›)
  all_goals try (cases ‹JasminCmp›)
  all_goals simp [emitOp] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals try simp only [castCode, matCF, cmpCode, cinCode]
  all_goals repeat' split
  all_goals simp [asgn, copn, pv, cnst, lvv, instrErasedB, exprErasedB, exprsErasedB,
    lvalErasedB, isArrInit, cmdErasedB, vi0]

/-- The code of a lowered region is erased. -/
theorem body_erased : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (env : List JVar) (d n : Nat) (r : JOut),
    nfToJasminBody env p d n = some r → ∀ i ∈ r.code, instrErasedB i = true := by
  intro Γ ts p
  induction p with
  | ret vs =>
      intro env d n r h
      simp only [nfToJasminBody, Option.some.injEq] at h
      subst h; simp
  | var e k ih =>
      intro env d n r h
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨c, y⟩, hc, r', hr', rfl⟩ := h
      exact pre_erased (emitOp_erased hc) (ih _ _ _ _ hr')
  | forLoop count inits body k ihb ihk =>
      intro env d n r h
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, r', hr', rfl⟩ := h
      exact pre_erased (forCode_erased _ _ _ _ _ _ (ihb _ _ _ _ hb)) (ihk _ _ _ _ hr')
  | ifThenElse cond thn els k iht ihe ihk =>
      intro env d n r h
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, r', hr', rfl⟩ := h
      refine pre_erased ?_ (ihk _ _ _ _ hr')
      intro i hi
      simp only [List.mem_singleton] at hi
      subst hi
      exact ifCode_erased _ _ _ _ (iht _ _ _ _ ht) (ihe _ _ _ _ he)
  | whileLoop inits body k ihb ihk =>
      intro env d n r h
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, r', hr', rfl⟩ := h
      exact pre_erased (whileCode_erased _ _ _ (ihb _ _ _ _ hb)) (ihk _ _ _ _ hr')
  | call f args k ih =>
      intro env d n r h
      simp only [nfToJasminBody] at h
      split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨r', hr', rfl⟩ := h
        refine pre_erased ?_ (ih _ _ _ _ hr')
        intro i hi
        simp only [List.mem_singleton] at hi
        subst hi
        simp only [instrErasedB, Bool.and_eq_true, exprsErasedB_iff]
        exact ⟨⟨by simp, lvalsErasedB_map_lvv _ _ _⟩, by simp⟩
      · simp at h

/-! ### The checks and the erasure of the single printer -/

theorem eraseVarI_of {x : VarI} (h : (x.info == vi0) = true) : eraseVarI x = x := by
  obtain ⟨v, i⟩ := x
  simp only [beq_iff_eq] at h
  subst h
  rfl

theorem eraseGVar_of {x : GVar} (h : (x.gv.info == vi0) = true) : eraseGVar x = x := by
  obtain ⟨g, gs⟩ := x
  simp only [eraseGVar, eraseVarI_of h]

mutual
theorem eraseExpr_of : (e : PExpr) → exprErasedB e = true → eraseExpr e = e
  | .Pconst _, _ => rfl
  | .Pbool _, _ => rfl
  | .Parr_init _, _ => rfl
  | .Pvar x, h => by
      simp only [exprErasedB] at h
      simp only [eraseExpr, eraseGVar_of h]
  | .Pget aa ws x i, h => by
      simp only [exprErasedB, Bool.and_eq_true] at h
      simp only [eraseExpr, eraseGVar_of h.1, eraseExpr_of i h.2]
  | .Psub aa ws n x i, h => by
      simp only [exprErasedB, Bool.and_eq_true] at h
      simp only [eraseExpr, eraseGVar_of h.1, eraseExpr_of i h.2]
  | .Pload ws x o, h => by
      simp only [exprErasedB, Bool.and_eq_true] at h
      simp only [eraseExpr, eraseVarI_of h.1, eraseExpr_of o h.2]
  | .Papp1 op e, h => by
      simp only [exprErasedB] at h
      simp only [eraseExpr, eraseExpr_of e h]
  | .Papp2 op a b, h => by
      simp only [exprErasedB, Bool.and_eq_true] at h
      simp only [eraseExpr, eraseExpr_of a h.1, eraseExpr_of b h.2]
  | .PappN op es, h => by
      simp only [exprErasedB] at h
      simp only [eraseExpr, eraseExprs_of es h]
  | .Pif t c a b, h => by
      simp only [exprErasedB, Bool.and_eq_true] at h
      simp only [eraseExpr, eraseExpr_of c h.1.1, eraseExpr_of a h.1.2, eraseExpr_of b h.2]

theorem eraseExprs_of : (es : List PExpr) → exprsErasedB es = true → eraseExprs es = es
  | [], _ => rfl
  | e :: es, h => by
      simp only [exprsErasedB, Bool.and_eq_true] at h
      simp only [eraseExprs, eraseExpr_of e h.1, eraseExprs_of es h.2]
end

theorem eraseLval_of {lv : LVal} (h : lvalErasedB u64 lv = true) : eraseLval lv = lv := by
  cases lv with
  | Lnone i ty =>
      simp only [lvalErasedB, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | Lvar x => simp only [lvalErasedB] at h; simp only [eraseLval, eraseVarI_of h]
  | Lmem ws x o =>
      simp only [lvalErasedB, Bool.and_eq_true] at h
      simp only [eraseLval, eraseVarI_of h.1, eraseExpr_of o h.2]
  | Laset aa ws x i =>
      simp only [lvalErasedB, Bool.and_eq_true] at h
      simp only [eraseLval, eraseVarI_of h.1, eraseExpr_of i h.2]
  | Lasub aa ws n x i =>
      simp only [lvalErasedB, Bool.and_eq_true] at h
      simp only [eraseLval, eraseVarI_of h.1, eraseExpr_of i h.2]

theorem retypeGo_of (tys : List SType) : ∀ (k : Nat) (lvs : List LVal),
    lvalsErasedB tys k lvs = true → retypeGo tys k (lvs.map eraseLval) = lvs
  | _, [], _ => rfl
  | k, lv :: lvs, h => by
      simp only [lvalsErasedB, Bool.and_eq_true] at h
      have ih := retypeGo_of tys (k + 1) lvs h.2
      cases lv with
      | Lnone i ty =>
          simp only [lvalErasedB, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨rfl, rfl⟩, _⟩ := h
          simp only [List.map_cons, eraseLval, retypeGo, ih]
          rfl
      | Lvar x =>
          simp only [lvalErasedB] at h
          simp only [List.map_cons, eraseLval, eraseVarI_of h.1, retypeGo, ih]
      | Lmem ws x o =>
          simp only [lvalErasedB, Bool.and_eq_true] at h
          simp only [List.map_cons, eraseLval, eraseVarI_of h.1.1, eraseExpr_of o h.1.2,
            retypeGo, ih]
      | Laset aa ws x i =>
          simp only [lvalErasedB, Bool.and_eq_true] at h
          simp only [List.map_cons, eraseLval, eraseVarI_of h.1.1, eraseExpr_of i h.1.2,
            retypeGo, ih]
      | Lasub aa ws n x i =>
          simp only [lvalErasedB, Bool.and_eq_true] at h
          simp only [List.map_cons, eraseLval, eraseVarI_of h.1.1, eraseExpr_of i h.1.2,
            retypeGo, ih]

theorem map_eraseLval_of : ∀ (k : Nat) (lvs : List LVal),
    lvalsErasedB [] k lvs = true → lvs.map eraseLval = lvs
  | _, [], _ => rfl
  | k, lv :: lvs, h => by
      simp only [lvalsErasedB, Bool.and_eq_true] at h
      have h1 : lvalErasedB u64 lv = true := by simpa using h.1
      simp only [List.map_cons, eraseLval_of h1, map_eraseLval_of (k + 1) lvs h.2]

theorem isZeroInit_of {i : InstrR} (h : instrErasedB i = true) : isZeroInit i = false := by
  cases i with
  | Cassgn lv tag ty e =>
      cases e <;> cases lv <;> simp_all [isZeroInit, instrErasedB, isArrInit]
  | _ => rfl

mutual
theorem eraseInstr_of : (i : InstrR) → instrErasedB i = true → eraseInstr i = i
  | .Cassgn lv tag ty e, h => by
      simp only [instrErasedB, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨rfl, h1⟩, h2⟩, _⟩ := h
      simp only [eraseInstr, eraseLval_of h1, eraseExpr_of e h2]
  | .Copn lvs tag (.Oasm o) es, h => by
      simp only [instrErasedB, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, h1⟩, h2⟩ := h
      simp only [eraseInstr, retypeOpnLvs, opnName, List.length_map, retypeGo_of _ 0 lvs h1,
        eraseExprs_of es h2]
  | .Cif c t e, h => by
      simp only [instrErasedB, Bool.and_eq_true] at h
      simp only [eraseInstr, eraseExpr_of c h.1.1, cmdErase_of t h.1.2, cmdErase_of e h.2]
  | .Cfor v r b, h => by
      simp only [instrErasedB, Bool.and_eq_true] at h
      simp only [eraseInstr, eraseVarI_of h.1, cmdErase_of b h.2]
  | .Cwhile b c a, h => by
      simp only [instrErasedB, Bool.and_eq_true] at h
      simp only [eraseInstr, cmdErase_of b h.1.1, eraseExpr_of c h.1.2, cmdErase_of a h.2]
  | .Ccall ii lvs fn args, h => by
      simp only [instrErasedB, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, h1⟩, h2⟩ := h
      simp only [eraseInstr, map_eraseLval_of 0 lvs h1, eraseExprs_of args h2]

theorem cmdErase_of : (c : List InstrR) → cmdErasedB c = true →
    CatCrypt.Crypto.Jasmin.Jazz.Cmd.erase c = c
  | [], _ => rfl
  | i :: is, h => by
      simp only [cmdErasedB, Bool.and_eq_true] at h
      simp only [CatCrypt.Crypto.Jasmin.Jazz.Cmd.erase, isZeroInit_of h.1, Bool.false_eq_true,
        if_false, eraseInstr_of i h.1, cmdErase_of is h.2]
end

theorem mkUnit_erase {fname : String} {ps : List (JVar × Storage × PType)} {body : Cmd}
    {res : List JVar} {resTys : List (Storage × PType)} (hb : cmdErasedB body = true) :
    (mkUnit (mkFn fname ps body res resTys)).erase =
      { mkUnit (mkFn fname ps body res resTys) with externs := [] } := by
  simp only [CatCrypt.Crypto.Jasmin.Jazz.JazzUnit.erase, mkUnit, List.map_cons, List.map_nil,
    CatCrypt.Crypto.Jasmin.Jazz.JazzFn.erase, CatCrypt.Crypto.Jasmin.Jazz.FunDecl.erase, mkFn,
    List.map_map, Function.comp_def, cmdErase_of body hb]
  rfl

/-! ### Erasure of the spilled function -/

section SpillErase

open CatCrypt.Crypto.SecureCompilation.VIR.JasminSpill (Src St renG renE renEs renLv renI mv reloadSrc reloadFresh evict makeRoom
  helper helpers helpersOf loadOne loadAll dropDead afterDef stepI goBody fixOne fixAll initSt
  run spillFn lookS)

theorem renG_info (r : JVar → JVar) (g : GVar) : (renG r g).gv.info = g.gv.info := by
  unfold renG; split <;> rfl

mutual
theorem exprErasedB_renE (r : JVar → JVar) : ∀ e : PExpr, exprErasedB (renE r e) = exprErasedB e
  | .Pconst _ | .Pbool _ | .Parr_init _ => rfl
  | .Pvar g => by simp only [renE, exprErasedB, renG_info]
  | .Pget _ _ x i => by simp only [renE, exprErasedB, renG_info, exprErasedB_renE r i]
  | .Psub _ _ _ x i => by simp only [renE, exprErasedB, renG_info, exprErasedB_renE r i]
  | .Pload _ x o => by simp only [renE, exprErasedB, exprErasedB_renE r o]
  | .Papp1 _ e => by simp only [renE, exprErasedB, exprErasedB_renE r e]
  | .Papp2 _ a b => by simp only [renE, exprErasedB, exprErasedB_renE r a, exprErasedB_renE r b]
  | .PappN _ es => by simp only [renE, exprErasedB, exprsErasedB_renEs r es]
  | .Pif _ c a b => by
      simp only [renE, exprErasedB, exprErasedB_renE r c, exprErasedB_renE r a,
        exprErasedB_renE r b]

theorem exprsErasedB_renEs (r : JVar → JVar) :
    ∀ es : List PExpr, exprsErasedB (renEs r es) = exprsErasedB es
  | [] => rfl
  | e :: es => by simp only [renEs, exprsErasedB, exprErasedB_renE r e, exprsErasedB_renEs r es]
end

theorem isArrInit_renE (r : JVar → JVar) (e : PExpr) : isArrInit (renE r e) = isArrInit e := by
  cases e <;> rfl

theorem lvalErasedB_renLv (r : JVar → JVar) (ty : SType) (lv : LVal) :
    lvalErasedB ty (renLv r lv) = lvalErasedB ty lv := by
  cases lv <;> simp [renLv, lvalErasedB, exprErasedB_renE]

/-- Renaming the reads of an instruction keeps it erased. -/
theorem instrErasedB_renI (r : JVar → JVar) (i : InstrR) :
    instrErasedB (renI r i) = instrErasedB i := by
  cases i with
  | Cassgn lv tag ty e =>
      simp only [renI, instrErasedB, lvalErasedB_renLv, exprErasedB_renE, isArrInit_renE]
  | Copn lvs tag op es => cases op; simp only [renI, instrErasedB, exprsErasedB_renEs]
  | _ => rfl

theorem instrErasedB_mv (d s : JVar) : instrErasedB (mv d s) = true := by
  simp [mv, instrErasedB, lvalErasedB, exprErasedB, isArrInit, JasminSpill.vi, JasminSpill.lpv,
    vi0]

/-- A reload source whose right-hand side is erased and is not `Parr_init`. -/
def SrcErasedP : Src → Prop
  | .slot _ => True
  | .remat _ e => exprErasedB e = true ∧ isArrInit e = false

/-- The reload sources of a pass state are erased. -/
def SigErased (st : St) : Prop := ∀ p ∈ st.sig, SrcErasedP p.2

/-- The final state of a step of the pass has erased reload sources, and the instructions
the step emits are erased. -/
def OutErased (r : St × List InstrR) : Prop :=
  SigErased r.1 ∧ ∀ i ∈ r.2, instrErasedB i = true

theorem instrErasedB_reloadSrc (rho : List (JVar × JVar)) (d : JVar) {src : Src}
    (h : SrcErasedP src) : instrErasedB (reloadSrc rho d src) = true := by
  cases src with
  | slot s => exact instrErasedB_mv _ _
  | remat ty e =>
      obtain ⟨h1, h2⟩ := h
      simp [reloadSrc, instrErasedB, lvalErasedB, JasminSpill.vi, vi0, exprErasedB_renE,
        isArrInit_renE, h1, h2]

theorem srcErasedP_lookS {st : St} (h : SigErased st) {x : JVar} {src : Src}
    (hl : lookS st.sig x = some src) : SrcErasedP src := by
  unfold lookS at hl
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hl
  exact h p (List.mem_of_find?_eq_some hp)

theorem OutErased.app {r1 r2 : St × List InstrR} (h1 : OutErased r1) (h2 : OutErased r2) :
    OutErased (r2.1, r1.2 ++ r2.2) :=
  ⟨h2.1, fun i hi => (List.mem_append.mp hi).elim (h1.2 i) (h2.2 i)⟩

theorem evict_erased (res : List JVar) (c : List InstrR) {st : St} (p : JVar × JVar)
    (h : SigErased st) : OutErased (evict res c st p) := by
  unfold evict
  split
  · refine ⟨?_, ?_⟩
    · intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact trivial
      · exact h q hq
    · intro i hi
      simp only [List.mem_singleton] at hi
      subst hi
      exact instrErasedB_mv _ _
  · exact ⟨h, by simp⟩

theorem makeRoom_erased (k need : Nat) (prot res : List JVar) (c : List InstrR) :
    ∀ (fuel : Nat) {st : St}, SigErased st → OutErased (makeRoom k need prot res c fuel st)
  | 0, st, h => by
      simp only [makeRoom]; exact ⟨h, by simp⟩
  | fuel + 1, st, h => by
      simp only [makeRoom]
      split
      · exact ⟨h, by simp⟩
      · split
        · exact ⟨h, by simp⟩
        · next p _ =>
          exact (evict_erased res c p h).app
            (makeRoom_erased k need prot res c fuel (evict_erased res c p h).1)

theorem reloadFresh_erased {st : St} (x : JVar) {src : Src} (h : SigErased st)
    (hs : SrcErasedP src) : OutErased (reloadFresh st x src) := by
  unfold reloadFresh
  refine ⟨h, ?_⟩
  intro i hi
  simp only [List.mem_singleton] at hi
  subst hi
  exact instrErasedB_reloadSrc _ _ hs

theorem helper_erased (cand : JVar → Bool) {st : St} (y : JVar) (h : SigErased st) :
    OutErased (helper cand st y) := by
  unfold helper
  split
  · exact ⟨h, by simp⟩
  · split
    · next ty e hl =>
      split
      · exact reloadFresh_erased y h (srcErasedP_lookS h hl)
      · exact ⟨h, by simp⟩
    · exact ⟨h, by simp⟩

theorem helpers_erased (cand : JVar → Bool) :
    ∀ (ys : List JVar) {st : St}, SigErased st → OutErased (helpers cand st ys)
  | [], st, h => by simp only [helpers]; exact ⟨h, by simp⟩
  | y :: ys, st, h => by
      simp only [helpers]
      exact (helper_erased cand y h).app (helpers_erased cand ys (helper_erased cand y h).1)

theorem helpersOf_erased (cand : JVar → Bool) {st : St} (src : Src) (h : SigErased st) :
    OutErased (helpersOf cand st src) := by
  cases src with
  | remat ty e => exact helpers_erased cand _ h
  | slot s => simp only [helpersOf]; exact ⟨h, by simp⟩

theorem loadOne_erased (k : Nat) (cand : JVar → Bool) (prot res : List JVar) (c : List InstrR)
    {st : St} (x : JVar) (h : SigErased st) : OutErased (loadOne k cand prot res c st x) := by
  unfold loadOne
  split
  · exact ⟨h, by simp⟩
  · split
    · exact ⟨h, by simp⟩
    · next src hl =>
      have h1 := makeRoom_erased k (JasminSpill.needOf cand src) prot res c st.rho.length h
      have h2 := helpersOf_erased cand src h1.1
      have h3 := reloadFresh_erased x h2.1 (srcErasedP_lookS h hl)
      refine ⟨h3.1, ?_⟩
      intro i hi
      simp only [List.mem_append] at hi
      rcases hi with (hi | hi) | hi
      exacts [h1.2 i hi, h2.2 i hi, h3.2 i hi]

theorem loadAll_erased (k : Nat) (cand : JVar → Bool) (prot res : List JVar) (c : List InstrR) :
    ∀ (xs : List JVar) {st : St}, SigErased st → OutErased (loadAll k cand prot res c st xs)
  | [], st, h => by simp only [loadAll]; exact ⟨h, by simp⟩
  | x :: xs, st, h => by
      simp only [loadAll]
      exact (loadOne_erased k cand prot res c x h).app
        (loadAll_erased k cand prot res c xs (loadOne_erased k cand prot res c x h).1)

theorem afterDef_erased (cand : JVar → Bool) (c : List InstrR) {st : St} {i : InstrR}
    (h : SigErased st) (hi : instrErasedB i = true) : SigErased (afterDef cand c st i) := by
  intro q hq
  simp only [afterDef] at hq
  split at hq
  · split at hq
    · simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · simp only [instrErasedB, Bool.and_eq_true, Bool.not_eq_true'] at hi
        exact ⟨hi.1.2, hi.2⟩
      · exact h q (List.mem_of_mem_filter hq)
    · exact h q (List.mem_of_mem_filter hq)
  · exact h q (List.mem_of_mem_filter hq)

theorem stepI_erased (k : Nat) (cand : JVar → Bool) (res : List JVar) {st : St} {i : InstrR}
    (c : List InstrR) (h : SigErased st) (hi : instrErasedB i = true) :
    OutErased (stepI k cand res st i c) := by
  have h1 := loadAll_erased k cand (JasminSpill.usesOf cand i) res (i :: c)
    (JasminSpill.usesOf cand i) (st := dropDead res (i :: c) st) h
  have h2 := makeRoom_erased k (JasminSpill.defsOf cand i).length (JasminSpill.usesOf cand i) res
    (i :: c) (loadAll k cand (JasminSpill.usesOf cand i) res (i :: c) (dropDead res (i :: c) st)
      (JasminSpill.usesOf cand i)).1.rho.length h1.1
  refine ⟨afterDef_erased cand c h2.1 hi, ?_⟩
  intro j hj
  simp only [stepI, List.mem_append, List.mem_singleton] at hj
  rcases hj with (hj | hj) | rfl
  · exact h1.2 j hj
  · exact h2.2 j hj
  · rw [instrErasedB_renI]; exact hi

theorem goBody_erased (k : Nat) (cand : JVar → Bool) (res : List JVar) :
    ∀ (c : List InstrR) {st : St}, SigErased st → (∀ i ∈ c, instrErasedB i = true) →
      OutErased (goBody k cand res st c)
  | [], st, h, _ => by simp only [goBody]; exact ⟨h, by simp⟩
  | i :: c, st, h, hc => by
      simp only [goBody]
      have h1 := stepI_erased k cand res c h (hc i List.mem_cons_self)
      exact h1.app (goBody_erased k cand res c h1.1 fun j hj => hc j (List.mem_cons_of_mem _ hj))

theorem fixOne_erased (k : Nat) (cand : JVar → Bool) (res : List JVar) {st : St} (r : JVar)
    (h : SigErased st) : OutErased (fixOne k cand res st r) := by
  unfold fixOne
  split
  · split
    · exact ⟨h, by simp⟩
    · have h1 := makeRoom_erased k 1 res res [] st.rho.length h
      refine ⟨h1.1, ?_⟩
      intro i hi
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with hi | rfl
      · exact h1.2 i hi
      · exact instrErasedB_mv _ _
  · split
    · exact ⟨h, by simp⟩
    · next src hl =>
      have h1 := makeRoom_erased k (JasminSpill.needOf cand src) res res [] st.rho.length h
      have h2 := helpersOf_erased cand src h1.1
      refine ⟨h2.1, ?_⟩
      intro i hi
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with (hi | hi) | rfl
      · exact h1.2 i hi
      · exact h2.2 i hi
      · exact instrErasedB_reloadSrc _ _ (srcErasedP_lookS h hl)

theorem fixAll_erased (k : Nat) (cand : JVar → Bool) (res : List JVar) :
    ∀ (rs : List JVar) {st : St}, SigErased st → OutErased (fixAll k cand res st rs)
  | [], st, h => by simp only [fixAll]; exact ⟨h, by simp⟩
  | r :: rs, st, h => by
      simp only [fixAll]
      exact (fixOne_erased k cand res r h).app
        (fixAll_erased k cand res rs (fixOne_erased k cand res r h).1)

/-- The spill pass keeps the body of a function erased. -/
theorem cmdErasedB_spillFn (k : Nat) {fn : JazzFn} (hb : cmdErasedB fn.fd.body = true) :
    cmdErasedB (spillFn k fn).fd.body = true := by
  unfold spillFn
  split
  · rw [cmdErasedB_iff] at hb ⊢
    have h1 := goBody_erased k (JasminSpill.regWordB fn) (JasminSpill.resOf fn) fn.fd.body
      (st := initSt (JasminSpill.regWordB fn) (JasminSpill.resOf fn) fn.fd.body)
      (by intro q hq; simp [initSt] at hq) hb
    have h2 := fixAll_erased k (JasminSpill.regWordB fn) (JasminSpill.resOf fn)
      (((JasminSpill.resOf fn).filter (JasminSpill.regWordB fn)).dedup) h1.1
    intro i hi
    simp only [run, List.mem_append] at hi
    rcases hi with hi | hi
    · exact h1.2 i hi
    · exact h2.2 i hi
  · exact hb

/-- The spill pass keeps a function its own erasure when its body is erased. -/
theorem erase_spillFn (k : Nat) {fn : JazzFn} (he : fn.erase = fn)
    (hb : cmdErasedB fn.fd.body = true) : (spillFn k fn).erase = spillFn k fn := by
  have hb' := cmdErasedB_spillFn k hb
  have hp : (spillFn k fn).fd.params = fn.fd.params := by unfold spillFn; split <;> rfl
  have hr : (spillFn k fn).fd.results = fn.fd.results := by unfold spillFn; split <;> rfl
  have h1 := congrArg (fun f : JazzFn => f.fd.params) he
  have h2 := congrArg (fun f : JazzFn => f.fd.results) he
  simp only [CatCrypt.Crypto.Jasmin.Jazz.JazzFn.erase, CatCrypt.Crypto.Jasmin.Jazz.FunDecl.erase]
    at h1 h2 ⊢
  rw [cmdErase_of _ hb', hp, h1, hr, h2, ← hp, ← hr]

/-- The unit of a function after the spill pass is its own erasure except for its extern
signatures, when the unit before the pass is and the body of the function is erased. -/
theorem spillUnit_mkUnit_erase (k : Nat) {fn : JazzFn}
    (hu : (mkUnit fn).erase = { mkUnit fn with externs := [] })
    (hb : cmdErasedB fn.fd.body = true) :
    (JasminSpill.spillUnit k (mkUnit fn)).erase =
      { JasminSpill.spillUnit k (mkUnit fn) with externs := [] } := by
  have hF : fn.erase = fn := by
    have := congrArg JazzUnit.fns hu
    simpa [CatCrypt.Crypto.Jasmin.Jazz.JazzUnit.erase, mkUnit] using this
  simp only [CatCrypt.Crypto.Jasmin.Jazz.JazzUnit.erase, JasminSpill.spillUnit, mkUnit,
    List.map_cons, List.map_nil, erase_spillFn k hF hb]

end SpillErase

/-! ## 8. The variables of a lowered program -/

theorem mem_cmdVars {v : JVar} {c : Cmd} : v ∈ cmdVars c ↔ ∃ i ∈ c, v ∈ instrVars i := by
  induction c with
  | nil => simp [cmdVars]
  | cons i is ih => simp [cmdVars, ih]

theorem goodV_getD {env : List JVar} (h : ∀ v ∈ env, GoodV v) (i : Nat) :
    GoodV (env.getD i dfltV) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : env[i]? with
  | none => simp [dfltV]
  | some v => exact h v (List.mem_of_getElem? hi)

theorem goodV_headD {l : List JVar} (h : ∀ v ∈ l, GoodV v) : GoodV (l.headD dfltV) := by
  cases l with
  | nil => simp [dfltV]
  | cons v l => exact h v (by simp)

theorem goodV_resolveHV {env : List JVar} (h : ∀ v ∈ env, GoodV v) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (hv : HVector (fun t => Ctxt.Var Γ t) ts) :
    ∀ v ∈ resolveHV env hv, GoodV v := by
  intro v hv'
  simp only [resolveHV, List.mem_map] at hv'
  obtain ⟨i, _, rfl⟩ := hv'
  exact goodV_getD h i

theorem goodV_blockVars (base : Nat) (cs : List JasminTy) :
    ∀ v ∈ blockVars base cs, GoodV v := by
  intro v hv
  simp only [blockVars, List.mem_map] at hv
  obtain ⟨p, _, rfl⟩ := hv
  simp

/-- The variables of an instruction of a code are variables of the lowering. -/
def GoodC (c : Cmd) : Prop := ∀ i ∈ c, ∀ v ∈ instrVars i, GoodV v

theorem goodC_asgn_pv {x v : JVar} (hx : GoodV x) (hv : GoodV v) : GoodC [asgn x (pv v)] := by
  intro i hi w hw
  simp only [List.mem_singleton] at hi
  subst hi
  simp only [asgn, pv, lvv, instrVars, lvalVars, pexprVars, List.mem_append,
    List.mem_singleton] at hw
  rcases hw with rfl | rfl <;> assumption

theorem goodC_parMovesJ (D : Nat) {ps : List (JVar × JVar)}
    (h : ∀ p ∈ ps, GoodV p.1 ∧ GoodV p.2) : GoodC (parMovesJ D ps) := by
  intro i hi v hv
  simp only [parMovesJ] at hi
  split at hi
  · simp only [List.mem_map, List.mem_filter] at hi
    obtain ⟨p, ⟨hp, _⟩, rfl⟩ := hi
    exact goodC_asgn_pv (h p hp).1 (h p hp).2 _ (List.mem_singleton_self _) v hv
  · simp only [List.mem_append, List.mem_map] at hi
    rcases hi with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have hq' := (List.mem_filter.mp (List.fst_mem_of_mem_zipIdx hq)).1
      exact goodC_asgn_pv (by simp) (h _ hq').2 _ (List.mem_singleton_self _) v hv
    · have hq' := (List.mem_filter.mp (List.fst_mem_of_mem_zipIdx hq)).1
      exact goodC_asgn_pv (h _ hq').1 (by simp) _ (List.mem_singleton_self _) v hv

theorem goodV_zip {l l' : List JVar} (h : ∀ v ∈ l, GoodV v) (h' : ∀ v ∈ l', GoodV v) :
    ∀ p ∈ l.zip l', GoodV p.1 ∧ GoodV p.2 :=
  fun _ hp => ⟨h _ (List.of_mem_zip hp).1, h' _ (List.of_mem_zip hp).2⟩

theorem emitOp_good {op : JasminOp} {d : Nat} {x : JVar} {as : List JVar} {c : Cmd}
    {y : JVar} (h : emitOp op d x as = some (c, y)) (hx : GoodV x)
    (has : ∀ v ∈ as, GoodV v) : GoodC c ∧ GoodV y := by
  have hg : ∀ i, GoodV (as.getD i dfltV) := goodV_getD has
  have hg' : ∀ i, GoodV (as[i]?.getD dfltV) := fun i => by
    simpa [List.getD_eq_getElem?_getD] using hg i
  cases op
  all_goals try (cases ‹JasminBinOp›)
  all_goals try (cases ‹JasminCmp›)
  all_goals simp [emitOp] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals refine ⟨?_, by first | exact hx | exact hg _⟩
  all_goals simp only [GoodC, castCode, matCF, cmpCode, cinCode]
  all_goals repeat' split
  all_goals simp [asgn, copn, pv, cnst, lvv, outLvs, outsCW, outsW, tmp, instrVars,
    pexprVars, pexprsVars, lvalVars, lvalsVars, cmdVars, hx, hg']

theorem goodV_append {l l' : List JVar} (h : ∀ v ∈ l, GoodV v) (h' : ∀ v ∈ l', GoodV v) :
    ∀ v ∈ l ++ l', GoodV v := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact h v hv
  · exact h' v hv

theorem goodV_cons {v : JVar} {l : List JVar} (h : GoodV v) (h' : ∀ v ∈ l, GoodV v) :
    ∀ w ∈ v :: l, GoodV w := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact h
  · exact h' w hw

theorem pre_good {c : Cmd} {r : JOut} (hc : GoodC c) (hr : GoodC r.code) :
    GoodC (JOut.pre c r).code := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hc i hi
  · exact hr i hi

theorem seqMoves_good {ps : List (JVar × JVar)} (h : ∀ p ∈ ps, GoodV p.1 ∧ GoodV p.2) :
    GoodC (seqMoves ps) := by
  intro i hi
  simp only [seqMoves, List.mem_map] at hi
  obtain ⟨p, hp, rfl⟩ := hi
  exact goodC_asgn_pv (h p hp).1 (h p hp).2 _ (List.mem_singleton_self _)

theorem goodV_nz {v : JVar} (hv : GoodV v) : ∀ w ∈ pexprVars (nz v), GoodV w := by
  intro w hw
  simp [nz, pv, cnst, pexprVars] at hw
  subst hw
  exact hv

theorem forCode_good {env : List JVar} {d n : Nat} {cs : List JasminTy} {inits : List JVar}
    {ci : Nat} {b : JOut} (henv : ∀ v ∈ env, GoodV v) (hinit : ∀ v ∈ inits, GoodV v)
    (hb1 : GoodC b.code) (hb2 : ∀ v ∈ b.res, GoodV v) :
    GoodC (forCode env d n cs inits ci b) := by
  have hcar := goodV_blockVars (d + 1) cs
  intro i hi
  simp only [forCode, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with ((hi | rfl | rfl | rfl) | hi)
  · exact seqMoves_good (goodV_zip hcar hinit) i hi
  · exact fun v hv => by
      simp [asgn, cnst, lvv, instrVars, lvalVars, pexprVars] at hv
      subst hv; simp
  · exact goodC_asgn_pv (by simp) (goodV_getD henv _) _ (List.mem_singleton_self _)
  · intro v hv
    simp only [instrVars, mem_cmdVars, List.mem_append, List.not_mem_nil, List.mem_cons,
      or_false] at hv
    rcases hv with ((⟨_, h0, _⟩ | hv) | ⟨i, hi, hv⟩)
    · exact h0.elim
    · exact goodV_nz (by simp) v hv
    · rcases hi with (hi | hi) | rfl | rfl
      · exact hb1 i hi v hv
      · exact goodC_parMovesJ _ (goodV_zip hcar hb2) i hi v hv
      all_goals
        simp [asgn, pv, cnst, lvv, instrVars, lvalVars, pexprVars] at hv
        rcases hv with rfl | rfl
        all_goals simp
  · refine seqMoves_good (fun p hp => goodV_zip (goodV_blockVars d cs) hcar p ?_) i hi
    exact List.mem_reverse.mp hp

theorem ifCode_good {env : List JVar} {d : Nat} {rs : List JasminTy} {ci : Nat}
    {bt be : JOut} (henv : ∀ v ∈ env, GoodV v) (ht1 : GoodC bt.code)
    (ht2 : ∀ v ∈ bt.res, GoodV v) (he1 : GoodC be.code) (he2 : ∀ v ∈ be.res, GoodV v) :
    ∀ v ∈ instrVars (ifCode env d rs ci bt be), GoodV v := by
  have hblk := goodV_blockVars d rs
  intro v hv
  simp only [ifCode, instrVars, mem_cmdVars, List.mem_append] at hv
  rcases hv with (hv | ⟨i, hi, hv⟩) | ⟨i, hi, hv⟩
  · exact goodV_nz (goodV_getD henv _) v hv
  · rcases hi with hi | hi
    · exact ht1 i hi v hv
    · exact goodC_parMovesJ _ (goodV_zip hblk ht2) i hi v hv
  · rcases hi with hi | hi
    · exact he1 i hi v hv
    · exact goodC_parMovesJ _ (goodV_zip hblk he2) i hi v hv

theorem whileCode_good {d : Nat} {cs : List JasminTy} {inits : List JVar} {b : JOut}
    (hinit : ∀ v ∈ inits, GoodV v) (hb1 : GoodC b.code) (hb2 : ∀ v ∈ b.res, GoodV v) :
    GoodC (whileCode d cs inits b) := by
  have hcar := goodV_blockVars d cs
  have htail : ∀ v ∈ b.res.tail, GoodV v := fun v hv => hb2 v (List.mem_of_mem_tail hv)
  intro i hi
  simp only [whileCode, List.mem_append, List.mem_singleton] at hi
  rcases hi with hi | rfl
  · exact seqMoves_good (goodV_zip hcar hinit) i hi
  · intro v hv
    simp only [instrVars, mem_cmdVars, List.mem_append, List.mem_cons] at hv
    rcases hv with (⟨i, hi, hv⟩ | hv) | ⟨i, hi, hv⟩
    · rcases hi with hi | rfl | hi
      · exact hb1 i hi v hv
      · exact goodC_asgn_pv (by simp) (goodV_headD hb2) _ (List.mem_singleton_self _) v hv
      · exact goodC_parMovesJ _ (goodV_zip hcar htail) i hi v hv
    · exact goodV_nz (by simp) v hv
    · simp at hi

/-- The code and the returned variables of a lowered region are variables of the lowering,
when those of the environment are. -/
theorem body_good : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (env : List JVar) (d n : Nat) (r : JOut),
    (∀ v ∈ env, GoodV v) → nfToJasminBody env p d n = some r →
    GoodC r.code ∧ ∀ v ∈ r.res, GoodV v := by
  intro Γ ts p
  induction p with
  | ret vs =>
      intro env d n r henv h
      simp only [nfToJasminBody, Option.some.injEq] at h
      subst h
      exact ⟨by simp [GoodC], goodV_resolveHV henv vs⟩
  | var e k ih =>
      intro env d n r henv h
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨c, y⟩, hc, r', hr', rfl⟩ := h
      obtain ⟨hc1, hy⟩ := emitOp_good hc (by simp) (goodV_resolveHV henv e.args)
      obtain ⟨hk1, hk2⟩ := ih _ _ _ _ (by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hy
        · exact henv v hv) hr'
      refine ⟨?_, hk2⟩
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hc1 i hi
      · exact hk1 i hi
  | forLoop count inits body k ihb ihk =>
      intro env d n r henv h
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, r', hr', rfl⟩ := h
      obtain ⟨hb1, hb2⟩ := ihb _ _ _ _ (goodV_append (goodV_blockVars _ _)
        (goodV_cons (by simp) henv)) hb
      obtain ⟨hk1, hk2⟩ := ihk _ _ _ _ (goodV_append (goodV_blockVars _ _) henv) hr'
      exact ⟨pre_good (forCode_good henv (goodV_resolveHV henv inits) hb1 hb2) hk1, hk2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro env d n r henv h
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, r', hr', rfl⟩ := h
      obtain ⟨ht1, ht2⟩ := iht _ _ _ _ henv ht
      obtain ⟨he1, he2⟩ := ihe _ _ _ _ henv he
      obtain ⟨hk1, hk2⟩ := ihk _ _ _ _ (goodV_append (goodV_blockVars _ _) henv) hr'
      refine ⟨pre_good ?_ hk1, hk2⟩
      intro i hi
      simp only [List.mem_singleton] at hi
      subst hi
      exact ifCode_good henv ht1 ht2 he1 he2
  | whileLoop inits body k ihb ihk =>
      intro env d n r henv h
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, r', hr', rfl⟩ := h
      obtain ⟨hb1, hb2⟩ := ihb _ _ _ _ (goodV_append (goodV_blockVars _ _) henv) hb
      obtain ⟨hk1, hk2⟩ := ihk _ _ _ _ (goodV_append (goodV_blockVars _ _) henv) hr'
      exact ⟨pre_good (whileCode_good (goodV_resolveHV henv inits) hb1 hb2) hk1, hk2⟩
  | call f args k ih =>
      intro env d n r henv h
      simp only [nfToJasminBody] at h
      split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨r', hr', rfl⟩ := h
        obtain ⟨hk1, hk2⟩ := ih _ _ _ _ (goodV_append (goodV_blockVars _ _) henv) hr'
        refine ⟨pre_good ?_ hk1, hk2⟩
        intro i hi
        simp only [List.mem_singleton] at hi
        subst hi
        · intro v hv
          simp only [instrVars, lvalsVars, List.mem_append, List.mem_flatMap,
            List.mem_map] at hv
          rcases hv with ⟨lv, ⟨w, hw, rfl⟩, hv⟩ | hv
          · simp [lvv, lvalVars] at hv; subst hv; exact goodV_blockVars _ _ _ hw
          · have : ∀ es : List PExpr, (∀ e ∈ es, ∃ w, GoodV w ∧ e = pv w) →
                ∀ v ∈ pexprsVars es, GoodV v := by
              intro es
              induction es with
              | nil => simp [pexprsVars]
              | cons e es ihe =>
                  intro hes v hv
                  simp only [pexprsVars, List.mem_append] at hv
                  rcases hv with hv | hv
                  · obtain ⟨w, hw, rfl⟩ := hes e (by simp)
                    simp [pv, pexprVars] at hv; subst hv; exact hw
                  · exact ihe (fun e he => hes e (by simp [he])) v hv
            refine this _ ?_ v hv
            intro e he
            simp only [List.mem_map] at he
            obtain ⟨w, hw, rfl⟩ := he
            exact ⟨w, goodV_resolveHV henv args w hw, rfl⟩
      · simp at h

/-! ## 9. Well-formedness -/

theorem flatMap_declOf (l : List JVar) :
    (l.map declOf).flatMap (·.names) = l.map (·.vname) := by
  induction l with
  | nil => rfl
  | cons v l ih => simp [declOf, ih]

theorem mkFn_wellFormed (fname : String) (ps : List (JVar × Storage × PType)) (body : Cmd)
    (res : List JVar) (resTys : List (Storage × PType)) (callees : List String)
    (hps : ∀ p ∈ ps, p.2.2.toSType = p.1.vtype) (hpg : ∀ p ∈ ps, GoodV p.1)
    (hpn : (ps.map Prod.fst).Nodup) (hb : GoodC body) (hres : ∀ v ∈ res, GoodV v)
    (hlen : res.length = resTys.length)
    (hrt : ∀ q ∈ res.zip resTys, q.2.2.toSType = q.1.vtype)
    (hreg : ∀ q ∈ resTys, q.1.isReg = true) (hc : ∀ f ∈ cmdCalls body, f ∈ callees) :
    (mkFn fname ps body res resTys).WellFormed callees := by
  set pvs := ps.map Prod.fst with hpvs
  set locals := ((cmdVars body ++ res).dedup).filter fun v => !pvs.contains v with hloc
  have hused : ∀ v ∈ cmdVars body ++ res, GoodV v := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨i, hi, hv⟩ := mem_cmdVars.mp hv
      exact hb i hi v hv
    · exact hres v hv
  have hpvg : ∀ v ∈ pvs, GoodV v := by
    intro v hv
    simp only [hpvs, List.mem_map] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact hpg p hp
  have hlocg : ∀ v ∈ locals, GoodV v := fun v hv =>
    hused v (List.mem_dedup.mp (List.mem_filter.mp hv).1)
  refine ⟨by simp [mkFn], by simp [mkFn, hlen], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    simp only [mkFn, List.zip_map', List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact hps p hp
  · intro q hq
    simp only [mkFn, List.zip_map_left, List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact hrt p hp
  · have henv : (JazzFn.env (mkFn fname ps body res resTys)).map Prod.fst
        = (pvs ++ locals).map (·.vname) := by
      simp [JazzFn.env, mkFn, hpvs, hloc, List.map_flatMap, Function.comp_def,
        flatMap_declOf]
    rw [henv]
    refine List.Nodup.map_on (fun v hv w hw h => goodV_inj ?_ ?_ h) ?_
    · rcases List.mem_append.mp hv with hv | hv
      · exact hpvg v hv
      · exact hlocg v hv
    · rcases List.mem_append.mp hw with hw | hw
      · exact hpvg w hw
      · exact hlocg w hw
    · refine List.nodup_append.mpr ⟨hpn, (List.nodup_dedup _).filter _, ?_⟩
      intro a ha b hb hab
      subst hab
      have := (List.mem_filter.mp hb).2
      simp [ha] at this
  · intro v hv
    have hv' : v ∈ cmdVars body ++ res := by
      simp only [JazzFn.usedVars, mkFn, List.map_map, List.mem_append, List.mem_map,
        Function.comp_def] at hv
      rcases hv with hv | ⟨w, hw, rfl⟩
      · exact List.mem_append_left _ hv
      · exact List.mem_append_right _ hw
    by_cases hp : v ∈ pvs
    · simp only [hpvs, List.mem_map] at hp
      obtain ⟨p, hp, rfl⟩ := hp
      simp only [JazzFn.env, mkFn, List.mem_append, List.mem_map]
      exact Or.inl ⟨⟨⟨p.1, vi0⟩⟩, ⟨p, hp, rfl⟩, rfl⟩
    · simp only [JazzFn.env, mkFn, List.mem_append, List.mem_flatMap, List.mem_map]
      refine Or.inr ⟨_, ⟨v, ?_, rfl⟩, v.vname, List.mem_singleton_self _, ?_⟩
      · exact List.mem_filter.mpr ⟨List.mem_dedup.mpr hv', by simpa [hpvs] using hp⟩
      · simp [declOf, canonP_toSType]
  · intro _ q hq
    exact hreg q hq
  · intro f hf
    exact hc f hf

theorem mkUnit_wellFormed {fn : JazzFn} (h : fn.WellFormed (mkUnit fn).callees) :
    (mkUnit fn).WellFormed := by
  intro f hf
  simp only [mkUnit, List.mem_singleton] at hf
  subst hf
  exact h

theorem cmdCalls_sub_callees (fn : JazzFn) :
    ∀ f ∈ cmdCalls fn.fd.body, f ∈ (mkUnit fn).callees := by
  intro f hf
  simp only [JazzUnit.callees, mkUnit, List.mem_append, List.map_map, List.mem_map]
  refine Or.inr ⟨f, List.mem_dedup.mpr hf, ?_⟩
  simp only [Function.comp_def, externOf]
  split <;> rfl

theorem paramPairs_spec {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t) :
    (∀ p ∈ paramPairs sig, p.2.2.toSType = p.1.vtype) ∧
    (∀ p ∈ paramPairs sig, GoodV p.1) ∧ ((paramPairs sig).map Prod.fst).Nodup := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp only [paramPairs, List.mem_map] at hp
    obtain ⟨j, _, rfl⟩ := hp
    rfl
  · intro p hp
    simp only [paramPairs, List.mem_map] at hp
    obtain ⟨j, _, rfl⟩ := hp
    simp
  · simp only [paramPairs, List.map_map]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro j _ j' _ h
    exact (nameOf_inj (congrArg (fun v : JVar => v.vname) h)).2.1

/-- The surface type of the parameter at position `j` of a signature is the type of its
variable, the defaults `(.reg, .word .U64)` and `dfltV` past the end. -/
theorem paramPairs_getD_ty {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t)
    (j : Nat) :
    (((paramPairs sig).map Prod.snd).getD j (.reg, .word .U64)).2.toSType =
      (((paramPairs sig).map Prod.fst).getD j dfltV).vtype := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_map]
  cases h : (paramPairs sig)[j]? with
  | none => rfl
  | some p => exact (paramPairs_spec sig).1 p (List.mem_of_getElem? h)

/-! ## 10. Main results -/

theorem emitOp_isSome {op : JasminOp} (h : OpPlain op) (d : Nat)
    (x : JVar) (as : List JVar) : (emitOp op d x as).isSome := by
  cases op
  all_goals try (cases ‹JasminBinOp›)
  all_goals simp_all [OpPlain, emitOp]

/-- The lowering of a region succeeds on every program of `RegionExportable`. -/
theorem body_isSome : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts), RegionExportable p →
    ∀ (env : List JVar) (d n : Nat), (nfToJasminBody env p d n).isSome := by
  intro Γ ts p
  induction p with
  | ret vs => intro _ env d n; simp [nfToJasminBody]
  | @var Γ t ts e k ih =>
      intro hp env d n
      obtain ⟨he, hk⟩ := hp
      obtain ⟨cx, hcx⟩ := Option.isSome_iff_exists.mp
        (emitOp_isSome he.opPlain d (mkV 'r' d (styOf t)) (resolveHV env e.args))
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (ih hk (cx.2 :: env) (d + 1) n)
      simp [nfToJasminBody, hcx, hr]
  | @forLoop Γ cs ts count inits body k ihb ihk =>
      intro hp env d n
      obtain ⟨hb, hk⟩ := hp
      obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp
        (ihb hb (blockVars (d + 1) cs ++ mkV 'r' d u64 :: env) (d + 1 + cs.length) (n + 1))
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
        (ihk hk (blockVars d cs ++ env) (d + cs.length) b.next)
      simp [nfToJasminBody, hb', hr]
  | @ifThenElse Γ rs ts cond thn els k iht ihe ihk =>
      intro hp env d n
      obtain ⟨ht, he, hk⟩ := hp
      obtain ⟨t, ht'⟩ := Option.isSome_iff_exists.mp (iht ht env d n)
      obtain ⟨e, he'⟩ := Option.isSome_iff_exists.mp (ihe he env d t.next)
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
        (ihk hk (blockVars d rs ++ env) (d + rs.length) e.next)
      simp [nfToJasminBody, ht', he', hr]
  | @whileLoop Γ cs ts inits body k ihb ihk =>
      intro hp env d n
      obtain ⟨_, hb, hk⟩ := hp
      obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp
        (ihb hb (blockVars d cs ++ env) (d + cs.length) n)
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
        (ihk hk (blockVars d cs ++ env) (d + cs.length) b.next)
      simp [nfToJasminBody, hb', hr]
  | @call Γ as rs ts f args k ih =>
      intro hp env d n
      obtain ⟨hw, hk⟩ := hp
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
        (ih hk (blockVars d rs ++ env) (d + rs.length) n)
      simp [nfToJasminBody, hw, hr]

/-- **Completeness of the lowering**: `nfToJasmin` succeeds on every program of
`RegionExportable` that `linearArrB` and `jasminWidthsB` accept, for a signature that fits
its context. No operation of the fragment is refused; an arithmetic shift by `n` is emitted
with the count `sarCount w n` (`sshiftRight_sarCount`). -/
theorem nfToJasmin_isSome {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t)
    (fname : String) {p : NFProg jasminDialect Γ [t]} (hp : RegionExportable p)
    (hlin : linearArrB p = true) (hw : jasminWidthsB p = true) (hsig : sig.Fits) :
    (nfToJasmin sig fname p).isSome := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
    (body_isSome p hp ((paramPairs sig).map Prod.fst).reverse Γ.length 0)
  simp [nfToJasmin, (sig.fitsB_iff).mpr hsig, hlin, hw, hr]

theorem nfToJasmin_eq_some {Γ : Ctxt jasminDialect} {t : JasminTy} {sig : JazzSig Γ t}
    {fname : String} {p : NFProg jasminDialect Γ [t]} {u : JazzUnit}
    (h : nfToJasmin sig fname p = some u) :
    sig.fitsB = true ∧ ∃ r, nfToJasminBody ((paramPairs sig).map Prod.fst).reverse p
      Γ.length 0 = some r ∧ u = JasminSpill.spillUnit spillK (mkUnit (finish sig fname r)) := by
  unfold nfToJasmin at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact ⟨hc.1.1, r, hr, rfl⟩
  · simp at h

/-- Every program `nfToJasmin` lowers passes `jasminWidthsB`. -/
theorem jasminWidthsB_of_nfToJasmin {Γ : Ctxt jasminDialect} {t : JasminTy}
    {sig : JazzSig Γ t} {fname : String} {p : NFProg jasminDialect Γ [t]} {u : JazzUnit}
    (h : nfToJasmin sig fname p = some u) : jasminWidthsB p = true := by
  unfold nfToJasmin at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact hc.2
  · simp at h

/-- The body of the function of a lowered program is erased, and the unit of that function,
before the spill pass, is its own erasure except for its extern signatures. -/
theorem mkUnit_finish_erase {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t)
    (fname : String) {p : NFProg jasminDialect Γ [t]} {r : JOut}
    (hr : nfToJasminBody ((paramPairs sig).map Prod.fst).reverse p Γ.length 0 = some r) :
    cmdErasedB (finish sig fname r).fd.body = true ∧
      (mkUnit (finish sig fname r)).erase = { mkUnit (finish sig fname r) with externs := [] } := by
  have hb := body_erased p _ _ _ r hr
  cases hrp : sig.resultParam with
  | some j =>
      simp only [finish, hrp]
      have hc : cmdErasedB (r.code ++ if ((paramPairs sig).map Prod.fst).getD j dfltV ==
          r.res.headD dfltV then [] else [asgn (((paramPairs sig).map Prod.fst).getD j dfltV)
            (pv (r.res.headD dfltV))]) = true := by
        simp only [cmdErasedB_iff, List.mem_append]
        rintro i (hi | hi)
        · exact hb i hi
        · split at hi
          · simp at hi
          · simp only [List.mem_singleton] at hi; subst hi; simp
      exact ⟨hc, mkUnit_erase hc⟩
  | none =>
      simp only [finish, hrp]
      have hc : cmdErasedB (r.code ++ [asgn (mkV 'r' r.depth sig.result.2.toSType)
          (pv (r.res.headD dfltV))]) = true := by
        simp only [cmdErasedB_iff, List.mem_append, List.mem_singleton]
        rintro i (hi | rfl)
        · exact hb i hi
        · simp
      exact ⟨hc, mkUnit_erase hc⟩

/-- **The units of the lowering are erased**: the erasure `JazzUnit.erase` of the single
Jasmin printer leaves every unit `nfToJasmin` returns unchanged except for its extern
signatures, which the erasure drops. -/
theorem nfToJasmin_erase {Γ : Ctxt jasminDialect} {t : JasminTy} {sig : JazzSig Γ t}
    {fname : String} {p : NFProg jasminDialect Γ [t]} {u : JazzUnit}
    (h : nfToJasmin sig fname p = some u) : u.erase = { u with externs := [] } := by
  obtain ⟨_, r, hr, rfl⟩ := nfToJasmin_eq_some h
  obtain ⟨hb, hu⟩ := mkUnit_finish_erase sig fname hr
  exact spillUnit_mkUnit_erase spillK hu hb

/-- The function of a lowered program, before the spill pass, is well formed. -/
theorem mkUnit_finish_wellFormed {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t)
    (fname : String) {p : NFProg jasminDialect Γ [t]} {r : JOut} (hfit : sig.fitsB = true)
    (hr : nfToJasminBody ((paramPairs sig).map Prod.fst).reverse p Γ.length 0 = some r) :
    (mkUnit (finish sig fname r)).WellFormed := by
  obtain ⟨hps, hpg, hpn⟩ := paramPairs_spec sig
  have henv : ∀ v ∈ ((paramPairs sig).map Prod.fst).reverse, GoodV v := by
    intro v hv
    simp only [List.mem_reverse, List.mem_map] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact hpg p hp
  obtain ⟨hb, hres⟩ := body_good p _ _ _ r henv hr
  have hrv : GoodV (r.res.headD dfltV) := goodV_headD hres
  refine mkUnit_wellFormed ?_
  have hcal := cmdCalls_sub_callees (finish sig fname r)
  have hpj : ∀ j, GoodV (((paramPairs sig).map Prod.fst).getD j dfltV) := by
    intro j
    refine goodV_getD ?_ j
    intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact hpg p hp
  cases hrp : sig.resultParam with
  | some j =>
      simp only [finish, hrp] at hcal ⊢
      refine mkFn_wellFormed _ _ _ _ _ _ hps hpg hpn ?_ (by simpa using hpj j) rfl
        (by simpa using paramPairs_getD_ty sig j) (by simp [Storage.isReg]) hcal
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hb i hi
      · split at hi
        · simp at hi
        · exact goodC_asgn_pv (hpj _) hrv i hi
  | none =>
      simp only [finish, hrp] at hcal ⊢
      have hreg : sig.result.1.isReg = true := by
        simp only [JazzSig.fitsB, hrp, Bool.and_eq_true] at hfit
        exact hfit.2.1
      refine mkFn_wellFormed _ _ _ _ _ _ hps hpg hpn ?_ (by simp) rfl (by simp [mkV])
        (by simp [hreg]) hcal
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hb i hi
      · exact goodC_asgn_pv (by simp) hrv i hi

end CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
