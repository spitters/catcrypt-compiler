/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.TileBridge

/-!
# Vector memory operations of the x86 target as value operations on arrays

`vecMem` is a dialect over the type alphabet `JasminTy` with three operations between stack
arrays, registers of a lane width `w` and 512-bit registers:

* `vload w N` takes an array `stackArr w N` and an index of type `reg 64` and returns the
  512-bit register whose lane `j` of width `w` is the element of the array at the index plus
  `j`, read by `stackGet` (position modulo `N`);
* `vstore w N` takes an array, an index and a 512-bit register and returns the array after
  the `512 / w` lanes of the register are written by `stackSet` at the index plus `j`, lane
  `0` first;
* `vsplat w` takes a register `reg w` and returns the 512-bit register with its value in
  every lane of width `w`.

`jasminVecMem` is the operation sum `Dialect.opSum jasminVec vecMem`. Its leakage model
`jasminVecMemLeak M` gives an operation of `jasminVec` the class of `jasminVecLeak M`; a
`vload` and a `vstore` have the class `addrAt 1` and emit one address event, the reading of
the index; `vsplat` is quiet.

## Main definitions

* `vecLoad`, `vecStore` — the register read from an array at a position, and the array after
  the lanes of a register are written at a position.
* `VecMemOp`, `vecMem`, `vecMemKind` — the operations, the dialect and the event classes.
* `jasminVecMem`, `jasminVecMemDenote`, `jasminVecMemLeak` — the operation sum with
  `jasminVec`, its denotation on programs and its leakage model.
* `vloadE`, `vstoreE`, `vsplatE` — the expressions of `jasminVecMem` of the three operations.
* `memCom` — a block of `jasminVec` as a block of `jasminVecMem`.

## Main results

* `lane_vecLoad`: lane `k` of a load at `i` is `stackGet` at `i + k`.
* `vecLoad_lanes`: the lanes of a load are the tile `tileLoad` returns.
* `vecStore_eq_laneStore`: a store of a register whose lanes are those of a tile is the array
  `tileStore` returns.
* `lane_vsplat`: every lane of a broadcast is the register.
* `vloadE_denote`, `vstoreE_denote`, `vsplatE_denote`: the values of the three expressions.
* `jasminVecMem_opLeak_vload`, `jasminVecMem_opLeak_vstore`, `jasminVecMem_opLeak_vsplat`:
  one address event carrying the index per load and per store, none for a broadcast.
* `jasminVecMem_opLeak_inl`, `jasminVecMem_opLeak_scalar`, `jasminVecMem_opLeak_vec`: an
  operation of `jasminVec` emits the events it emits in `jasminVec`.
* `jasminVecMem_nfCTRel_of_levelCheck'`: a program the level checker accepts is constant time
  relative to its runs.
* `memCom_denote`, `memCom_ctLeak`: an included block has the value and the events of the
  block.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.X86VecMem

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (lane ofLanes lane_ofLanes bcast)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TileBridge
open CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum
  (castVar castArgs lookup_castVar lookupArgs_castArgs)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)
open Ctxt (Var Valuation)

/-! ## 1. The values of a vector load, store and broadcast -/

/-- The 512-bit register read from the array `a` at the position `i`: lane `j` of width `w`
    is the element at `i + j`, read modulo the length of the array. -/
def vecLoad (w : Nat) {N : Nat} (a : Fin N → BitVec w) (i : Nat) : BitVec 512 :=
  ofLanes w (fun j => stackGet a (i + j))

/-- The array `a` after the `512 / w` lanes of width `w` of the register `v` are written at
    the positions `i, i + 1, …`, lane `0` first. -/
def vecStore (w : Nat) {N : Nat} (a : Fin N → BitVec w) (i : Nat) (v : BitVec 512) :
    Fin N → BitVec w :=
  (List.finRange (512 / w)).foldl (fun acc j => stackSet acc (i + j.val) (lane w v j.val)) a

/-- **Lane `k` of a load at `i`** is the element at `i + k`. -/
theorem lane_vecLoad {w N k : Nat} (a : Fin N → BitVec w) (i : Nat) (hw : 0 < w)
    (hk : w * k + w ≤ 512) : lane w (vecLoad w a i) k = stackGet a (i + k) :=
  lane_ofLanes _ hw hk

/-- **The lanes of a load are the tile `tileLoad` returns**, for `n` lanes that fit the
    register. -/
theorem vecLoad_lanes {w N n : Nat} (a : Fin N → BitVec w) (i : Nat) (hw : 0 < w)
    (hn : ∀ k : Fin n, w * k.val + w ≤ 512) :
    (fun k : Fin n => lane w (vecLoad w a i) k.val) = jasminLaneLoad n a i :=
  funext fun k => lane_vecLoad a i hw (hn k)

/-- **A store of a register whose lanes are those of a tile** is the array `tileStore`
    returns. -/
theorem vecStore_eq_laneStore {w N : Nat} (a : Fin N → BitVec w) (i : Nat) (v : BitVec 512)
    (t : Fin (512 / w) → BitVec w) (ht : ∀ j : Fin (512 / w), lane w v j.val = t j) :
    vecStore w a i v = jasminLaneStore a i t := by
  rw [jasmin_laneStore_eq]
  exact congrArg (fun f => (List.finRange (512 / w)).foldl f a)
    (funext fun acc => funext fun j => by rw [ht j])

/-- **Every lane of a broadcast** is the register. -/
theorem lane_vsplat {w k : Nat} (x : BitVec w) (hw : 0 < w) (hk : w * k + w ≤ 512) :
    lane w (bcast w x) k = x :=
  lane_ofLanes _ hw hk

/-! ## 2. The operations -/

/-- The vector memory operations and the broadcast of a register, at a lane width `w`. -/
inductive VecMemOp where
  /-- The load of `512 / w` consecutive `w`-bit elements of an array of `N` elements
      (`vmovdqu64 (base, idx, w / 8), dst`). -/
  | vload (w N : Nat)
  /-- The store of the `512 / w` lanes of a register to consecutive positions of an array of
      `N` elements (`vmovdqu64 src, (base, idx, w / 8)`). -/
  | vstore (w N : Nat)
  /-- The broadcast of a `w`-bit register to every lane (`vpbroadcastq` / `vpbroadcastd` of a
      general register). -/
  | vsplat (w : Nat)
  deriving DecidableEq

/-- The dialect of the vector memory operations over the type alphabet `JasminTy`. -/
@[reducible] def vecMem : Dialect := { Op := VecMemOp, Ty := JasminTy }

/-- The signatures: `vload` takes an array and an index and returns a 512-bit register;
    `vstore` takes an array, an index and a 512-bit register and returns the array; `vsplat`
    takes a register of the lane width and returns a 512-bit register. -/
instance instDialectSignatureVecMem : DialectSignature vecMem where
  sig
    | .vload w N => [.stackArr w N, .reg 64]
    | .vstore w N => [.stackArr w N, .reg 64, .reg 512]
    | .vsplat w => [.reg w]
  ret
    | .vload _ _ => .reg 512
    | .vstore w N => .stackArr w N
    | .vsplat _ => .reg 512

/-- The values: `vecLoad` and `vecStore` at the position the index denotes, and `bcast`. -/
instance instDialectDenoteVecMem : DialectDenote vecMem where
  denote
    | .vload w N => fun args =>
        let a : Fin N → BitVec w := args.head
        let i : BitVec 64 := args.tail.head
        (vecLoad w a i.toNat : BitVec 512)
    | .vstore w N => fun args =>
        let a : Fin N → BitVec w := args.head
        let i : BitVec 64 := args.tail.head
        let v : BitVec 512 := args.tail.tail.head
        (vecStore w a i.toNat v : Fin N → BitVec w)
    | .vsplat w => fun args =>
        let x : BitVec w := args.head
        (bcast w x : BitVec 512)

/-- The event class of an operation: `vload` and `vstore` address memory at their index,
    argument `1`; `vsplat` is quiet. -/
def vecMemKind : VecMemOp → LeakKind
  | .vload .. => .addrAt 1
  | .vstore .. => .addrAt 1
  | .vsplat .. => .quiet

/-! ## 3. The operation sum with `jasminVec` -/

/-- The operation sum of `jasminVec` and `vecMem` over `JasminTy`. -/
abbrev jasminVecMem : Dialect.{0, 0} := Dialect.opSum jasminVec vecMem

/-- The signature of `jasminVecMem`: the signature of the summand. -/
instance instDialectSignatureJasminVecMem : DialectSignature jasminVecMem :=
  DialectOpSum.instDialectSignatureOpSum (O₁ := jasminVec.Op) (O₂ := VecMemOp) (T := JasminTy)

/-- The value of an operation of `jasminVecMem`: the value in its summand. -/
instance instDialectDenoteJasminVecMem : DialectDenote jasminVecMem :=
  DialectOpSum.instDialectDenoteOpSum (O₁ := jasminVec.Op) (O₂ := VecMemOp) (T := JasminTy)

/-- The trip counter of `jasminVecMem` is the 64-bit register. -/
instance instHasWord64JasminVecMem : HasWord64 jasminVecMem where
  word := HasWord64.word (d := jasminDialect)
  toNat := HasWord64.toNat (d := jasminDialect)
  ofNat := HasWord64.ofNat (d := jasminDialect)

/-- The bit of `jasminVecMem` is the 1-bit register. -/
instance instHasBoolBitJasminVecMem : HasBoolBit jasminVecMem where
  bit := HasBitType.bit (d := jasminDialect)
  toBool := HasBoolBit.toBool (d := jasminDialect)

/-- `jasminVecMem` denotes calls in the empty environment. -/
instance instCallDenoteJasminVecMem : CallDenote jasminVecMem := ⟨.empty⟩

/-- The denotation of `jasminVecMem` on programs: every summand is total. The instance has
    high priority, so that programs of `jasminVecMem` denote by the pure denotation of the
    operation sum. -/
@[instance_reducible] instance (priority := high) jasminVecMemDenote :
    DialectDenoteM jasminVecMem Option :=
  instDialectDenoteMOptionOfPure jasminVecMem

/-- An operation of `jasminVec` has in `jasminVecMem` its value in `jasminVec`. -/
@[simp] theorem jasminVecMem_denote_inl (o : jasminVec.Op)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasminVec) o)) :
    DialectDenote.denote (d := jasminVecMem) (.inl o) args =
      DialectDenote.denote (d := jasminVec) o args := rfl

/-- A vector memory operation has in `jasminVecMem` its value in `vecMem`. -/
@[simp] theorem jasminVecMem_denote_inr (o : VecMemOp)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := vecMem) o)) :
    DialectDenote.denote (d := jasminVecMem) (.inr o) args =
      DialectDenote.denote (d := vecMem) o args := rfl

/-! ## 4. The leakage model -/

/-- The leakage model of `jasminVecMem` over a model `M` of `jasminDialect`: an operation of
    `jasminVec` has its class in `jasminVecLeak M`, a vector memory operation the class
    `vecMemKind` gives it, and a value has the reading of `M`. -/
def jasminVecMemLeak (M : LeakModel jasminDialect) : LeakModel jasminVecMem where
  kind := Sum.elim (jasminVecLeak M).kind vecMemKind
  valNat := M.valNat

/-- An operation of `jasminVec` has the class `jasminVecLeak M` gives it. -/
@[simp] theorem jasminVecMemLeak_kind_inl (M : LeakModel jasminDialect) (op : jasminVec.Op) :
    (jasminVecMemLeak M).kind (.inl op) = (jasminVecLeak M).kind op := rfl

/-- A vector memory operation has the class `vecMemKind` gives it. -/
@[simp] theorem jasminVecMemLeak_kind_inr (M : LeakModel jasminDialect) (op : VecMemOp) :
    (jasminVecMemLeak M).kind (.inr op) = vecMemKind op := rfl

/-- The readings of a list of values are those of `jasminVecLeak M`. -/
theorem jasminVecMem_valsNat (M : LeakModel jasminDialect) :
    ∀ {ts : List JasminTy} (vals : HVector (fun t => ⟦t⟧) ts),
      valsNat (jasminVecMemLeak M) vals = valsNat (jasminVecLeak M) vals
  | [], .nil => rfl
  | _ :: _, .cons x xs => by
      show M.valNat _ x :: valsNat (jasminVecMemLeak M) xs =
        M.valNat _ x :: valsNat (jasminVecLeak M) xs
      rw [jasminVecMem_valsNat M xs]

/-- **An operation of `jasminVec` emits in `jasminVecMem` the events it emits in
    `jasminVec`.** -/
theorem jasminVecMem_opLeak_inl (M : LeakModel jasminDialect) (op : jasminVec.Op)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasminVec) op)) :
    opLeak (jasminVecMemLeak M) (.inl op) vals = opLeak (jasminVecLeak M) op vals := by
  unfold opLeak
  rw [jasminVecMemLeak_kind_inl, jasminVecMem_valsNat M vals]

/-- A scalar operation emits in `jasminVecMem` the events it emits in `jasminDialect`. -/
theorem jasminVecMem_opLeak_scalar (M : LeakModel jasminDialect) (op : JasminOp)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasminDialect) op)) :
    opLeak (jasminVecMemLeak M) (.inl (.inl op)) vals = opLeak M op vals :=
  (jasminVecMem_opLeak_inl M (.inl op) vals).trans (jasminVec_opLeak_inl M op vals)

/-- A register-to-register vector operation emits no event in `jasminVecMem`. -/
theorem jasminVecMem_opLeak_vec (M : LeakModel jasminDialect) (op : X86VecOp)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := x86vec) op)) :
    opLeak (jasminVecMemLeak M) (.inl (.inr op)) vals = [] :=
  (jasminVecMem_opLeak_inl M (.inr op) vals).trans (jasminVec_opLeak_inr M op vals)

/-- **`vload` emits one address event**, the reading of its index. -/
theorem jasminVecMem_opLeak_vload (M : LeakModel jasminDialect) (w N : Nat)
    (a : Fin N → BitVec w) (i : BitVec 64) :
    opLeak (jasminVecMemLeak M) (.inr (.vload w N))
        (.cons (f := fun t : JasminTy => ⟦t⟧) (t := JasminTy.stackArr w N) a
          (.cons (f := fun t : JasminTy => ⟦t⟧) (t := JasminTy.reg 64) i .nil))
      = [CTLeak.addr "" ((M.valNat (.reg 64) i : Nat) : Int)] := rfl

/-- **`vstore` emits one address event**, the reading of its index. -/
theorem jasminVecMem_opLeak_vstore (M : LeakModel jasminDialect) (w N : Nat)
    (a : Fin N → BitVec w) (i : BitVec 64) (v : BitVec 512) :
    opLeak (jasminVecMemLeak M) (.inr (.vstore w N))
        (.cons (f := fun t : JasminTy => ⟦t⟧) (t := JasminTy.stackArr w N) a
          (.cons (f := fun t : JasminTy => ⟦t⟧) (t := JasminTy.reg 64) i
            (.cons (f := fun t : JasminTy => ⟦t⟧) (t := JasminTy.reg 512) v .nil)))
      = [CTLeak.addr "" ((M.valNat (.reg 64) i : Nat) : Int)] := rfl

/-- **`vsplat` emits no event.** -/
theorem jasminVecMem_opLeak_vsplat (M : LeakModel jasminDialect) (w : Nat)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := vecMem) (.vsplat w))) :
    opLeak (jasminVecMemLeak M) (.inr (.vsplat w)) vals = [] := rfl

/-- The constraint of an operation of `jasminVec` is its constraint in `jasminVecLeak M`. -/
@[simp] theorem jasminVecMem_opAccepts_inl (M : LeakModel jasminDialect) (op : jasminVec.Op)
    (ls : List SecretLevel) :
    opAccepts (jasminVecMemLeak M) (.inl op) ls = opAccepts (jasminVecLeak M) op ls := rfl

/-- The level checker requires a public index of `vload`. -/
theorem jasminVecMem_opAccepts_vload (M : LeakModel jasminDialect) (w N : Nat)
    (ls : List SecretLevel) :
    opAccepts (jasminVecMemLeak M) (.inr (.vload w N)) ls
      = decide (ls.getD 1 .Secret = .Public) := rfl

/-- The level checker requires a public index of `vstore`. -/
theorem jasminVecMem_opAccepts_vstore (M : LeakModel jasminDialect) (w N : Nat)
    (ls : List SecretLevel) :
    opAccepts (jasminVecMemLeak M) (.inr (.vstore w N)) ls
      = decide (ls.getD 1 .Secret = .Public) := rfl

/-- The level checker places no constraint on `vsplat`. -/
theorem jasminVecMem_opAccepts_vsplat (M : LeakModel jasminDialect) (w : Nat)
    (ls : List SecretLevel) :
    opAccepts (jasminVecMemLeak M) (.inr (.vsplat w)) ls = true := rfl

/-! ## 5. Programs of `jasminVecMem` -/

/-- The denotation of a program of `jasminVecMem`. -/
abbrev jasminVecMemDenP (fuel : Nat) {Γ : Ctxt jasminVecMem} {ts : List jasminVecMem.Ty}
    (p : NFProg jasminVecMem Γ ts) (V : Valuation Γ) : Option (Valuation ts) :=
  p.denote fuel V

/-- The leakage run of a program of `jasminVecMem` over the model `M` of `jasminDialect`. -/
abbrev jasminVecMemLeakRun (M : LeakModel jasminDialect) (fuel : Nat)
    {Γ : Ctxt jasminVecMem} {ts : List jasminVecMem.Ty} (p : NFProg jasminVecMem Γ ts)
    (V : Valuation Γ) : Option (Valuation ts × List CTLeak) :=
  NFProg.leakRun (jasminVecMemLeak M) fuel p V

/-- **The level checker on `jasminVecMem`.** A program the checker `levelCheck'` accepts at
    `jasminVecMemLeak M` for the entry labels `L` is constant time for `L` relative to the
    runs that succeed. -/
theorem jasminVecMem_nfCTRel_of_levelCheck' (M : LeakModel jasminDialect) (fuel : Nat)
    {Γ : Ctxt jasminVecMem} {ts : List jasminVecMem.Ty} (p : NFProg jasminVecMem Γ ts)
    (L : Labels Γ) (h : (NFProg.levelCheck' (jasminVecMemLeak M) p L).isSome) :
    NFCTRel (jasminVecMemLeak M) L fuel p :=
  NFProg.nfCTRel_of_levelCheck' (jasminVecMemLeak M) fuel p L h

/-! ## 6. Expressions of the three operations -/

section Exprs

variable {Γ : Ctxt jasminVecMem}

/-- The load of the lanes of width `w` from the array `a` at the index `i`. -/
def vloadE (w N : Nat) (a : Var Γ (JasminTy.stackArr w N)) (i : Var Γ (JasminTy.reg 64)) :
    Expr jasminVecMem Γ VReg :=
  ⟨.inr (.vload w N), rfl, .cons a (.cons i .nil)⟩

/-- The store of the lanes of width `w` of `v` to the array `a` at the index `i`. -/
def vstoreE (w N : Nat) (a : Var Γ (JasminTy.stackArr w N)) (i : Var Γ (JasminTy.reg 64))
    (v : Var Γ VReg) : Expr jasminVecMem Γ (JasminTy.stackArr w N) :=
  ⟨.inr (.vstore w N), rfl, .cons a (.cons i (.cons v .nil))⟩

/-- The broadcast of the register `x` to every lane of width `w`. -/
def vsplatE (w : Nat) (x : Var Γ (JasminTy.reg w)) : Expr jasminVecMem Γ VReg :=
  ⟨.inr (.vsplat w), rfl, .cons x .nil⟩

@[simp] theorem vloadE_denote (w N : Nat) (a : Var Γ (JasminTy.stackArr w N))
    (i : Var Γ (JasminTy.reg 64)) (V : Valuation Γ) :
    (vloadE w N a i).denote V = vecLoad w (a.lookup V) (BitVec.toNat (i.lookup V)) := by
  unfold Expr.denote; rfl

@[simp] theorem vstoreE_denote (w N : Nat) (a : Var Γ (JasminTy.stackArr w N))
    (i : Var Γ (JasminTy.reg 64)) (v : Var Γ VReg) (V : Valuation Γ) :
    (vstoreE w N a i v).denote V =
      vecStore w (a.lookup V) (BitVec.toNat (i.lookup V)) (v.lookup V) := rfl

@[simp] theorem vsplatE_denote (w : Nat) (x : Var Γ (JasminTy.reg w)) (V : Valuation Γ) :
    (vsplatE w x).denote V = bcast w (x.lookup V) := by
  unfold Expr.denote; rfl

/-- A load emits one address event, the reading of its index. -/
theorem vloadE_ctLeak (M : LeakModel jasminDialect) (w N : Nat)
    (a : Var Γ (JasminTy.stackArr w N)) (i : Var Γ (JasminTy.reg 64)) (V : Valuation Γ) :
    Expr.ctLeak (jasminVecMemLeak M) (vloadE w N a i) V =
      [CTLeak.addr "" ((M.valNat (.reg 64) (i.lookup V) : Nat) : Int)] := rfl

/-- A store emits one address event, the reading of its index. -/
theorem vstoreE_ctLeak (M : LeakModel jasminDialect) (w N : Nat)
    (a : Var Γ (JasminTy.stackArr w N)) (i : Var Γ (JasminTy.reg 64)) (v : Var Γ VReg)
    (V : Valuation Γ) :
    Expr.ctLeak (jasminVecMemLeak M) (vstoreE w N a i v) V =
      [CTLeak.addr "" ((M.valNat (.reg 64) (i.lookup V) : Nat) : Int)] := rfl

/-- A broadcast emits no event. -/
theorem vsplatE_ctLeak (M : LeakModel jasminDialect) (w : Nat) (x : Var Γ (JasminTy.reg w))
    (V : Valuation Γ) : Expr.ctLeak (jasminVecMemLeak M) (vsplatE w x) V = [] := rfl

end Exprs

/-! ## 7. Blocks of `jasminVec` in `jasminVecMem` -/

/-- A block of `jasminVec` as a block of `jasminVecMem`: every operation tagged `.inl`. -/
def memCom {Γ : Ctxt jasminVec} {t : JasminTy} (c : Com jasminVec Γ t) :
    Com jasminVecMem Γ t :=
  (DialectOpSum.inl (O₁ := jasminVec.Op) (O₂ := VecMemOp) (T := JasminTy)).lowerCom c

/-- **An included block has the value of the block.** -/
theorem memCom_denote {Γ : Ctxt jasminVec} {t : JasminTy} (c : Com jasminVec Γ t)
    (V : Valuation Γ) : (memCom c).denote (d := jasminVecMem) V = c.denote V :=
  DialectOpSum.inl_fundamental (O₁ := jasminVec.Op) (O₂ := VecMemOp) (T := JasminTy) c V

/-- **An included block emits the events of the block.** -/
theorem memCom_ctLeak (M : LeakModel jasminDialect) {Γ : Ctxt jasminVec} {t : JasminTy}
    (c : Com jasminVec Γ t) (V : Valuation Γ) :
    Com.ctLeak (jasminVecMemLeak M) (memCom c) V = Com.ctLeak (jasminVecLeak M) c V := by
  induction c with
  | ret _ => rfl
  | var e body ih =>
      obtain ⟨op, rfl, args⟩ := e
      have hd : DialectDenote.denote (d := jasminVecMem) (.inl op)
          (Expr.lookupArgs (d := jasminVecMem) (castArgs args) V) =
          DialectDenote.denote (d := jasminVec) op (Expr.lookupArgs args V) := by
        rw [lookupArgs_castArgs args V]
        rfl
      have hl : opLeak (jasminVecMemLeak M) (.inl op)
          (Expr.lookupArgs (d := jasminVecMem) (castArgs args) V) =
          opLeak (jasminVecLeak M) op (Expr.lookupArgs args V) := by
        rw [lookupArgs_castArgs args V, jasminVecMem_opLeak_inl]
      show opLeak (jasminVecMemLeak M) (.inl op)
          (Expr.lookupArgs (d := jasminVecMem) (castArgs args) V) ++
        Com.ctLeak (jasminVecMemLeak M) (memCom body)
          (Valuation.extend (d := jasminVecMem) V
            (DialectDenote.denote (d := jasminVecMem) (.inl op)
              (Expr.lookupArgs (d := jasminVecMem) (castArgs args) V))) =
        opLeak (jasminVecLeak M) op (Expr.lookupArgs args V) ++
          Com.ctLeak (jasminVecLeak M) body
            (Valuation.extend (d := jasminVec) V
              (DialectDenote.denote (d := jasminVec) op (Expr.lookupArgs args V)))
      rw [hl, hd, ih]
      rfl

end CatCrypt.Crypto.SecureCompilation.VIR.X86VecMem
