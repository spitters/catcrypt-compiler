/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel
public import CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum

/-!
# The dialect of x86 vector operations

`x86vec` is a dialect over the type alphabet `JasminTy` whose operations are the value
forms of the register-to-register vector instructions of `ZmmTextModel.Instr`: an
operation takes the values of the source registers and returns the value written to the
destination. An operation carries its register form `Mode`; its operands and its result
have the type `.reg m.act`, a 512-bit register at `Mode.zmm` and a 256-bit register at
`Mode.ymm`. The value of an operation is the semantic function of the text model
(`semLW`, `semShImm`, `semDup`, `semMerge`, `semPerm`, `semRol`, `semTern`, `bcast`) on
the operands widened to 512 bits (`up`), narrowed to the register (`dn`); `up m (dn m x)`
is the write `wr m x` of the text model. A mask register operand of an instruction is a
static mask of the operation. The arithmetic shift right `sra` (`vpsraq`, `vpsrad`) has
the semantic function `semSra` of this file; the text model has no instruction for it.

`jasminVec` is the operation sum `Dialect.opSum jasminDialect x86vec`: a program
interleaves scalar operations of `jasminDialect` and vector operations on registers of
the shared alphabet. Its leakage model `jasminVecLeak M` gives a scalar operation the
class of the model `M` of `jasminDialect` and makes every vector operation quiet: a
vector operation of this dialect reads and writes registers only.

## Main definitions

* `up`, `dn` — a register of the form `m` as a 512-bit value, and back.
* `semSra` — the arithmetic shift right of every lane by an immediate.
* `X86VecOp`, `x86vec`, `x86vecDenote` — the operations, the dialect and its denotation.
* `jasminVec`, `jasminVecDenote`, `jasminVecLeak` — the operation sum with
  `jasminDialect`, its denotation on programs and its leakage model.
* `VReg`, `cstE`, `bcstE`, `lwE`, `shiE`, `sraE`, `dupE`, `permE`, `blendE`, `rolE`,
  `ternE` — the 512-bit register type and the expressions of `jasminVec` on it.
* `allVec` — the blocks whose every operation is a vector operation.

## Main results

* `up_dn` — narrowing and widening is the write of the text model.
* `lane_semSra` — a lane of an arithmetic shift right.
* `lwE_denote`, `shiE_denote`, `permE_denote`, `blendE_denote` and the lemmas beside them —
  an expression on 512-bit registers has the value of the semantic function of the text
  model.
* `ctLeak_allVec` — a block of vector operations emits no event.
* `jasminVec_opLeak_inr`, `jasminVec_opLeak_inl` — a vector operation emits no event, a
  scalar operation the events of the scalar model.
* `jasminVec_nfCTRel_of_levelCheck'` — a program the level checker accepts is constant
  time relative to its runs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode LOp wr lane ofLanes lane_ofLanes
  semLW semShImm semDup semMerge semPerm semRol semTern bcast)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)
open Ctxt (Var Valuation)

/-! ## 1. Registers of a form as 512-bit values -/

/-- A register of the form `m` as a 512-bit value: a `%ymm` register is zero-extended. -/
def up : (m : Mode) → BitVec m.act → BitVec 512
  | .zmm, x => x
  | .ymm, x => x.setWidth 512

/-- The register of the form `m` that holds the active bits of a 512-bit value. -/
def dn : (m : Mode) → BitVec 512 → BitVec m.act
  | .zmm, x => x
  | .ymm, x => x.setWidth 256

/-- Narrowing to the register form and widening is the write of the text model. -/
theorem up_dn (m : Mode) (x : BitVec 512) : up m (dn m x) = wr m x := by
  cases m <;> rfl

/-- At `Mode.zmm` the widening is the identity. -/
@[simp] theorem up_zmm (x : BitVec 512) : up .zmm x = x := rfl

/-- At `Mode.zmm` the narrowing is the identity. -/
@[simp] theorem dn_zmm (x : BitVec 512) : dn .zmm x = x := rfl

/-- `vpsraq` / `vpsrad $imm`: every lane of width `L` shifted right by `imm` with sign
    fill. -/
def semSra (L imm : Nat) (x : BitVec 512) : BitVec 512 :=
  ofLanes L (fun k => (lane L x k).sshiftRight imm)

/-- Lane `k` of an arithmetic shift right. -/
theorem lane_semSra {L k : Nat} (imm : Nat) (x : BitVec 512) (hL : 0 < L)
    (hk : L * k + L ≤ 512) : lane L (semSra L imm x) k = (lane L x k).sshiftRight imm :=
  lane_ofLanes _ hL hk

/-! ## 2. The operations -/

/-- The value forms of the vector instructions. Every operation carries its register form
    `m`; `L` is a lane width in bits. -/
inductive X86VecOp where
  /-- The register constant with the active bits of `v` (`vmovdqu64 lbl(%rip), dst`). -/
  | cst (m : Mode) (v : BitVec 512)
  /-- Every lane of width `L` holding `c` (`vpbroadcastq` / `vpbroadcastd lbl(%rip), dst`). -/
  | bcst (m : Mode) (L c : Nat)
  /-- The lane-wise operation `o` at width `L` on the operands `src1`, `src2`
      (`vpaddq`, `vpsubd`, `vpmuludq`, `vpminuq`, `vpxorq`, …). -/
  | lw (m : Mode) (L : Nat) (o : LOp)
  /-- The shift of every lane by the immediate `imm`, left or logical right
      (`vpsllq`, `vpsrlq`, `vpslld`, `vpsrld`). -/
  | shi (m : Mode) (L : Nat) (left : Bool) (imm : Nat)
  /-- The arithmetic shift right of every lane by the immediate `imm` (`vpsraq`, `vpsrad`). -/
  | sra (m : Mode) (L imm : Nat)
  /-- `vmovshdup` (`odd`) or `vmovsldup`. -/
  | dup (m : Mode) (odd : Bool)
  /-- `vmovshdup` or `vmovsldup` merged under the mask `k` into the second operand, the
      old value of the destination. -/
  | dupMerge (m : Mode) (odd : Bool) (k : BitVec 16)
  /-- `vmovdqa64`. -/
  | mova (m : Mode)
  /-- `vpermd`: the operands are the source and the index register. -/
  | perm (m : Mode)
  /-- `vpblendmd` under the mask `k`: dword `j` of the first operand where bit `j` of `k`
      is set, else dword `j` of the second. -/
  | blend (m : Mode) (k : BitVec 16)
  /-- The rotation left of every lane by the immediate `imm` (`vprolq`, `vprold`). -/
  | rol (m : Mode) (L imm : Nat)
  /-- `vpternlogq` (`L = 64`) or `vpternlogd` (`L = 32`) with the truth table `imm`: the
      operands are the old value of the destination, the second and the third source. -/
  | tern (m : Mode) (L : Nat) (imm : BitVec 8)
  deriving DecidableEq

/-- The register form of an operation. -/
def X86VecOp.mode : X86VecOp → Mode
  | .cst m _ | .bcst m _ _ | .lw m _ _ | .shi m _ _ _ | .sra m _ _ | .dup m _
  | .dupMerge m _ _ | .mova m | .perm m | .blend m _ | .rol m _ _ | .tern m _ _ => m

/-- The number of operands of an operation. -/
def X86VecOp.arity : X86VecOp → Nat
  | .cst _ _ | .bcst _ _ _ => 0
  | .shi _ _ _ _ | .sra _ _ _ | .dup _ _ | .mova _ | .rol _ _ _ => 1
  | .lw _ _ _ | .dupMerge _ _ _ | .perm _ | .blend _ _ => 2
  | .tern _ _ _ => 3

/-- The dialect of x86 vector operations over the type alphabet `JasminTy`. -/
@[reducible] def x86vec : Dialect := { Op := X86VecOp, Ty := JasminTy }

/-- The signature of a vector operation: registers of its form. -/
instance instDialectSignatureX86Vec : DialectSignature x86vec where
  sig
    | .cst _ _ => []
    | .bcst _ _ _ => []
    | .lw m _ _ => [.reg m.act, .reg m.act]
    | .shi m _ _ _ => [.reg m.act]
    | .sra m _ _ => [.reg m.act]
    | .dup m _ => [.reg m.act]
    | .dupMerge m _ _ => [.reg m.act, .reg m.act]
    | .mova m => [.reg m.act]
    | .perm m => [.reg m.act, .reg m.act]
    | .blend m _ => [.reg m.act, .reg m.act]
    | .rol m _ _ => [.reg m.act]
    | .tern m _ _ => [.reg m.act, .reg m.act, .reg m.act]
  ret op := .reg op.mode.act

/-- The value of a vector operation: the semantic function of the text model on the
    widened operands, narrowed to the register form. -/
instance x86vecDenote : DialectDenote x86vec where
  denote
    | .cst m v => fun _ => dn m v
    | .bcst m L c => fun _ => dn m (bcast L (BitVec.ofNat L c))
    | .lw m L o => fun args =>
        let a : BitVec m.act := args.head
        let b : BitVec m.act := args.tail.head
        dn m (semLW L o (up m a) (up m b))
    | .shi m L left imm => fun args =>
        let a : BitVec m.act := args.head
        dn m (semShImm L left imm (up m a))
    | .sra m L imm => fun args =>
        let a : BitVec m.act := args.head
        dn m (semSra L imm (up m a))
    | .dup m odd => fun args =>
        let a : BitVec m.act := args.head
        dn m (semDup odd (up m a))
    | .dupMerge m odd k => fun args =>
        let a : BitVec m.act := args.head
        let old : BitVec m.act := args.tail.head
        dn m (semMerge k (semDup odd (up m a)) (up m old))
    | .mova m => fun args =>
        let a : BitVec m.act := args.head
        dn m (up m a)
    | .perm m => fun args =>
        let src : BitVec m.act := args.head
        let idx : BitVec m.act := args.tail.head
        dn m (semPerm (m.act / 32) (up m src) (up m idx))
    | .blend m k => fun args =>
        let a : BitVec m.act := args.head
        let b : BitVec m.act := args.tail.head
        dn m (semMerge k (up m a) (up m b))
    | .rol m L imm => fun args =>
        let a : BitVec m.act := args.head
        dn m (semRol L imm (up m a))
    | .tern m _ imm => fun args =>
        let a : BitVec m.act := args.head
        let b : BitVec m.act := args.tail.head
        let c : BitVec m.act := args.tail.tail.head
        dn m (semTern imm (up m a) (up m b) (up m c))

/-! ## 3. The operation sum with `jasminDialect` -/

/-- The operation sum of `jasminDialect` and `x86vec` over `JasminTy`. -/
abbrev jasminVec : Dialect.{0, 0} := Dialect.opSum jasminDialect x86vec

/-- The signature of `jasminVec`: the signature of the summand. -/
instance instDialectSignatureJasminVec : DialectSignature jasminVec where
  sig
    | .inl o => DialectSignature.sig (d := jasminDialect) o
    | .inr o => DialectSignature.sig (d := x86vec) o
  ret
    | .inl o => DialectSignature.ret (d := jasminDialect) o
    | .inr o => DialectSignature.ret (d := x86vec) o

/-- The value of an operation of `jasminVec`: the value in its summand. -/
instance instDialectDenoteJasminVec : DialectDenote jasminVec where
  denote
    | .inl o => fun args => DialectDenote.denote (d := jasminDialect) o args
    | .inr o => fun args => DialectDenote.denote (d := x86vec) o args

/-- The trip counter of `jasminVec` is the 64-bit register. -/
instance instHasWord64JasminVec : HasWord64 jasminVec where
  word := HasWord64.word (d := jasminDialect)
  toNat := HasWord64.toNat (d := jasminDialect)
  ofNat := HasWord64.ofNat (d := jasminDialect)

/-- The bit of `jasminVec` is the 1-bit register. -/
instance instHasBoolBitJasminVec : HasBoolBit jasminVec where
  bit := HasBitType.bit (d := jasminDialect)
  toBool := HasBoolBit.toBool (d := jasminDialect)

/-- `jasminVec` denotes calls in the empty environment. -/
instance instCallDenoteJasminVec : CallDenote jasminVec := ⟨.empty⟩

/-- The denotation of `jasminVec` on programs: both summands are total. -/
@[instance_reducible] def jasminVecDenote : DialectDenoteM jasminVec Option :=
  instDialectDenoteMOptionOfPure jasminVec

/-- A scalar operation has in `jasminVec` its value in `jasminDialect`. -/
@[simp] theorem jasminVec_denote_inl (o : JasminOp)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasminDialect) o)) :
    DialectDenote.denote (d := jasminVec) (.inl o) args =
      DialectDenote.denote (d := jasminDialect) o args := rfl

/-- A vector operation has in `jasminVec` its value in `x86vec`. -/
@[simp] theorem jasminVec_denote_inr (o : X86VecOp)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := x86vec) o)) :
    DialectDenote.denote (d := jasminVec) (.inr o) args =
      DialectDenote.denote (d := x86vec) o args := rfl

/-! ## 4. The leakage model -/

/-- The leakage model of `jasminVec` over a model `M` of `jasminDialect`: a scalar
    operation has its class in `M`, a vector operation is quiet, and a value has the
    reading of `M`. -/
def jasminVecLeak (M : LeakModel jasminDialect) : LeakModel jasminVec where
  kind := Sum.elim M.kind (fun _ => .quiet)
  valNat := M.valNat

/-- A scalar operation has the class `M` gives it. -/
@[simp] theorem jasminVecLeak_kind_inl (M : LeakModel jasminDialect) (op : JasminOp) :
    (jasminVecLeak M).kind (.inl op) = M.kind op := rfl

/-- A vector operation is quiet. -/
@[simp] theorem jasminVecLeak_kind_inr (M : LeakModel jasminDialect) (op : X86VecOp) :
    (jasminVecLeak M).kind (.inr op) = .quiet := rfl

/-- The readings of a list of values are those of `M`. -/
theorem jasminVec_valsNat (M : LeakModel jasminDialect) :
    ∀ {ts : List JasminTy} (vals : HVector (fun t => ⟦t⟧) ts),
      valsNat (jasminVecLeak M) vals = valsNat M vals
  | [], .nil => rfl
  | _ :: _, .cons x xs => by
      show M.valNat _ x :: valsNat (jasminVecLeak M) xs = M.valNat _ x :: valsNat M xs
      rw [jasminVec_valsNat M xs]

/-- **A scalar operation emits in `jasminVec` the events it emits in `jasminDialect`.** -/
theorem jasminVec_opLeak_inl (M : LeakModel jasminDialect) (op : JasminOp)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasminDialect) op)) :
    opLeak (jasminVecLeak M) (.inl op) vals = opLeak M op vals := by
  unfold opLeak
  rw [jasminVecLeak_kind_inl, jasminVec_valsNat M vals]

/-- **A vector operation emits no event.** -/
theorem jasminVec_opLeak_inr (M : LeakModel jasminDialect) (op : X86VecOp)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := x86vec) op)) :
    opLeak (jasminVecLeak M) (.inr op) vals = [] := rfl

/-- The constraint of a scalar operation is its constraint in `M`. -/
@[simp] theorem jasminVec_opAccepts_inl (M : LeakModel jasminDialect) (op : JasminOp)
    (ls : List SecretLevel) :
    opAccepts (jasminVecLeak M) (.inl op) ls = opAccepts M op ls := rfl

/-- The level checker places no constraint on a vector operation. -/
@[simp] theorem jasminVec_opAccepts_inr (M : LeakModel jasminDialect) (op : X86VecOp)
    (ls : List SecretLevel) : opAccepts (jasminVecLeak M) (.inr op) ls = true := rfl

/-! ## 5. Programs of `jasminVec` -/

/-- The denotation of a program of `jasminVec`. -/
abbrev jasminVecDenP (fuel : Nat) {Γ : Ctxt jasminVec} {ts : List jasminVec.Ty}
    (p : NFProg jasminVec Γ ts) (V : Valuation Γ) : Option (Valuation ts) :=
  p.denote fuel V

/-- The leakage run of a program of `jasminVec` over the model `M` of `jasminDialect`. -/
abbrev jasminVecLeakRun (M : LeakModel jasminDialect) (fuel : Nat) {Γ : Ctxt jasminVec}
    {ts : List jasminVec.Ty} (p : NFProg jasminVec Γ ts) (V : Valuation Γ) :
    Option (Valuation ts × List CTLeak) :=
  NFProg.leakRun (jasminVecLeak M) fuel p V

/-- **The level checker on `jasminVec`.** A program the checker `levelCheck'` accepts at
    `jasminVecLeak M` for the entry labels `L` is constant time for `L` relative to the runs
    that succeed. -/
theorem jasminVec_nfCTRel_of_levelCheck' (M : LeakModel jasminDialect) (fuel : Nat)
    {Γ : Ctxt jasminVec} {ts : List jasminVec.Ty} (p : NFProg jasminVec Γ ts) (L : Labels Γ)
    (h : (NFProg.levelCheck' (jasminVecLeak M) p L).isSome) :
    NFCTRel (jasminVecLeak M) L fuel p :=
  NFProg.nfCTRel_of_levelCheck' (jasminVecLeak M) fuel p L h

/-! ## 6. Expressions on 512-bit registers -/

/-- The 512-bit register type. -/
abbrev VReg : JasminTy := .reg 512

section Exprs

variable {Γ : Ctxt jasminVec}

/-- The register constant `v`. -/
def cstE (v : BitVec 512) : Expr jasminVec Γ VReg := ⟨.inr (.cst .zmm v), rfl, .nil⟩

/-- Every lane of width `L` holding `c`. -/
def bcstE (L c : Nat) : Expr jasminVec Γ VReg := ⟨.inr (.bcst .zmm L c), rfl, .nil⟩

/-- The lane-wise operation `o` at width `L` on `a` and `b`. -/
def lwE (L : Nat) (o : LOp) (a b : Var Γ VReg) : Expr jasminVec Γ VReg :=
  ⟨.inr (.lw .zmm L o), rfl, .cons a (.cons b .nil)⟩

/-- The shift of every lane of `a` by the immediate `imm`. -/
def shiE (L : Nat) (left : Bool) (imm : Nat) (a : Var Γ VReg) : Expr jasminVec Γ VReg :=
  ⟨.inr (.shi .zmm L left imm), rfl, .cons a .nil⟩

/-- The arithmetic shift right of every lane of `a` by the immediate `imm`. -/
def sraE (L imm : Nat) (a : Var Γ VReg) : Expr jasminVec Γ VReg :=
  ⟨.inr (.sra .zmm L imm), rfl, .cons a .nil⟩

/-- The dword duplication of `a`. -/
def dupE (odd : Bool) (a : Var Γ VReg) : Expr jasminVec Γ VReg :=
  ⟨.inr (.dup .zmm odd), rfl, .cons a .nil⟩

/-- The dword permutation of `src` by the index register `idx`. -/
def permE (src idx : Var Γ VReg) : Expr jasminVec Γ VReg :=
  ⟨.inr (.perm .zmm), rfl, .cons src (.cons idx .nil)⟩

/-- The dword blend under the mask `k`: `a` where the bit is set, else `b`. -/
def blendE (k : BitVec 16) (a b : Var Γ VReg) : Expr jasminVec Γ VReg :=
  ⟨.inr (.blend .zmm k), rfl, .cons a (.cons b .nil)⟩

/-- The rotation left of every lane of `a` by the immediate `imm`. -/
def rolE (L imm : Nat) (a : Var Γ VReg) : Expr jasminVec Γ VReg :=
  ⟨.inr (.rol .zmm L imm), rfl, .cons a .nil⟩

/-- The three-input logic operation with the truth table `imm`. -/
def ternE (L : Nat) (imm : BitVec 8) (a b c : Var Γ VReg) : Expr jasminVec Γ VReg :=
  ⟨.inr (.tern .zmm L imm), rfl, .cons a (.cons b (.cons c .nil))⟩

@[simp] theorem cstE_denote (v : BitVec 512) (V : Valuation Γ) :
    (cstE v (Γ := Γ)).denote V = v := by
  unfold Expr.denote; exact dn_zmm _

@[simp] theorem bcstE_denote (L c : Nat) (V : Valuation Γ) :
    (bcstE L c (Γ := Γ)).denote V = bcast L (BitVec.ofNat L c) := by
  unfold Expr.denote; exact dn_zmm _

@[simp] theorem lwE_denote (L : Nat) (o : LOp) (a b : Var Γ VReg) (V : Valuation Γ) :
    (lwE L o a b).denote V = semLW L o (a.lookup V) (b.lookup V) := by
  unfold Expr.denote; exact dn_zmm _

@[simp] theorem shiE_denote (L : Nat) (left : Bool) (imm : Nat) (a : Var Γ VReg)
    (V : Valuation Γ) : (shiE L left imm a).denote V = semShImm L left imm (a.lookup V) := by
  unfold Expr.denote; exact dn_zmm _

@[simp] theorem sraE_denote (L imm : Nat) (a : Var Γ VReg) (V : Valuation Γ) :
    (sraE L imm a).denote V = semSra L imm (a.lookup V) := by
  unfold Expr.denote; exact dn_zmm _

@[simp] theorem dupE_denote (odd : Bool) (a : Var Γ VReg) (V : Valuation Γ) :
    (dupE odd a).denote V = semDup odd (a.lookup V) := by
  unfold Expr.denote; exact dn_zmm _

@[simp] theorem permE_denote (src idx : Var Γ VReg) (V : Valuation Γ) :
    (permE src idx).denote V = semPerm 16 (src.lookup V) (idx.lookup V) := by
  unfold Expr.denote; exact dn_zmm _

@[simp] theorem blendE_denote (k : BitVec 16) (a b : Var Γ VReg) (V : Valuation Γ) :
    (blendE k a b).denote V = semMerge k (a.lookup V) (b.lookup V) := by
  unfold Expr.denote; exact dn_zmm _

@[simp] theorem rolE_denote (L imm : Nat) (a : Var Γ VReg) (V : Valuation Γ) :
    (rolE L imm a).denote V = semRol L imm (a.lookup V) := by
  unfold Expr.denote; exact dn_zmm _

@[simp] theorem ternE_denote (L : Nat) (imm : BitVec 8) (a b c : Var Γ VReg) (V : Valuation Γ) :
    (ternE L imm a b c).denote V = semTern imm (a.lookup V) (b.lookup V) (c.lookup V) := by
  unfold Expr.denote; exact dn_zmm _

end Exprs

/-- A block whose every operation is a vector operation. -/
def allVec : {Γ : Ctxt jasminVec} → {t : JasminTy} → Com jasminVec Γ t → Prop
  | _, _, .ret _ => True
  | _, _, .var e body => (∃ o, e.op = .inr o) ∧ allVec body

/-- A block of vector operations emits no event. -/
theorem ctLeak_allVec (M : LeakModel jasminDialect) :
    ∀ {Γ : Ctxt jasminVec} {t : JasminTy} (c : Com jasminVec Γ t), allVec c →
      ∀ V : Valuation Γ, Com.ctLeak (jasminVecLeak M) c V = []
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, h, V => by
      show Expr.ctLeak (jasminVecLeak M) e V ++ Com.ctLeak (jasminVecLeak M) body _ = []
      rw [ctLeak_allVec M body h.2]
      obtain ⟨op, hty, args⟩ := e
      obtain ⟨o, ho⟩ := h.1
      cases ho
      rfl

end CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
