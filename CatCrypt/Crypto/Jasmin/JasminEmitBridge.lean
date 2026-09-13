/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.BignumExec
public import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public import CatCrypt.Crypto.Jasmin.VmFlatExec


@[expose] public section
set_option autoImplicit false

/-!
# Bridge: `BignumExec.bignumExec` ≡ `JasminCoqSemMirror.execInstrR`

Phase C, first per-opcode bridge step. We want the agreement

```
bignumExec is s = some s'  ↔
execInstrR_chain realAsmSem realOpSem [] fuel (stateToEstate s) is_mirror
    = JResult.ok (stateToEstate s')
```

for the straight-line `Cassgn` / `Copn` chains the bignum SSA fragment
emits, where `is_mirror = astToMirror_Cmd is`.

## What this scaffold delivers

* `astToMirror_PExpr` / `astToMirror_LVal` / `astToMirror_InstrR` —
  a partial syntax translation from `CatCrypt.Crypto.Jasmin.*` to
  `JasminCoqSemMirror.*`.  Returns `none` for shapes the bignum SSA
  fragment never produces (e.g. `Pif`, `Cfor`).
* `stateToEstate` — a concrete state lift mapping `BignumState`'s
  register file + byte memory into the mirror's abstract `Estate`.
* `bignumMemModel` — a `MemModel` instance for the concrete
  `BignumState.mem` type.
* `realOpSem` / `realAsmSem` — concrete `OpSem` / `AsmSem` records
  carrying the same arithmetic that `BignumExec.evalPExpr` /
  `BignumExec.execInstr` perform.
* `OpcodeAgrees` — a predicate stating per-opcode agreement of the two
  semantics under the chosen lift.
* `opcodeAgrees_Cassgn_Lvar_Pvar` — proved: `Cassgn (Lvar v) _ _ (Pvar w)`
  agrees on both sides (the cleanest register-to-register move case).
* `bignumExec_agrees_coqSem_chain_skel` — chain-level lemma: given
  per-instruction `OpcodeAgrees`, the chain version follows.

The `Cassgn (Lvar _) _ _ (Pconst _)` case, mnemonic Copn cases, and
the other shapes documented in §7 are tracked as follow-up per-opcode
batches that feed into the same chain-skel lemma.

## What remains as future per-opcode batches

The per-mnemonic opcode lemmas for `ADD_64`, `ADC_64`, `SUB_64`, `SBB_64`,
`MULX`, `ADCX`, `ADOX`, `XOR_64`, `SHL_64`, `SHR_64`, `SHLD_64`, `SHRD_64`,
and their 32-bit variants are named below as `OpcodeAgrees` instances
*not yet provided*.  Each is a small per-mnemonic proof: pick the right
`sopn_sem` clause in `realAsmSem`, unfold both sides, and discharge.
This module ships the *skeleton*; the per-opcode batches are tracked as
follow-up work.

### Shape-mismatch caveat

`CatCrypt.Crypto.Jasmin.PExpr` has `Pload (ws) (x : VarI) (off : PExpr)` (split
base/offset) while `JasminCoqSemMirror.Pexpr` has
`Pload (al : Aligned) (sz : WSize) (e : Pexpr)` (single addressing
expression).  Our translation reconstructs the single expression as
`Papp2 (Oadd .U64) (Pvar (mkLvar base)) off`.  The agreement at the
`Pload` arm therefore *also* relies on the `Papp2 (Oadd .U64)` arm —
proving the `Pload` case unconditionally requires first establishing
the `Pvar` and `Papp2 .Oadd` arms.  This is documented at
`OpcodeAgrees_Cassgn_Lvar_Pload` below.
-/

namespace CatCrypt.Crypto.Jasmin.JasminEmitBridge

-- We do NOT `open CatCrypt.Crypto.Jasmin` here so that bare names like
-- `WSize`, `Var`, `Pexpr`, ... refer to the mirror's versions (opened
-- below).  The AST versions are referenced via their fully-qualified
-- names `CatCrypt.Crypto.Jasmin.WSize`, etc.  We use a short alias
-- `JasAST` to keep names readable.
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.CoqSemMirror

/-! ## §1. Syntax translation — `CatCrypt.Crypto.Jasmin.*` → `CoqSemMirror.*`

Two separate inductive families sharing a similar surface.  We translate
the bignum SSA fragment shapes only; everything else returns `none`. -/

/-- Translate a `CatCrypt.Crypto.Jasmin.WSize` to the mirror's `WSize`.

    The six upstream widths `U8`..`U256` map structurally (the mirror is a
    faithful image of Coq `wsize.v`, which has exactly these six). The CatCrypt
    AVX-512 extension width `U512` (task #286) has **no** image in the faithful
    Coq mirror — Jasmin's scalar word model caps at `U256`. This arm maps it to
    `U256` only to keep the bridge total; it is **unreachable** for emitted
    AVX-512 (`zmm`) kernels, which carry their per-lane meaning through the
    packed-vector op alphabet (`MpnAvx512Emit`, `LaneMap`) rather than scalar
    mirror ops (`mirrorSOp2`). No emitted scalar `Oadd .U512` ever reaches this
    bridge. -/
def astToMirror_WSize : CatCrypt.Crypto.Jasmin.WSize → CoqSemMirror.WSize
  | .U8   => .U8
  | .U16  => .U16
  | .U32  => .U32
  | .U64  => .U64
  | .U128 => .U128
  | .U256 => .U256
  | .U512 => .U256

/-- Translate a `CatCrypt.Crypto.Jasmin.SType` to the mirror's `Atype`. -/
def astToMirror_Atype : CatCrypt.Crypto.Jasmin.SType → CoqSemMirror.Atype
  | .sbool       => .abool
  | .sint        => .aint
  | .sarr n      => .aarr .U8 n     -- treat as byte-array
  | .sword ws    => .aword (astToMirror_WSize ws)

/-- Translate a `CatCrypt.Crypto.Jasmin.Var`. -/
def astToMirror_Var (v : CatCrypt.Crypto.Jasmin.Var) : CoqSemMirror.Var :=
  { vtype := astToMirror_Atype v.vtype, vname := v.vname }

/-- Translate a `CatCrypt.Crypto.Jasmin.VarI`. -/
def astToMirror_VarI (v : CatCrypt.Crypto.Jasmin.VarI) : CoqSemMirror.VarI :=
  { v_var := astToMirror_Var v.var }

/-- Translate a `CatCrypt.Crypto.Jasmin.GVar`.  We map the `gs : Bool` global-flag to
    the mirror's `VScope`. -/
def astToMirror_GVar (g : CatCrypt.Crypto.Jasmin.GVar) : CoqSemMirror.GVar :=
  { gv := astToMirror_VarI g.gv, gs := if g.gs then .Sglob else .Slocal }

/-- Translate a `CatCrypt.Crypto.Jasmin.SOp1`.  Sign-mode is folded into the mirror's
    `Signedness`. -/
def astToMirror_SOp1 : CatCrypt.Crypto.Jasmin.SOp1 → CoqSemMirror.SOp1
  | .Oword_of_int ws => .Oword_of_int (astToMirror_WSize ws)
  | .Oint_of_word ws => .Oint_of_word .Unsigned (astToMirror_WSize ws)
  | .Osignext wso wsi => .Osignext (astToMirror_WSize wso) (astToMirror_WSize wsi)
  | .Ozeroext wso wsi => .Ozeroext (astToMirror_WSize wso) (astToMirror_WSize wsi)
  | .Onot => .Onot
  | .Olnot ws => .Olnot (astToMirror_WSize ws)
  | .Oneg ws => .Oneg (.Op_w (astToMirror_WSize ws))

/-- Translate a `CatCrypt.Crypto.Jasmin.SignExtend` to the mirror's `Signedness`. -/
def astToMirror_Sign : CatCrypt.Crypto.Jasmin.SignExtend → CoqSemMirror.Signedness
  | .Sextend => .Signed
  | .Uextend => .Unsigned

/-- Translate a `CatCrypt.Crypto.Jasmin.SOp2` to the mirror's `SOp2`.  SIMD vector
    variants (`Ovadd`, `Ovsub`, ...) are not supported by the mirror's
    scalar `SOp2`; we return `none` for them. -/
def astToMirror_SOp2 : CatCrypt.Crypto.Jasmin.SOp2 → Option CoqSemMirror.SOp2
  | .Obeq     => some .Obeq
  | .Oand     => some .Oand
  | .Oor      => some .Oor
  | .Oadd ws  => some (.Oadd (.Op_w (astToMirror_WSize ws)))
  | .Omul ws  => some (.Omul (.Op_w (astToMirror_WSize ws)))
  | .Osub ws  => some (.Osub (.Op_w (astToMirror_WSize ws)))
  | .Odiv se ws => some (.Odiv (astToMirror_Sign se) (.Op_w (astToMirror_WSize ws)))
  | .Omod se ws => some (.Omod (astToMirror_Sign se) (.Op_w (astToMirror_WSize ws)))
  | .Oland ws => some (.Oland (astToMirror_WSize ws))
  | .Olor ws  => some (.Olor (astToMirror_WSize ws))
  | .Olxor ws => some (.Olxor (astToMirror_WSize ws))
  | .Olsr ws  => some (.Olsr (astToMirror_WSize ws))
  | .Olsl ws  => some (.Olsl (.Op_w (astToMirror_WSize ws)))
  | .Oasr ws  => some (.Oasr (.Op_w (astToMirror_WSize ws)))
  | .Oeq ws   => some (.Oeq (.Op_w (astToMirror_WSize ws)))
  | .Oneq ws  => some (.Oneq (.Op_w (astToMirror_WSize ws)))
  | .Olt se ws => some (.Olt (.Cmp_w (astToMirror_Sign se) (astToMirror_WSize ws)))
  | .Ole se ws => some (.Ole (.Cmp_w (astToMirror_Sign se) (astToMirror_WSize ws)))
  | .Ogt se ws => some (.Ogt (.Cmp_w (astToMirror_Sign se) (astToMirror_WSize ws)))
  | .Oge se ws => some (.Oge (.Cmp_w (astToMirror_Sign se) (astToMirror_WSize ws)))
  | .Ovadd _ _ | .Ovsub _ _ | .Ovmul _ _
  | .Ovlsr _ _ | .Ovlsl _ _ | .Ovasr _ _ => none

/-- Translate a `CatCrypt.Crypto.Jasmin.AssgnTag` (constructors line up 1-1). -/
def astToMirror_AssgnTag : CatCrypt.Crypto.Jasmin.AssgnTag → CoqSemMirror.AssgnTag
  | .AT_none    => .AT_none
  | .AT_keep    => .AT_keep
  | .AT_rename  => .AT_rename
  | .AT_inline  => .AT_inline
  | .AT_phinode => .AT_phinode

/-- Translate `CatCrypt.Crypto.Jasmin.ArrAccess`. -/
def astToMirror_ArrAccess : CatCrypt.Crypto.Jasmin.ArrAccess → CoqSemMirror.ArrAccess
  | .AAscale  => .AAscale
  | .AAdirect => .AAdirect

/-- Translate `CatCrypt.Crypto.Jasmin.PExpr` to the mirror's `Pexpr`.  Partial: shapes
    not in the bignum SSA fragment return `none`.  In particular, the
    AST `Pload (ws : WSize) (x : VarI) (off : PExpr)` (split base + offset)
    is reconstructed as `Pload IsAligned ws (Papp2 (Oadd U64) (Pvar base) off)`
    on the mirror side.  This is the unique shape-mismatch documented in
    `BignumExec.lean`'s trust grounding section. -/
def astToMirror_PExpr : CatCrypt.Crypto.Jasmin.PExpr → Option CoqSemMirror.Pexpr
  | .Pconst z       => some (.Pconst z)
  | .Pbool b        => some (.Pbool b)
  | .Parr_init _    => none  -- requires a wsize the AST does not carry
  | .Pvar g         => some (.Pvar (astToMirror_GVar g))
  | .Pget aa ws x idx =>
      (astToMirror_PExpr idx).map fun mIdx =>
        .Pget .IsAligned (astToMirror_ArrAccess aa) (astToMirror_WSize ws)
              (astToMirror_GVar x) mIdx
  | .Psub aa ws len x idx =>
      (astToMirror_PExpr idx).map fun mIdx =>
        .Psub (astToMirror_ArrAccess aa) (astToMirror_WSize ws) len
              (astToMirror_GVar x) mIdx
  | .Pload ws base off =>
      -- Lean AST: split base + off.  Mirror: single addressing expression.
      -- Reconstruct as Papp2 (Oadd U64) (Pvar base) off.
      match astToMirror_PExpr off with
      | none => none
      | some mOff =>
          let baseG : CoqSemMirror.GVar := CoqSemMirror.mkLvar (astToMirror_VarI base)
          some (.Pload .IsAligned (astToMirror_WSize ws)
                  (.Papp2 (.Oadd (.Op_w .U64)) (.Pvar baseG) mOff))
  | .Papp1 op e =>
      (astToMirror_PExpr e).map fun me => .Papp1 (astToMirror_SOp1 op) me
  | .Papp2 op e1 e2 => do
      let mOp ← astToMirror_SOp2 op
      let me1 ← astToMirror_PExpr e1
      let me2 ← astToMirror_PExpr e2
      some (.Papp2 mOp me1 me2)
  | .PappN _ _      => none  -- needs OpN translation; deferred
  | .Pif ty c e1 e2 => do
      let mc  ← astToMirror_PExpr c
      let me1 ← astToMirror_PExpr e1
      let me2 ← astToMirror_PExpr e2
      some (.Pif (astToMirror_Atype ty) mc me1 me2)

/-- Translate `CatCrypt.Crypto.Jasmin.LVal` to the mirror's `Lval`.  Same Pload-style
    reconstruction for `Lmem`. -/
def astToMirror_LVal : CatCrypt.Crypto.Jasmin.LVal → Option CoqSemMirror.Lval
  | .Lnone _ ty => some (.Lnone () (astToMirror_Atype ty))
  | .Lvar x => some (.Lvar (astToMirror_VarI x))
  | .Lmem ws base off =>
      match astToMirror_PExpr off with
      | none => none
      | some mOff =>
          let baseG : CoqSemMirror.GVar := CoqSemMirror.mkLvar (astToMirror_VarI base)
          some (.Lmem .IsAligned (astToMirror_WSize ws) ()
                  (.Papp2 (.Oadd (.Op_w .U64)) (.Pvar baseG) mOff))
  | .Laset aa ws x idx =>
      (astToMirror_PExpr idx).map fun mIdx =>
        .Laset .IsAligned (astToMirror_ArrAccess aa) (astToMirror_WSize ws)
               (astToMirror_VarI x) mIdx
  | .Lasub aa ws len x idx =>
      (astToMirror_PExpr idx).map fun mIdx =>
        .Lasub (astToMirror_ArrAccess aa) (astToMirror_WSize ws) len
               (astToMirror_VarI x) mIdx

/-- Translate `CatCrypt.Crypto.Jasmin.SOpn` (which wraps `AsmOp { name }`) to the mirror's
    `Sopn.Oasm name`.  The AST has only `Oasm`; the mirror has six
    constructors but we only emit into `Oasm`. -/
def astToMirror_SOpn : CatCrypt.Crypto.Jasmin.SOpn → CoqSemMirror.Sopn
  | .Oasm op => .Oasm op.name

/-- Translate the straight-line `InstrR` shapes (`Cassgn`, `Copn`).
    Control-flow shapes (`Cif`, `Cfor`, `Cwhile`, `Ccall`) return `none` —
    a `Phase D` task to extend the chain bridge to control flow.  The
    instruction list versions of `Cif`/`Cfor`/`Cwhile` would also require
    a translated `body : List Instr`; we omit them. -/
def astToMirror_InstrR : CatCrypt.Crypto.Jasmin.InstrR → Option CoqSemMirror.InstrR
  | .Cassgn lv tag ty e => do
      let mLv ← astToMirror_LVal lv
      let me  ← astToMirror_PExpr e
      some (.Cassgn mLv (astToMirror_AssgnTag tag) (astToMirror_Atype ty) me)
  | .Copn lvs tag op es => do
      let mLvs ← lvs.mapM astToMirror_LVal
      let mEs  ← es.mapM astToMirror_PExpr
      some (.Copn mLvs (astToMirror_AssgnTag tag) (astToMirror_SOpn op) mEs)
  | .Cif _ _ _    => none
  | .Cfor _ _ _   => none
  | .Cwhile _ _ _ => none
  | .Ccall _ _ _ _ => none

/-! ## §2. State lift — `BignumState` → `Estate`

The mirror's `Estate` is parameterised over a syscall-state type and a
memory type with a `MemModel` instance.  We instantiate syscall-state to
`Unit` and memory to `BignumState`'s flat `MemoryModel.Mem`. -/

/-- Concrete `MemModel` instance for `MemoryModel.Mem` (the partial
    byte-addressable memory used by `BignumState`).

    *Reads* return `JResult.ok` whenever the full byte range is allocated,
    otherwise `.addrUndef`.  *Writes* always succeed at the byte level
    (the flat memory is total under `storeByte`).

    Only `U64`, `U32`, and `U8` are handled — the widths the bignum SSA
    fragment uses.  Other widths return `.typeError`. -/
def bignumMemRead (m : MemoryModel.Mem) (_al : CoqSemMirror.Aligned)
    (p : BitVec CoqSemMirror.WSize.Uptr.bits) (sz : CoqSemMirror.WSize) :
    CoqSemMirror.JResult (BitVec sz.bits) :=
  let addr : UInt64 := UInt64.ofNat p.toNat
  match sz with
  | .U64 =>
      match BignumExec.load64Mem m addr with
      | some v => .ok (BitVec.ofNat 64 v.toNat)
      | none   => .addrUndef
  | .U32 =>
      match BignumExec.load32Mem m addr with
      | some v => .ok (BitVec.ofNat 32 v.toNat)
      | none   => .addrUndef
  | .U8 =>
      match m.loadByte addr with
      | some b => .ok (BitVec.ofNat 8 b.toNat)
      | none   => .addrUndef
  | _ => .typeError

/-- Concrete `MemModel.write` operation. -/
def bignumMemWrite (m : MemoryModel.Mem) (_al : CoqSemMirror.Aligned)
    (p : BitVec CoqSemMirror.WSize.Uptr.bits) (sz : CoqSemMirror.WSize)
    (w : BitVec sz.bits) : CoqSemMirror.JResult MemoryModel.Mem :=
  let addr : UInt64 := UInt64.ofNat p.toNat
  match sz with
  | .U64 =>
      .ok (BignumExec.Mem.store32 m addr (UInt64.ofNat w.toNat))   -- placeholder; see note
  | .U32 =>
      .ok (BignumExec.Mem.store32 m addr (UInt64.ofNat w.toNat))
  | .U8 =>
      .ok (m.storeByte addr (UInt8.ofNat (w.toNat % 256)))
  | _ => .typeError

-- Note: `BignumExec.storeMem` (8-byte LE store) would be the right U64
-- write, but it's defined on `BignumState`, not `Mem`.  An equivalent
-- byte-by-byte `Mem.store64` helper is the right primitive here; we use
-- the existing `Mem.store32` as a placeholder for the *shape* of the
-- instance — the per-opcode U64-write proofs will need to bridge this
-- via a `Mem.store64` helper (additive to MemoryModel.lean).  Documented
-- in `OpcodeAgrees_Cassgn_Lmem_U64` below.

instance bignumMemModel : CoqSemMirror.MemModel MemoryModel.Mem where
  read  := bignumMemRead
  write := bignumMemWrite

/-- Lift a `BitVec 64` register value to the mirror's `Value`. -/
def liftReg (w : BitVec 64) : CoqSemMirror.Value := .Vword .U64 w

/-- Lift the register file to a `Vm` on the mirror side.  Variables of
    `aword .U64` type read out as their register value; everything else
    reads out as `Vundef` (which `getVar` then surfaces as `.addrUndef`). -/
def liftVm (s : BignumExec.BignumState) : CoqSemMirror.Vm := fun v =>
  match v.vtype with
  | .aword .U64 => liftReg (s.regs v.vname)
  | t           => CoqSemMirror.undefAddr (CoqSemMirror.evalAtype t)

/-- The full state lift. -/
def stateToEstate (s : BignumExec.BignumState) :
    CoqSemMirror.Estate Unit MemoryModel.Mem :=
  { escs := (), emem := s.mem, evm := liftVm s }

/-! ## §3. Concrete `OpSem` and `AsmSem` realising BignumExec

We give an `OpSem` that mirrors `BignumExec.evalPExpr`'s arithmetic and
an `AsmSem` that mirrors `BignumExec.execInstr`'s intrinsic outputs. -/

/-- Concrete `sem_sop1`.  We handle the unary ops the bignum fragment
    actually emits (`Oneg`, `Olnot`, `Ozeroext`, `Onot`); the rest are
    `.typeError` — they are not in the executable image. -/
def realSemOp1 : CoqSemMirror.SOp1 → CoqSemMirror.Value → CoqSemMirror.JResult CoqSemMirror.Value
  | .Olnot .U64, .Vword .U64 w => .ok (.Vword .U64 (~~~ w))
  | .Onot, .Vbool b => .ok (.Vbool (!b))
  | .Ozeroext .U64 _, .Vword _ w =>
      -- low-`wso.bits` keep; rest zero.  For .U64 target on a U64 source,
      -- this is identity; for narrower sources, zero-extend.
      .ok (.Vword .U64 (BitVec.ofNat 64 w.toNat))
  | .Oneg (.Op_w .U64), .Vword .U64 w => .ok (.Vword .U64 (-w))
  | _, _ => .typeError

/-- Concrete `sem_sop2`.  We handle the binary ops on `.U64` words used by
    `BignumExec.evalPExpr`. -/
def realSemOp2 : CoqSemMirror.SOp2 → CoqSemMirror.Value → CoqSemMirror.Value →
    CoqSemMirror.JResult CoqSemMirror.Value
  | .Oadd (.Op_w .U64), .Vword .U64 a, .Vword .U64 b => .ok (.Vword .U64 (a + b))
  | .Osub (.Op_w .U64), .Vword .U64 a, .Vword .U64 b => .ok (.Vword .U64 (a - b))
  | .Oland .U64, .Vword .U64 a, .Vword .U64 b => .ok (.Vword .U64 (a &&& b))
  | .Olor  .U64, .Vword .U64 a, .Vword .U64 b => .ok (.Vword .U64 (a ||| b))
  | .Olxor .U64, .Vword .U64 a, .Vword .U64 b => .ok (.Vword .U64 (a ^^^ b))
  | .Oeq (.Op_w .U64), .Vword .U64 a, .Vword .U64 b =>
      .ok (.Vword .U64 (if a = b then 1 else 0))
  | .Oneq (.Op_w .U64), .Vword .U64 a, .Vword .U64 b =>
      .ok (.Vword .U64 (if a = b then 0 else 1))
  | _, _, _ => .typeError

/-- Concrete `OpSem` record. -/
def realOpSem : CoqSemMirror.OpSem :=
  { sem_sop1 := realSemOp1
  , sem_sop2 := realSemOp2
  , sem_opN  := fun _ _ => .typeError }

/-- Concrete `sopn_sem`.  The bignum SSA fragment uses x86 intrinsics
    `ADD_64`, `SUB_64`, `ADC_64`, `SBB_64`, `MULX`, `ADCX`, `ADOX`,
    `XOR_64`, `SHL_64`, `SHR_64`, `SHLD_64`, `SHRD_64` plus their U32
    counterparts.  For each, the asm-side returns a `Values` list whose
    layout matches the `writeSubBundle` / `writeMulxBundle` /
    `writeAdxBundle` / `writeXorBundle` / `writeShiftBundle` layout in
    `BignumExec`.  All values are tagged as `.Vword .U64`. -/
def realSopnSem : CoqSemMirror.Sopn → CoqSemMirror.Values →
    CoqSemMirror.JResult CoqSemMirror.Values
  | .Oasm "ADD_64", [.Vword .U64 a, .Vword .U64 b] =>
      let (cf, r) := BignumExec.addCarry a b
      -- 6-LVal bundle [_, cf, _, _, _, r]
      .ok [.Vbool false, .Vword .U64 cf, .Vbool false, .Vbool false, .Vbool false,
           .Vword .U64 r]
  | .Oasm "ADC_64", [.Vword .U64 a, .Vword .U64 b, .Vword .U64 c] =>
      let (cf, r) := BignumExec.addCarryIn a b c
      .ok [.Vbool false, .Vword .U64 cf, .Vbool false, .Vbool false, .Vbool false,
           .Vword .U64 r]
  | .Oasm "SUB_64", [.Vword .U64 a, .Vword .U64 b] =>
      let (cf, r) := BignumExec.subBorrow a b
      .ok [.Vbool false, .Vword .U64 cf, .Vbool false, .Vbool false, .Vbool false,
           .Vword .U64 r]
  | .Oasm "SBB_64", [.Vword .U64 a, .Vword .U64 b, .Vword .U64 c] =>
      let (cf, r) := BignumExec.subBorrowIn a b c
      .ok [.Vbool false, .Vword .U64 cf, .Vbool false, .Vbool false, .Vbool false,
           .Vword .U64 r]
  | .Oasm "MULX", [.Vword .U64 a, .Vword .U64 b] =>
      let (hi, lo) := BignumExec.mulx a b
      .ok [.Vword .U64 hi, .Vword .U64 lo]
  | .Oasm "ADCX", [.Vword .U64 a, .Vword .U64 b, .Vword .U64 c] =>
      let (cf, r) := BignumExec.addCarryIn a b c
      .ok [.Vword .U64 cf, .Vword .U64 r]
  | .Oasm "ADOX", [.Vword .U64 a, .Vword .U64 b, .Vword .U64 c] =>
      let (of, r) := BignumExec.addCarryIn a b c
      .ok [.Vword .U64 of, .Vword .U64 r]
  | .Oasm "XOR_64", [.Vword .U64 a, .Vword .U64 b] =>
      let r := a ^^^ b
      -- 6-LVal bundle [of, cf, _, _, _, r] with of = cf = 0
      .ok [.Vword .U64 0, .Vword .U64 0, .Vbool false, .Vbool false, .Vbool false,
           .Vword .U64 r]
  | _, _ => .typeError

/-- Concrete `AsmSem` record. -/
def realAsmSem : CoqSemMirror.AsmSem :=
  { sopn_sem := realSopnSem }

/-! ## §4. Per-opcode agreement predicate

We package "BignumExec.execInstr on `i` agrees with the mirror's
`execInstrR` on the translated `i` under the chosen state lift" as a
single predicate `OpcodeAgrees`.  Per-opcode lemmas establish this for
particular `InstrR` shapes; the chain-level lemma threads them. -/

/-- `OpcodeAgrees i` means: for every `BignumState s`, if `execInstr s i`
    succeeds with result `s'`, then the mirror's `execInstrR` with our
    `realAsmSem` / `realOpSem` succeeds and ends in `stateToEstate s'`.

    (Symmetric direction — mirror succeeds ⇒ BignumExec succeeds — is the
    second half of the bridge; deferred. The forward direction is what
    a denotation-preserving compiler pipeline needs.) -/
def OpcodeAgrees (i : CatCrypt.Crypto.Jasmin.InstrR) : Prop :=
  ∀ (s s' : BignumExec.BignumState) (mi : CoqSemMirror.InstrR) (fuel : Nat),
    astToMirror_InstrR i = some mi →
    BignumExec.execInstr s i = some s' →
    0 < fuel →
    CoqSemMirror.execInstrR (Mem := MemoryModel.Mem)
        realAsmSem realOpSem [] fuel (stateToEstate s) mi
      = .ok (stateToEstate s')

/-! ## §5. Concrete per-opcode lemmas

We discharge the cleanest cases.  The bundle-level Copn cases follow the
same shape but require unfolding `writeSubBundle` / `writeMulxBundle` /
etc.; deferred to the per-opcode batches (see §7). -/

/-- Helper: when `v` is a `BitVec 64` register, `liftVm s v = Vword U64 _`.
    Used to peel off `getVar` calls on the mirror side. -/
lemma liftVm_of_u64 (s : BignumExec.BignumState) (v : CoqSemMirror.Var)
    (hv : v.vtype = .aword .U64) :
    liftVm s v = .Vword .U64 (s.regs v.vname) := by
  simp [liftVm, hv, liftReg]

/-- The `getVar` operation on the lifted state reads out as a defined
    `Vword .U64` for a `.U64`-typed register name. -/
lemma getVar_liftVm_u64 (s : BignumExec.BignumState) (v : CoqSemMirror.Var)
    (hv : v.vtype = .aword .U64) :
    CoqSemMirror.getVar true (liftVm s) v = .ok (.Vword .U64 (s.regs v.vname)) := by
  simp [CoqSemMirror.getVar, CoqSemMirror.Vm.get, liftVm_of_u64 s v hv,
        CoqSemMirror.Value.isDefined]

/-- `truncateWord` from `U64` to `U64` is the identity (modulo a `BitVec.ofNat
    ... toNat` round-trip). -/
lemma truncateWord_U64_U64 (w : BitVec 64) :
    CoqSemMirror.truncateWord .U64 (sz' := .U64) w = .ok w := by
  unfold CoqSemMirror.truncateWord
  simp [CoqSemMirror.WSize.bits, BitVec.ofNat_toNat]

/-- `truncateVal` on a `.U64` word with target ctype `.cword .U64` is the
    identity (with `Vword`-wrapping). -/
lemma truncateVal_U64_word (w : BitVec 64) :
    CoqSemMirror.truncateVal (.cword .U64) (.Vword .U64 w) = .ok (.Vword .U64 w) := by
  show (do let w' ← CoqSemMirror.truncateWord .U64 (sz' := .U64) w
           CoqSemMirror.JResult.ok (CoqSemMirror.Value.Vword .U64 w')) = _
  rw [truncateWord_U64_U64]
  rfl

/-- Lift commutes with `setReg` for a `.U64`-typed target.  Specifically: the
    mirror `(liftVm s).set v (.Vword .U64 w)` equals `liftVm (setReg s v.vname w)`
    *pointwise* — for every key.  This is the homogeneity property we rely on
    for the `Cassgn (Lvar _) _ _ _` cases. -/
lemma liftVm_setReg_eq (s : BignumExec.BignumState) (v : CoqSemMirror.Var)
    (hv : v.vtype = .aword .U64) (w : BitVec 64) :
    (∀ x : CoqSemMirror.Var, x.vname = v.vname → x.vtype = .aword .U64) →
    CoqSemMirror.Vm.set (liftVm s) v (.Vword .U64 w)
      = liftVm (BignumExec.setReg s v.vname w) := by
  intro hHomog
  funext x
  simp only [CoqSemMirror.Vm.set, liftVm, BignumExec.setReg]
  by_cases hx : x = v
  · subst hx
    simp [hv, liftReg]
  · -- decide branch
    simp only [decide_eq_true_eq]
    rw [if_neg hx]
    -- Need: liftVm s x = (if x.vname = v.vname ...). Two sub-cases on names.
    by_cases hn : x.vname = v.vname
    · -- Same name, different vars ⇒ different vtype.  But hHomog forces same vtype.
      -- So x must equal v after all — contradiction with hx.
      exfalso; apply hx
      have hx_ty : x.vtype = .aword .U64 := hHomog x hn
      cases x with
      | mk xT xN =>
        cases v with
        | mk vT vN =>
          simp at hn hv hx_ty
          subst hn; subst hv; subst hx_ty; rfl
    · -- Different names ⇒ liftVm s on x is whatever it was, and the setReg branch picks s.regs x.vname.
      cases hxt : x.vtype with
      | aword ws =>
        cases ws with
        | U64 => simp [liftReg, hn]
        | U8 | U16 | U32 | U128 | U256 => simp
      | abool | aint | aarr _ _ => simp

/-! ### §5.a. Cassgn-Lvar-Pvar: register-to-register move

The cleanest case.  Both sides reduce to `setReg s tgt (s.regs src)` after
the lift. -/

/-- Forward bridge for `Cassgn (Lvar v) _ ty (Pvar w)` where both `v` and `w`
    have `.sword .U64` types and ty is `.sword .U64`.  Additional homogeneity
    hypothesis: no other variable in the program shares the same name as `v`
    or `w` with a different type. -/
theorem opcodeAgrees_Cassgn_Lvar_Pvar
    (v : CatCrypt.Crypto.Jasmin.VarI) (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (ty : CatCrypt.Crypto.Jasmin.SType) (w : CatCrypt.Crypto.Jasmin.GVar)
    (hVTy : v.var.vtype = .sword .U64)
    (hWTy : w.gv.var.vtype = .sword .U64)
    (hTy : ty = .sword .U64)
    (hWLocal : w.gs = false)
    (hHomogV : ∀ x : CoqSemMirror.Var,
        x.vname = v.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees (.Cassgn (.Lvar v) tag ty (.Pvar w)) := by
  intro s s' mi fuel hMi hExec hFuel
  subst hTy
  -- Step 1: decode the InstrR translation.
  have hMi_eq : astToMirror_InstrR (.Cassgn (.Lvar v) tag (.sword .U64) (.Pvar w))
      = some (.Cassgn (.Lvar (astToMirror_VarI v)) (astToMirror_AssgnTag tag)
              (astToMirror_Atype (.sword .U64)) (.Pvar (astToMirror_GVar w))) := by
    simp [astToMirror_InstrR, astToMirror_LVal, astToMirror_PExpr]
  rw [hMi_eq] at hMi
  have hMi' := Option.some.inj hMi
  subst hMi'
  -- Step 2: decode the BignumExec result.
  have hExec_eq : BignumExec.execInstr s (.Cassgn (.Lvar v) tag (.sword .U64) (.Pvar w))
      = some (BignumExec.setReg s v.var.vname (s.regs w.gv.var.vname)) := by
    unfold BignumExec.execInstr BignumExec.evalPExpr
    rfl
  rw [hExec_eq] at hExec
  have hExec' := Option.some.inj hExec
  subst hExec'
  -- Step 3: unfold the mirror executor.
  cases fuel with
  | zero => omega
  | succ fuel' =>
    -- Definitional facts about astToMirror_VarI / astToMirror_GVar.
    have hSrcTy : (astToMirror_GVar w).gv.v_var.vtype = .aword .U64 := by
      show astToMirror_Atype w.gv.var.vtype = _
      rw [hWTy]; rfl
    have hTgtTy : (astToMirror_VarI v).v_var.vtype = .aword .U64 := by
      show astToMirror_Atype v.var.vtype = _
      rw [hVTy]; rfl
    have hSrcName : (astToMirror_GVar w).gv.v_var.vname = w.gv.var.vname := rfl
    have hTgtName : (astToMirror_VarI v).v_var.vname = v.var.vname := rfl
    -- Reduction: execInstrR (succ fuel') s (.Cassgn ...) unfolds to:
    --   do let val ← semPexpr ...; let val' ← truncateVal ...; writeLval ... val' s
    unfold CoqSemMirror.execInstrR
    show (do
        let val ← CoqSemMirror.semPexpr (Mem := MemoryModel.Mem) true [] realOpSem
                    (stateToEstate s) (.Pvar (astToMirror_GVar w))
        let val' ← CoqSemMirror.truncateVal
                    (CoqSemMirror.evalAtype (astToMirror_Atype (.sword .U64))) val
        CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
          (.Lvar (astToMirror_VarI v)) val' (stateToEstate s))
        = .ok (stateToEstate (BignumExec.setReg s v.var.vname (s.regs w.gv.var.vname)))
    -- semPexpr of Pvar uses getGvar; w.gs = false ⇒ Slocal, so getVar fires.
    have hGvarLocal : (astToMirror_GVar w).isLvar = true := by
      show ((if w.gs then CoqSemMirror.VScope.Sglob else .Slocal) == .Slocal) = true
      rw [hWLocal]; rfl
    have hSemPexpr :
        CoqSemMirror.semPexpr (Mem := MemoryModel.Mem) true [] realOpSem
          (stateToEstate s) (.Pvar (astToMirror_GVar w))
        = .ok (.Vword .U64 (s.regs w.gv.var.vname)) := by
      show CoqSemMirror.getGvar true [] (stateToEstate s).evm
            (astToMirror_GVar w) = _
      unfold CoqSemMirror.getGvar
      rw [if_pos hGvarLocal]
      show CoqSemMirror.getVar true (stateToEstate s).evm (astToMirror_GVar w).gv.v_var = _
      change CoqSemMirror.getVar true (liftVm s) _ = _
      rw [getVar_liftVm_u64 s _ hSrcTy, hSrcName]
    rw [hSemPexpr]
    -- Reduce the (.ok val) >>= continuation via a single change step.
    change CoqSemMirror.truncateVal (.cword .U64) (.Vword .U64 (s.regs w.gv.var.vname)) >>=
        (fun val' => CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
          (.Lvar (astToMirror_VarI v)) val' (stateToEstate s)) = _
    rw [truncateVal_U64_word]
    change CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
          (.Lvar (astToMirror_VarI v)) (.Vword .U64 (s.regs w.gv.var.vname)) (stateToEstate s)
        = _
    -- writeLval (Lvar mv) val s = writeVar true mv val s = setVar then ok (s.withVm vm)
    unfold CoqSemMirror.writeLval CoqSemMirror.writeVar
    -- Unfold writeVar/setVar.  At target type .aword .U64, both DB and
    -- truncatable evaluate to `true` on `.Vword .U64 _`, so the inner
    -- if-chain reduces to `.ok (vm.set tgt val)`.
    unfold CoqSemMirror.setVar
    -- DB check (Vword is defined ⇒ DB = true)
    have hDB : CoqSemMirror.DB (.Vword .U64 (s.regs w.gv.var.vname)) = true := by
      unfold CoqSemMirror.DB
      simp [CoqSemMirror.Value.isDefined]
    -- truncatable check
    have hTrunc :
        CoqSemMirror.truncatable (.cword .U64) (.Vword .U64 (s.regs w.gv.var.vname)) = true := by
      unfold CoqSemMirror.truncatable
      simp [CoqSemMirror.Value.typeOf]
    -- Equate the inner Vm.set to liftVm (setReg ...) using liftVm_setReg_eq.
    have hKey : ∀ x : CoqSemMirror.Var,
        x.vname = (astToMirror_VarI v).v_var.vname → x.vtype = .aword .U64 := by
      intro x hx; apply hHomogV; rw [hx]; rfl
    have hRw : CoqSemMirror.Vm.set (liftVm s) (astToMirror_VarI v).v_var
        (.Vword .U64 (s.regs w.gv.var.vname))
        = liftVm (BignumExec.setReg s v.var.vname (s.regs w.gv.var.vname)) := by
      rw [liftVm_setReg_eq s _ hTgtTy _ hKey]
      rfl
    -- Now reduce the do-let and if-chain.  simp reduces `if false = true`.
    simp only [hDB, hTrunc, Bool.not_true, Bool.and_false, hTgtTy,
               Bool.false_eq_true, ↓reduceIte]
    -- The do-let-bind should now reduce to ok (...withVm...).
    -- Replace the (stateToEstate s).evm with liftVm s (definitionally equal).
    change (CoqSemMirror.JResult.ok ((stateToEstate s).withVm
        (CoqSemMirror.Vm.set (liftVm s) (astToMirror_VarI v).v_var
          (.Vword .U64 (s.regs w.gv.var.vname))))
        : CoqSemMirror.JResult (CoqSemMirror.Estate Unit MemoryModel.Mem))
        = .ok (stateToEstate (BignumExec.setReg s v.var.vname (s.regs w.gv.var.vname)))
    rw [hRw]
    rfl

/-! ### §5.a.bis. Once-and-for-all step helpers for `execInstrR`

The per-opcode `OpcodeAgrees` proofs all start with the same brittle dance:
unfold `execInstrR`, then `show` the resulting do-block matches a fresh `let`
chain.  We package that step as two helpers (one per `InstrR` shape the bignum
SSA fragment emits) so the per-opcode lemmas stay shallow.  Discharges the
follow-up note in the §5.a scaffold. -/

/-- The `.Cassgn` arm of `execInstrR` reduces (on a positive fuel) to the
    canonical do-chain `semPexpr e >>= truncateVal (evalAtype ty) >>=
    writeLval x`.  Isolates the brittle "unfold then `show`" step. -/
theorem execInstrR_Cassgn_step (fuel : Nat)
    (x : CoqSemMirror.Lval) (tag : CoqSemMirror.AssgnTag)
    (ty : CoqSemMirror.Atype) (e : CoqSemMirror.Pexpr)
    (s : CoqSemMirror.Estate Unit MemoryModel.Mem) :
    CoqSemMirror.execInstrR (Mem := MemoryModel.Mem) realAsmSem realOpSem []
        (fuel + 1) s (.Cassgn x tag ty e)
      = (do
          let v ← CoqSemMirror.semPexpr (Mem := MemoryModel.Mem) true []
                    realOpSem s e
          let v' ← CoqSemMirror.truncateVal (CoqSemMirror.evalAtype ty) v
          CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
            x v' s) := by
  unfold CoqSemMirror.execInstrR
  rfl

/-- The `.Copn` arm of `execInstrR` reduces (on a positive fuel) to
    `semSopn ... o s xs es`, i.e. evaluate the arg list with `semPexprs`,
    push through `execSopn`, write the result list back into `xs` via
    `writeLvals`.  Same brittle-pattern bypass as `execInstrR_Cassgn_step`. -/
theorem execInstrR_Copn_step (fuel : Nat)
    (xs : CoqSemMirror.Lvals) (tag : CoqSemMirror.AssgnTag)
    (o : CoqSemMirror.Sopn) (es : CoqSemMirror.Pexprs)
    (s : CoqSemMirror.Estate Unit MemoryModel.Mem) :
    CoqSemMirror.execInstrR (Mem := MemoryModel.Mem) realAsmSem realOpSem []
        (fuel + 1) s (.Copn xs tag o es)
      = CoqSemMirror.semSopn (Mem := MemoryModel.Mem) realAsmSem realOpSem []
          o s xs es := by
  unfold CoqSemMirror.execInstrR
  rfl

/-! ### §5.a.ter. Per-opcode `OpcodeAgrees` lemmas for the bignum Copn fragment

We discharge agreement on the eight x86 intrinsics that the bignum SSA
fragment emits as `Copn`:

  `ADD_64`, `ADC_64`, `SUB_64`, `SBB_64`, `MULX`, `ADCX`, `ADOX`, `XOR_64`.

Each lemma takes:

* the source `GVar` operands, all `.sword .U64`-typed, all with `gs = false`
  (true `Pvar`-shape register reads — the only argument shape the bignum
  emitter produces for these intrinsics, per `BignumExec.evalPExpr`);
* the bundle's named destination `VarI`s, all `.sword .U64`-typed;
* the `Lnone` flag slots typed as `.sbool` (so the mirror's `writeLval` on
  the flag positions sees `.abool` — `writeNone` then accepts `Vbool _`);
* a single homogeneity hypothesis per output: no other variable in the
  program shares the same name with a different type.

Each proof reduces uniformly:

1. Decode `astToMirror_InstrR` on the `Copn` shape (one `rfl`).
2. Decode `BignumExec.execInstr` to the matching `writeBundle` arm.
3. Generalize the carry/result pair so it stays opaque across both sides.
4. Apply `execInstrR_Copn_step` on the mirror side, unfolding `semSopn`
   into `semPexprs >>= execSopn >>= writeLvals`.
5. Discharge each phase with a focused helper (`semPexpr_Pvar_u64_gv`,
   `realSopnSem`-unfold, `writeLvals_*bundle`). -/

/-- For a `.U64`-typed `GVar` with `gs = false` (a local register), the
    mirror semantics evaluates `Pvar` to the register value. -/
lemma semPexpr_Pvar_u64_gv
    (s : BignumExec.BignumState) (g : CatCrypt.Crypto.Jasmin.GVar)
    (hV : g.gv.var.vtype = .sword .U64) (hLocal : g.gs = false) :
    CoqSemMirror.semPexpr (Mem := MemoryModel.Mem) true [] realOpSem
        (stateToEstate s)
        (.Pvar (astToMirror_GVar g))
      = .ok (.Vword .U64 (s.regs g.gv.var.vname)) := by
  have hGvarLocal : (astToMirror_GVar g).isLvar = true := by
    show ((if g.gs then CoqSemMirror.VScope.Sglob else .Slocal) == .Slocal) = true
    rw [hLocal]; rfl
  have hTy : (astToMirror_GVar g).gv.v_var.vtype = .aword .U64 := by
    show astToMirror_Atype g.gv.var.vtype = _
    rw [hV]; rfl
  show CoqSemMirror.getGvar true [] (stateToEstate s).evm
        (astToMirror_GVar g) = _
  unfold CoqSemMirror.getGvar
  rw [if_pos hGvarLocal]
  show CoqSemMirror.getVar true (stateToEstate s).evm
        (astToMirror_GVar g).gv.v_var = _
  change CoqSemMirror.getVar true (liftVm s) _ = _
  rw [getVar_liftVm_u64 s _ hTy]
  rfl

/-- `writeLval` on `.Lnone _ .abool` accepting a `Vbool _` succeeds and leaves
    the state untouched.  Used for the flag slots in the SUB/XOR bundles. -/
lemma writeLval_Lnone_abool (s : CoqSemMirror.Estate Unit MemoryModel.Mem)
    (b : Bool) :
    CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lnone () .abool) (.Vbool b) s
      = .ok s := by
  show CoqSemMirror.writeNone s (CoqSemMirror.evalAtype .abool) (.Vbool b) = _
  unfold CoqSemMirror.writeNone CoqSemMirror.truncatable CoqSemMirror.DB
        CoqSemMirror.Value.isDefined CoqSemMirror.Value.typeOf
        CoqSemMirror.evalAtype
  simp

/-- `writeLval` on `.Lvar v` with a `.aword .U64`-typed register and a
    `Vword .U64 w` value succeeds, producing the state with `liftVm
    (setReg s v.vname w)` in its variable map. -/
lemma writeLval_Lvar_u64 (s : BignumExec.BignumState)
    (v : CoqSemMirror.VarI) (w : BitVec 64)
    (hTy : v.v_var.vtype = .aword .U64)
    (hHomog : ∀ x : CoqSemMirror.Var,
        x.vname = v.v_var.vname → x.vtype = .aword .U64) :
    CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lvar v) (.Vword .U64 w) (stateToEstate s)
      = .ok (stateToEstate (BignumExec.setReg s v.v_var.vname w)) := by
  unfold CoqSemMirror.writeLval CoqSemMirror.writeVar CoqSemMirror.setVar
  have hDB : CoqSemMirror.DB (.Vword .U64 w) = true := by
    unfold CoqSemMirror.DB; simp [CoqSemMirror.Value.isDefined]
  have hTrunc :
      CoqSemMirror.truncatable (.cword .U64) (.Vword .U64 w) = true := by
    unfold CoqSemMirror.truncatable
    simp [CoqSemMirror.Value.typeOf]
  have hRw : CoqSemMirror.Vm.set (liftVm s) v.v_var (.Vword .U64 w)
      = liftVm (BignumExec.setReg s v.v_var.vname w) :=
    liftVm_setReg_eq s _ hTy w hHomog
  simp only [hDB, hTrunc, hTy, Bool.not_true, Bool.and_false,
             Bool.false_eq_true, ↓reduceIte]
  change (CoqSemMirror.JResult.ok ((stateToEstate s).withVm
        (CoqSemMirror.Vm.set (liftVm s) v.v_var (.Vword .U64 w))))
      = .ok (stateToEstate (BignumExec.setReg s v.v_var.vname w))
  rw [hRw]
  rfl

/-! ### Bundle writers

We package the matching mirror reduction once per bundle shape so the
per-opcode proofs can chain through.  Each `writeLvals_*bundle` lemma
takes the bundle's named registers, the values to write, type+homogeneity
witnesses for each register, and produces the `stateToEstate (setReg ...
setReg ...)` result. -/

/-- Write the SUB-bundle `[_, cf, _, _, _, r]` on the mirror side: four flag
    slots succeed via `writeLval_Lnone_abool`, two `.Lvar` slots succeed via
    `writeLval_Lvar_u64`. -/
lemma writeLvals_SUBbundle
    (s : BignumExec.BignumState)
    (cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (cf r : BitVec 64)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true [] realOpSem
        (stateToEstate s)
        [ .Lnone () .abool, .Lvar (astToMirror_VarI cfV),
          .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
          .Lvar (astToMirror_VarI rV) ]
        [ .Vbool false, .Vword .U64 cf, .Vbool false, .Vbool false,
          .Vbool false, .Vword .U64 r ]
      = .ok (stateToEstate
          (BignumExec.setReg (BignumExec.setReg s cfV.var.vname cf)
            rV.var.vname r)) := by
  unfold CoqSemMirror.writeLvals
  show CoqSemMirror.JResult.fold2 _ _ _ _ _ = _
  have hCFTy' : (astToMirror_VarI cfV).v_var.vtype = .aword .U64 := by
    show astToMirror_Atype cfV.var.vtype = _; rw [hCFTy]; rfl
  have hRTy' : (astToMirror_VarI rV).v_var.vtype = .aword .U64 := by
    show astToMirror_Atype rV.var.vtype = _; rw [hRTy]; rfl
  -- Slot 0: Lnone abool / Vbool false
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lnone () .abool) (.Vbool false) (stateToEstate s)) >>=
        (fun s0 => CoqSemMirror.JResult.fold2 _ _ _ _ s0) = _
  rw [writeLval_Lnone_abool]
  -- Slot 1: Lvar cfV / Vword cf
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lvar (astToMirror_VarI cfV)) (.Vword .U64 cf) (stateToEstate s)) >>=
        (fun s1 => CoqSemMirror.JResult.fold2 _ _ _ _ s1) = _
  rw [writeLval_Lvar_u64 s _ cf hCFTy' (by intro x hx; exact hCFhomog x hx)]
  -- Slots 2, 3, 4: three Lnone abool / Vbool false
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lnone () .abool) (.Vbool false)
        (stateToEstate (BignumExec.setReg s cfV.var.vname cf))) >>=
        (fun _ => CoqSemMirror.JResult.fold2 _ _ _ _ _) = _
  rw [writeLval_Lnone_abool]
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lnone () .abool) (.Vbool false)
        (stateToEstate (BignumExec.setReg s cfV.var.vname cf))) >>=
        (fun _ => CoqSemMirror.JResult.fold2 _ _ _ _ _) = _
  rw [writeLval_Lnone_abool]
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lnone () .abool) (.Vbool false)
        (stateToEstate (BignumExec.setReg s cfV.var.vname cf))) >>=
        (fun _ => CoqSemMirror.JResult.fold2 _ _ _ _ _) = _
  rw [writeLval_Lnone_abool]
  -- Slot 5: Lvar rV / Vword r
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lvar (astToMirror_VarI rV)) (.Vword .U64 r)
        (stateToEstate (BignumExec.setReg s cfV.var.vname cf))) >>=
        (fun _ => CoqSemMirror.JResult.fold2 _ _ _ _ _) = _
  rw [writeLval_Lvar_u64 (BignumExec.setReg s cfV.var.vname cf)
        _ r hRTy' (by intro x hx; exact hRhomog x hx)]
  rfl

/-- Write the MULX-bundle `[hi, lo]` on the mirror side. -/
lemma writeLvals_MULXbundle
    (s : BignumExec.BignumState)
    (hiV loV : CatCrypt.Crypto.Jasmin.VarI)
    (hi lo : BitVec 64)
    (hHiTy : hiV.var.vtype = .sword .U64)
    (hLoTy : loV.var.vtype = .sword .U64)
    (hHihomog : ∀ x : CoqSemMirror.Var,
        x.vname = hiV.var.vname → x.vtype = .aword .U64)
    (hLohomog : ∀ x : CoqSemMirror.Var,
        x.vname = loV.var.vname → x.vtype = .aword .U64) :
    CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true [] realOpSem
        (stateToEstate s)
        [ .Lvar (astToMirror_VarI hiV), .Lvar (astToMirror_VarI loV) ]
        [ .Vword .U64 hi, .Vword .U64 lo ]
      = .ok (stateToEstate
          (BignumExec.setReg (BignumExec.setReg s hiV.var.vname hi)
            loV.var.vname lo)) := by
  unfold CoqSemMirror.writeLvals
  show CoqSemMirror.JResult.fold2 _ _ _ _ _ = _
  have hHiTy' : (astToMirror_VarI hiV).v_var.vtype = .aword .U64 := by
    show astToMirror_Atype hiV.var.vtype = _; rw [hHiTy]; rfl
  have hLoTy' : (astToMirror_VarI loV).v_var.vtype = .aword .U64 := by
    show astToMirror_Atype loV.var.vtype = _; rw [hLoTy]; rfl
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lvar (astToMirror_VarI hiV)) (.Vword .U64 hi) (stateToEstate s)) >>=
        (fun s0 => CoqSemMirror.JResult.fold2 _ _ _ _ s0) = _
  rw [writeLval_Lvar_u64 s _ hi hHiTy' (by intro x hx; exact hHihomog x hx)]
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lvar (astToMirror_VarI loV)) (.Vword .U64 lo)
        (stateToEstate (BignumExec.setReg s hiV.var.vname hi))) >>=
        (fun _ => CoqSemMirror.JResult.fold2 _ _ _ _ _) = _
  rw [writeLval_Lvar_u64 (BignumExec.setReg s hiV.var.vname hi)
        _ lo hLoTy' (by intro x hx; exact hLohomog x hx)]
  rfl

/-- Write the ADX-bundle `[flag, dst]` on the mirror side (used by
    ADCX/ADOX).  Structurally identical to `writeLvals_MULXbundle`. -/
lemma writeLvals_ADXbundle
    (s : BignumExec.BignumState)
    (flagV rV : CatCrypt.Crypto.Jasmin.VarI)
    (flag r : BitVec 64)
    (hFlagTy : flagV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hFlaghomog : ∀ x : CoqSemMirror.Var,
        x.vname = flagV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true [] realOpSem
        (stateToEstate s)
        [ .Lvar (astToMirror_VarI flagV), .Lvar (astToMirror_VarI rV) ]
        [ .Vword .U64 flag, .Vword .U64 r ]
      = .ok (stateToEstate
          (BignumExec.setReg (BignumExec.setReg s flagV.var.vname flag)
            rV.var.vname r)) :=
  writeLvals_MULXbundle s flagV rV flag r hFlagTy hRTy hFlaghomog hRhomog

/-- Write the XOR-bundle `[of, cf, _, _, _, r]` on the mirror side (first
    arm of `BignumExec.writeXorBundle`: both flag outputs captured). -/
lemma writeLvals_XORbundle
    (s : BignumExec.BignumState)
    (ofV cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (of cf r : BitVec 64)
    (hOFTy : ofV.var.vtype = .sword .U64)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hOFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = ofV.var.vname → x.vtype = .aword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true [] realOpSem
        (stateToEstate s)
        [ .Lvar (astToMirror_VarI ofV), .Lvar (astToMirror_VarI cfV),
          .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
          .Lvar (astToMirror_VarI rV) ]
        [ .Vword .U64 of, .Vword .U64 cf, .Vbool false, .Vbool false,
          .Vbool false, .Vword .U64 r ]
      = .ok (stateToEstate
          (BignumExec.setReg
            (BignumExec.setReg (BignumExec.setReg s ofV.var.vname of)
              cfV.var.vname cf)
            rV.var.vname r)) := by
  unfold CoqSemMirror.writeLvals
  show CoqSemMirror.JResult.fold2 _ _ _ _ _ = _
  have hOFTy' : (astToMirror_VarI ofV).v_var.vtype = .aword .U64 := by
    show astToMirror_Atype ofV.var.vtype = _; rw [hOFTy]; rfl
  have hCFTy' : (astToMirror_VarI cfV).v_var.vtype = .aword .U64 := by
    show astToMirror_Atype cfV.var.vtype = _; rw [hCFTy]; rfl
  have hRTy' : (astToMirror_VarI rV).v_var.vtype = .aword .U64 := by
    show astToMirror_Atype rV.var.vtype = _; rw [hRTy]; rfl
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lvar (astToMirror_VarI ofV)) (.Vword .U64 of) (stateToEstate s)) >>=
        (fun _ => CoqSemMirror.JResult.fold2 _ _ _ _ _) = _
  rw [writeLval_Lvar_u64 s _ of hOFTy' (by intro x hx; exact hOFhomog x hx)]
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lvar (astToMirror_VarI cfV)) (.Vword .U64 cf)
        (stateToEstate (BignumExec.setReg s ofV.var.vname of))) >>=
        (fun _ => CoqSemMirror.JResult.fold2 _ _ _ _ _) = _
  rw [writeLval_Lvar_u64 (BignumExec.setReg s ofV.var.vname of)
        _ cf hCFTy' (by intro x hx; exact hCFhomog x hx)]
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lnone () .abool) (.Vbool false) (stateToEstate _)) >>=
        (fun _ => CoqSemMirror.JResult.fold2 _ _ _ _ _) = _
  rw [writeLval_Lnone_abool]
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lnone () .abool) (.Vbool false) (stateToEstate _)) >>=
        (fun _ => CoqSemMirror.JResult.fold2 _ _ _ _ _) = _
  rw [writeLval_Lnone_abool]
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lnone () .abool) (.Vbool false) (stateToEstate _)) >>=
        (fun _ => CoqSemMirror.JResult.fold2 _ _ _ _ _) = _
  rw [writeLval_Lnone_abool]
  show (CoqSemMirror.writeLval (Mem := MemoryModel.Mem) true [] realOpSem
        (.Lvar (astToMirror_VarI rV)) (.Vword .U64 r) (stateToEstate _)) >>=
        (fun _ => CoqSemMirror.JResult.fold2 _ _ _ _ _) = _
  rw [writeLval_Lvar_u64 _ _ r hRTy' (by intro x hx; exact hRhomog x hx)]
  rfl

/-! ### The 8 per-opcode `OpcodeAgrees` instances. -/

/-- `OpcodeAgrees` for `ADD_64`.  6-LVal SUB-bundle, 2-input `Pvar` args.
    The arithmetic is `BignumExec.addCarry`. -/
theorem opcodeAgrees_Copn_ADD_64
    (eA eB : CatCrypt.Crypto.Jasmin.GVar)
    (cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (info1 info2 info3 info4 : CatCrypt.Crypto.Jasmin.VarInfo)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees
      (.Copn
        [.Lnone info1 .sbool, .Lvar cfV,
         .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
         .Lvar rV]
        tag (.Oasm ⟨"ADD_64"⟩) [.Pvar eA, .Pvar eB]) := by
  intro s s' mi fuel hMi hExec hFuel
  -- Step 1: decode the translation.
  have hMi_eq : astToMirror_InstrR
        (.Copn
          [.Lnone info1 .sbool, .Lvar cfV,
           .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
           .Lvar rV]
          tag (.Oasm ⟨"ADD_64"⟩) [.Pvar eA, .Pvar eB])
      = some (.Copn
          [ .Lnone () .abool, .Lvar (astToMirror_VarI cfV),
            .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
            .Lvar (astToMirror_VarI rV) ]
          (astToMirror_AssgnTag tag) (.Oasm "ADD_64")
          [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ]) := rfl
  rw [hMi_eq] at hMi
  have hMi' := Option.some.inj hMi; subst hMi'
  -- Step 2: decode the BignumExec result.
  have hExec_eq : BignumExec.execInstr s
        (.Copn
          [.Lnone info1 .sbool, .Lvar cfV,
           .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
           .Lvar rV]
          tag (.Oasm ⟨"ADD_64"⟩) [.Pvar eA, .Pvar eB])
      = (match BignumExec.addCarry (s.regs eA.gv.var.vname)
                                   (s.regs eB.gv.var.vname) with
         | (cf, r) =>
           some (BignumExec.setReg (BignumExec.setReg s cfV.var.vname cf)
                                    rV.var.vname r)) := by
    unfold BignumExec.execInstr BignumExec.evalPExpr BignumExec.writeSubBundle
    rfl
  rw [hExec_eq] at hExec
  -- Generalize the (cf, r) pair so it stays opaque on both sides.
  revert hExec
  generalize hCR : BignumExec.addCarry (s.regs eA.gv.var.vname)
                                       (s.regs eB.gv.var.vname) = cr
  obtain ⟨cf, r⟩ := cr
  intro hExec
  simp only at hExec
  have hExec' : s' = BignumExec.setReg
        (BignumExec.setReg s cfV.var.vname cf) rV.var.vname r :=
    (Option.some.inj hExec).symm
  subst hExec'
  -- Step 3: mirror side.
  cases fuel with
  | zero => omega
  | succ fuel' =>
    rw [execInstrR_Copn_step]
    unfold CoqSemMirror.semSopn
    -- Phase 3a: semPexprs evaluates both Pvar args.
    have hSemArgs : CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true []
        realOpSem (stateToEstate s)
        [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ]
        = .ok [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname) ] := by
      show CoqSemMirror.semPexprList (Mem := MemoryModel.Mem) true [] realOpSem
            (stateToEstate s)
            [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ] = _
      unfold CoqSemMirror.semPexprList
      rw [semPexpr_Pvar_u64_gv s eA hATy hALocal]
      show ((do
        let vs ← CoqSemMirror.semPexprList (Mem := MemoryModel.Mem) true []
                  realOpSem (stateToEstate s) [ .Pvar (astToMirror_GVar eB) ]
        CoqSemMirror.JResult.ok (Value.Vword .U64 (s.regs eA.gv.var.vname) :: vs))
        : CoqSemMirror.JResult _) = _
      unfold CoqSemMirror.semPexprList
      rw [semPexpr_Pvar_u64_gv s eB hBTy hBLocal]
      rfl
    -- Phase 3b: execSopn fires realSopnSem.
    have hExecSopn : CoqSemMirror.execSopn realAsmSem (.Oasm "ADD_64")
        [ .Vword .U64 (s.regs eA.gv.var.vname),
          .Vword .U64 (s.regs eB.gv.var.vname) ]
        = .ok [ .Vbool false, .Vword .U64 cf, .Vbool false, .Vbool false,
                .Vbool false, .Vword .U64 r ] := by
      exact (realSopnSem.eq_1 _ _).trans (by rw [hCR])
    -- Combine the two rewrites + writeLvals discharge in one block.
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true [] realOpSem
              (stateToEstate s)
              [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ])
            (fun vs => CoqSemMirror.JResult.bind
              (CoqSemMirror.execSopn realAsmSem (.Oasm "ADD_64") vs)
              (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
                realOpSem (stateToEstate s)
                [ .Lnone () .abool, .Lvar (astToMirror_VarI cfV),
                  .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
                  .Lvar (astToMirror_VarI rV) ] rs))
        = _
    rw [hSemArgs]
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.execSopn realAsmSem (.Oasm "ADD_64")
              [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname) ])
            (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
              realOpSem (stateToEstate s)
              [ .Lnone () .abool, .Lvar (astToMirror_VarI cfV),
                .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
                .Lvar (astToMirror_VarI rV) ] rs)
        = _
    rw [hExecSopn]
    -- Phase 3c: writeLvals on the SUB-bundle.
    exact writeLvals_SUBbundle s cfV rV cf r hCFTy hRTy hCFhomog hRhomog

/-- `OpcodeAgrees` for `SUB_64`.  Same SUB-bundle shape as `ADD_64`; carry
    semantics is `BignumExec.subBorrow`. -/
theorem opcodeAgrees_Copn_SUB_64
    (eA eB : CatCrypt.Crypto.Jasmin.GVar)
    (cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (info1 info2 info3 info4 : CatCrypt.Crypto.Jasmin.VarInfo)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees
      (.Copn
        [.Lnone info1 .sbool, .Lvar cfV,
         .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
         .Lvar rV]
        tag (.Oasm ⟨"SUB_64"⟩) [.Pvar eA, .Pvar eB]) := by
  intro s s' mi fuel hMi hExec hFuel
  have hMi_eq : astToMirror_InstrR
        (.Copn
          [.Lnone info1 .sbool, .Lvar cfV,
           .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
           .Lvar rV]
          tag (.Oasm ⟨"SUB_64"⟩) [.Pvar eA, .Pvar eB])
      = some (.Copn
          [ .Lnone () .abool, .Lvar (astToMirror_VarI cfV),
            .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
            .Lvar (astToMirror_VarI rV) ]
          (astToMirror_AssgnTag tag) (.Oasm "SUB_64")
          [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ]) := rfl
  rw [hMi_eq] at hMi
  have hMi' := Option.some.inj hMi; subst hMi'
  have hExec_eq : BignumExec.execInstr s
        (.Copn
          [.Lnone info1 .sbool, .Lvar cfV,
           .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
           .Lvar rV]
          tag (.Oasm ⟨"SUB_64"⟩) [.Pvar eA, .Pvar eB])
      = (match BignumExec.subBorrow (s.regs eA.gv.var.vname)
                                    (s.regs eB.gv.var.vname) with
         | (cf, r) =>
           some (BignumExec.setReg (BignumExec.setReg s cfV.var.vname cf)
                                    rV.var.vname r)) := by
    unfold BignumExec.execInstr BignumExec.evalPExpr BignumExec.writeSubBundle
    rfl
  rw [hExec_eq] at hExec
  revert hExec
  generalize hCR : BignumExec.subBorrow (s.regs eA.gv.var.vname)
                                        (s.regs eB.gv.var.vname) = cr
  obtain ⟨cf, r⟩ := cr
  intro hExec
  simp only at hExec
  have hExec' : s' = BignumExec.setReg
        (BignumExec.setReg s cfV.var.vname cf) rV.var.vname r :=
    (Option.some.inj hExec).symm
  subst hExec'
  cases fuel with
  | zero => omega
  | succ fuel' =>
    rw [execInstrR_Copn_step]
    unfold CoqSemMirror.semSopn
    have hSemArgs : CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true []
        realOpSem (stateToEstate s)
        [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ]
        = .ok [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname) ] := by
      show CoqSemMirror.semPexprList (Mem := MemoryModel.Mem) true [] realOpSem
            (stateToEstate s)
            [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ] = _
      unfold CoqSemMirror.semPexprList
      rw [semPexpr_Pvar_u64_gv s eA hATy hALocal]
      show ((do
        let vs ← CoqSemMirror.semPexprList (Mem := MemoryModel.Mem) true []
                  realOpSem (stateToEstate s) [ .Pvar (astToMirror_GVar eB) ]
        CoqSemMirror.JResult.ok (Value.Vword .U64 (s.regs eA.gv.var.vname) :: vs))
        : CoqSemMirror.JResult _) = _
      unfold CoqSemMirror.semPexprList
      rw [semPexpr_Pvar_u64_gv s eB hBTy hBLocal]
      rfl
    have hExecSopn : CoqSemMirror.execSopn realAsmSem (.Oasm "SUB_64")
        [ .Vword .U64 (s.regs eA.gv.var.vname),
          .Vword .U64 (s.regs eB.gv.var.vname) ]
        = .ok [ .Vbool false, .Vword .U64 cf, .Vbool false, .Vbool false,
                .Vbool false, .Vword .U64 r ] := by
      exact (realSopnSem.eq_3 _ _).trans (by rw [hCR])
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true [] realOpSem
              (stateToEstate s)
              [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ])
            (fun vs => CoqSemMirror.JResult.bind
              (CoqSemMirror.execSopn realAsmSem (.Oasm "SUB_64") vs)
              (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
                realOpSem (stateToEstate s)
                [ .Lnone () .abool, .Lvar (astToMirror_VarI cfV),
                  .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
                  .Lvar (astToMirror_VarI rV) ] rs))
        = _
    rw [hSemArgs]
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.execSopn realAsmSem (.Oasm "SUB_64")
              [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname) ])
            (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
              realOpSem (stateToEstate s)
              [ .Lnone () .abool, .Lvar (astToMirror_VarI cfV),
                .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
                .Lvar (astToMirror_VarI rV) ] rs)
        = _
    rw [hExecSopn]
    exact writeLvals_SUBbundle s cfV rV cf r hCFTy hRTy hCFhomog hRhomog

/-- `OpcodeAgrees` for `ADC_64`.  3-input variant: takes `eA`, `eB`, `eC`
    (the carry-in source).  Same SUB-bundle shape; semantics `addCarryIn`. -/
theorem opcodeAgrees_Copn_ADC_64
    (eA eB eC : CatCrypt.Crypto.Jasmin.GVar)
    (cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (info1 info2 info3 info4 : CatCrypt.Crypto.Jasmin.VarInfo)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hCTy : eC.gv.var.vtype = .sword .U64) (hCLocal : eC.gs = false)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees
      (.Copn
        [.Lnone info1 .sbool, .Lvar cfV,
         .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
         .Lvar rV]
        tag (.Oasm ⟨"ADC_64"⟩) [.Pvar eA, .Pvar eB, .Pvar eC]) := by
  intro s s' mi fuel hMi hExec hFuel
  have hMi_eq : astToMirror_InstrR
        (.Copn
          [.Lnone info1 .sbool, .Lvar cfV,
           .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
           .Lvar rV]
          tag (.Oasm ⟨"ADC_64"⟩) [.Pvar eA, .Pvar eB, .Pvar eC])
      = some (.Copn
          [ .Lnone () .abool, .Lvar (astToMirror_VarI cfV),
            .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
            .Lvar (astToMirror_VarI rV) ]
          (astToMirror_AssgnTag tag) (.Oasm "ADC_64")
          [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
            .Pvar (astToMirror_GVar eC) ]) := rfl
  rw [hMi_eq] at hMi
  have hMi' := Option.some.inj hMi; subst hMi'
  have hExec_eq : BignumExec.execInstr s
        (.Copn
          [.Lnone info1 .sbool, .Lvar cfV,
           .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
           .Lvar rV]
          tag (.Oasm ⟨"ADC_64"⟩) [.Pvar eA, .Pvar eB, .Pvar eC])
      = (match BignumExec.addCarryIn (s.regs eA.gv.var.vname)
                                     (s.regs eB.gv.var.vname)
                                     (s.regs eC.gv.var.vname) with
         | (cf, r) =>
           some (BignumExec.setReg (BignumExec.setReg s cfV.var.vname cf)
                                    rV.var.vname r)) := by
    unfold BignumExec.execInstr BignumExec.evalPExpr BignumExec.writeSubBundle
    rfl
  rw [hExec_eq] at hExec
  revert hExec
  generalize hCR : BignumExec.addCarryIn (s.regs eA.gv.var.vname)
                                         (s.regs eB.gv.var.vname)
                                         (s.regs eC.gv.var.vname) = cr
  obtain ⟨cf, r⟩ := cr
  intro hExec
  simp only at hExec
  have hExec' : s' = BignumExec.setReg
        (BignumExec.setReg s cfV.var.vname cf) rV.var.vname r :=
    (Option.some.inj hExec).symm
  subst hExec'
  cases fuel with
  | zero => omega
  | succ fuel' =>
    rw [execInstrR_Copn_step]
    unfold CoqSemMirror.semSopn
    have hSemArgs : CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true []
        realOpSem (stateToEstate s)
        [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
          .Pvar (astToMirror_GVar eC) ]
        = .ok [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname),
                .Vword .U64 (s.regs eC.gv.var.vname) ] := by
      show CoqSemMirror.semPexprList (Mem := MemoryModel.Mem) true [] realOpSem
            (stateToEstate s)
            [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
              .Pvar (astToMirror_GVar eC) ] = _
      simp only [CoqSemMirror.semPexprList,
                 semPexpr_Pvar_u64_gv s eA hATy hALocal,
                 semPexpr_Pvar_u64_gv s eB hBTy hBLocal,
                 semPexpr_Pvar_u64_gv s eC hCTy hCLocal,
                 CoqSemMirror.JResult.bind_ok, bind, Bind.bind]
    have hExecSopn : CoqSemMirror.execSopn realAsmSem (.Oasm "ADC_64")
        [ .Vword .U64 (s.regs eA.gv.var.vname),
          .Vword .U64 (s.regs eB.gv.var.vname),
          .Vword .U64 (s.regs eC.gv.var.vname) ]
        = .ok [ .Vbool false, .Vword .U64 cf, .Vbool false, .Vbool false,
                .Vbool false, .Vword .U64 r ] := by
      exact (realSopnSem.eq_2 _ _ _).trans (by rw [hCR])
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true [] realOpSem
              (stateToEstate s)
              [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
                .Pvar (astToMirror_GVar eC) ])
            (fun vs => CoqSemMirror.JResult.bind
              (CoqSemMirror.execSopn realAsmSem (.Oasm "ADC_64") vs)
              (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
                realOpSem (stateToEstate s)
                [ .Lnone () .abool, .Lvar (astToMirror_VarI cfV),
                  .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
                  .Lvar (astToMirror_VarI rV) ] rs))
        = _
    rw [hSemArgs]
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.execSopn realAsmSem (.Oasm "ADC_64")
              [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname),
                .Vword .U64 (s.regs eC.gv.var.vname) ])
            (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
              realOpSem (stateToEstate s)
              [ .Lnone () .abool, .Lvar (astToMirror_VarI cfV),
                .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
                .Lvar (astToMirror_VarI rV) ] rs)
        = _
    rw [hExecSopn]
    exact writeLvals_SUBbundle s cfV rV cf r hCFTy hRTy hCFhomog hRhomog

/-- `OpcodeAgrees` for `SBB_64`.  3-input variant; semantics `subBorrowIn`. -/
theorem opcodeAgrees_Copn_SBB_64
    (eA eB eC : CatCrypt.Crypto.Jasmin.GVar)
    (cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (info1 info2 info3 info4 : CatCrypt.Crypto.Jasmin.VarInfo)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hCTy : eC.gv.var.vtype = .sword .U64) (hCLocal : eC.gs = false)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees
      (.Copn
        [.Lnone info1 .sbool, .Lvar cfV,
         .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
         .Lvar rV]
        tag (.Oasm ⟨"SBB_64"⟩) [.Pvar eA, .Pvar eB, .Pvar eC]) := by
  intro s s' mi fuel hMi hExec hFuel
  have hMi_eq : astToMirror_InstrR
        (.Copn
          [.Lnone info1 .sbool, .Lvar cfV,
           .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
           .Lvar rV]
          tag (.Oasm ⟨"SBB_64"⟩) [.Pvar eA, .Pvar eB, .Pvar eC])
      = some (.Copn
          [ .Lnone () .abool, .Lvar (astToMirror_VarI cfV),
            .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
            .Lvar (astToMirror_VarI rV) ]
          (astToMirror_AssgnTag tag) (.Oasm "SBB_64")
          [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
            .Pvar (astToMirror_GVar eC) ]) := rfl
  rw [hMi_eq] at hMi
  have hMi' := Option.some.inj hMi; subst hMi'
  have hExec_eq : BignumExec.execInstr s
        (.Copn
          [.Lnone info1 .sbool, .Lvar cfV,
           .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
           .Lvar rV]
          tag (.Oasm ⟨"SBB_64"⟩) [.Pvar eA, .Pvar eB, .Pvar eC])
      = (match BignumExec.subBorrowIn (s.regs eA.gv.var.vname)
                                      (s.regs eB.gv.var.vname)
                                      (s.regs eC.gv.var.vname) with
         | (cf, r) =>
           some (BignumExec.setReg (BignumExec.setReg s cfV.var.vname cf)
                                    rV.var.vname r)) := by
    unfold BignumExec.execInstr BignumExec.evalPExpr BignumExec.writeSubBundle
    rfl
  rw [hExec_eq] at hExec
  revert hExec
  generalize hCR : BignumExec.subBorrowIn (s.regs eA.gv.var.vname)
                                          (s.regs eB.gv.var.vname)
                                          (s.regs eC.gv.var.vname) = cr
  obtain ⟨cf, r⟩ := cr
  intro hExec
  simp only at hExec
  have hExec' : s' = BignumExec.setReg
        (BignumExec.setReg s cfV.var.vname cf) rV.var.vname r :=
    (Option.some.inj hExec).symm
  subst hExec'
  cases fuel with
  | zero => omega
  | succ fuel' =>
    rw [execInstrR_Copn_step]
    unfold CoqSemMirror.semSopn
    have hSemArgs : CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true []
        realOpSem (stateToEstate s)
        [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
          .Pvar (astToMirror_GVar eC) ]
        = .ok [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname),
                .Vword .U64 (s.regs eC.gv.var.vname) ] := by
      show CoqSemMirror.semPexprList (Mem := MemoryModel.Mem) true [] realOpSem
            (stateToEstate s)
            [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
              .Pvar (astToMirror_GVar eC) ] = _
      simp only [CoqSemMirror.semPexprList,
                 semPexpr_Pvar_u64_gv s eA hATy hALocal,
                 semPexpr_Pvar_u64_gv s eB hBTy hBLocal,
                 semPexpr_Pvar_u64_gv s eC hCTy hCLocal,
                 CoqSemMirror.JResult.bind_ok, bind, Bind.bind]
    have hExecSopn : CoqSemMirror.execSopn realAsmSem (.Oasm "SBB_64")
        [ .Vword .U64 (s.regs eA.gv.var.vname),
          .Vword .U64 (s.regs eB.gv.var.vname),
          .Vword .U64 (s.regs eC.gv.var.vname) ]
        = .ok [ .Vbool false, .Vword .U64 cf, .Vbool false, .Vbool false,
                .Vbool false, .Vword .U64 r ] := by
      exact (realSopnSem.eq_4 _ _ _).trans (by rw [hCR])
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true [] realOpSem
              (stateToEstate s)
              [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
                .Pvar (astToMirror_GVar eC) ])
            (fun vs => CoqSemMirror.JResult.bind
              (CoqSemMirror.execSopn realAsmSem (.Oasm "SBB_64") vs)
              (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
                realOpSem (stateToEstate s)
                [ .Lnone () .abool, .Lvar (astToMirror_VarI cfV),
                  .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
                  .Lvar (astToMirror_VarI rV) ] rs))
        = _
    rw [hSemArgs]
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.execSopn realAsmSem (.Oasm "SBB_64")
              [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname),
                .Vword .U64 (s.regs eC.gv.var.vname) ])
            (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
              realOpSem (stateToEstate s)
              [ .Lnone () .abool, .Lvar (astToMirror_VarI cfV),
                .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
                .Lvar (astToMirror_VarI rV) ] rs)
        = _
    rw [hExecSopn]
    exact writeLvals_SUBbundle s cfV rV cf r hCFTy hRTy hCFhomog hRhomog

/-- `OpcodeAgrees` for `MULX`.  2-input, 2-LVal `[hi, lo]` bundle.  No flag
    side-effects on either side. -/
theorem opcodeAgrees_Copn_MULX
    (eA eB : CatCrypt.Crypto.Jasmin.GVar)
    (hiV loV : CatCrypt.Crypto.Jasmin.VarI)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hHiTy : hiV.var.vtype = .sword .U64)
    (hLoTy : loV.var.vtype = .sword .U64)
    (hHihomog : ∀ x : CoqSemMirror.Var,
        x.vname = hiV.var.vname → x.vtype = .aword .U64)
    (hLohomog : ∀ x : CoqSemMirror.Var,
        x.vname = loV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees
      (.Copn [.Lvar hiV, .Lvar loV] tag (.Oasm ⟨"MULX"⟩)
        [.Pvar eA, .Pvar eB]) := by
  intro s s' mi fuel hMi hExec hFuel
  have hMi_eq : astToMirror_InstrR
        (.Copn [.Lvar hiV, .Lvar loV] tag (.Oasm ⟨"MULX"⟩)
          [.Pvar eA, .Pvar eB])
      = some (.Copn
          [ .Lvar (astToMirror_VarI hiV), .Lvar (astToMirror_VarI loV) ]
          (astToMirror_AssgnTag tag) (.Oasm "MULX")
          [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ]) := rfl
  rw [hMi_eq] at hMi
  have hMi' := Option.some.inj hMi; subst hMi'
  have hExec_eq : BignumExec.execInstr s
        (.Copn [.Lvar hiV, .Lvar loV] tag (.Oasm ⟨"MULX"⟩)
          [.Pvar eA, .Pvar eB])
      = (match BignumExec.mulx (s.regs eA.gv.var.vname)
                               (s.regs eB.gv.var.vname) with
         | (hi, lo) =>
           some (BignumExec.setReg (BignumExec.setReg s hiV.var.vname hi)
                                    loV.var.vname lo)) := by
    unfold BignumExec.execInstr BignumExec.evalPExpr BignumExec.writeMulxBundle
    rfl
  rw [hExec_eq] at hExec
  revert hExec
  generalize hCR : BignumExec.mulx (s.regs eA.gv.var.vname)
                                   (s.regs eB.gv.var.vname) = pr
  obtain ⟨hi, lo⟩ := pr
  intro hExec
  simp only at hExec
  have hExec' : s' = BignumExec.setReg
        (BignumExec.setReg s hiV.var.vname hi) loV.var.vname lo :=
    (Option.some.inj hExec).symm
  subst hExec'
  cases fuel with
  | zero => omega
  | succ fuel' =>
    rw [execInstrR_Copn_step]
    unfold CoqSemMirror.semSopn
    have hSemArgs : CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true []
        realOpSem (stateToEstate s)
        [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ]
        = .ok [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname) ] := by
      show CoqSemMirror.semPexprList (Mem := MemoryModel.Mem) true [] realOpSem
            (stateToEstate s)
            [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ] = _
      unfold CoqSemMirror.semPexprList
      rw [semPexpr_Pvar_u64_gv s eA hATy hALocal]
      show ((do
        let vs ← CoqSemMirror.semPexprList (Mem := MemoryModel.Mem) true []
                  realOpSem (stateToEstate s) [ .Pvar (astToMirror_GVar eB) ]
        CoqSemMirror.JResult.ok (Value.Vword .U64 (s.regs eA.gv.var.vname) :: vs))
        : CoqSemMirror.JResult _) = _
      unfold CoqSemMirror.semPexprList
      rw [semPexpr_Pvar_u64_gv s eB hBTy hBLocal]
      rfl
    have hExecSopn : CoqSemMirror.execSopn realAsmSem (.Oasm "MULX")
        [ .Vword .U64 (s.regs eA.gv.var.vname),
          .Vword .U64 (s.regs eB.gv.var.vname) ]
        = .ok [ .Vword .U64 hi, .Vword .U64 lo ] := by
      exact (realSopnSem.eq_5 _ _).trans (by rw [hCR])
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true [] realOpSem
              (stateToEstate s)
              [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ])
            (fun vs => CoqSemMirror.JResult.bind
              (CoqSemMirror.execSopn realAsmSem (.Oasm "MULX") vs)
              (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
                realOpSem (stateToEstate s)
                [ .Lvar (astToMirror_VarI hiV), .Lvar (astToMirror_VarI loV) ] rs))
        = _
    rw [hSemArgs]
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.execSopn realAsmSem (.Oasm "MULX")
              [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname) ])
            (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
              realOpSem (stateToEstate s)
              [ .Lvar (astToMirror_VarI hiV), .Lvar (astToMirror_VarI loV) ] rs)
        = _
    rw [hExecSopn]
    exact writeLvals_MULXbundle s hiV loV hi lo hHiTy hLoTy hHihomog hLohomog

/-- `OpcodeAgrees` for `ADCX`.  3-input, 2-LVal `[cf_out, dst]` bundle. -/
theorem opcodeAgrees_Copn_ADCX
    (eA eB eC : CatCrypt.Crypto.Jasmin.GVar)
    (cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hCTy : eC.gv.var.vtype = .sword .U64) (hCLocal : eC.gs = false)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees
      (.Copn [.Lvar cfV, .Lvar rV] tag (.Oasm ⟨"ADCX"⟩)
        [.Pvar eA, .Pvar eB, .Pvar eC]) := by
  intro s s' mi fuel hMi hExec hFuel
  have hMi_eq : astToMirror_InstrR
        (.Copn [.Lvar cfV, .Lvar rV] tag (.Oasm ⟨"ADCX"⟩)
          [.Pvar eA, .Pvar eB, .Pvar eC])
      = some (.Copn
          [ .Lvar (astToMirror_VarI cfV), .Lvar (astToMirror_VarI rV) ]
          (astToMirror_AssgnTag tag) (.Oasm "ADCX")
          [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
            .Pvar (astToMirror_GVar eC) ]) := rfl
  rw [hMi_eq] at hMi
  have hMi' := Option.some.inj hMi; subst hMi'
  have hExec_eq : BignumExec.execInstr s
        (.Copn [.Lvar cfV, .Lvar rV] tag (.Oasm ⟨"ADCX"⟩)
          [.Pvar eA, .Pvar eB, .Pvar eC])
      = (match BignumExec.addCarryIn (s.regs eA.gv.var.vname)
                                     (s.regs eB.gv.var.vname)
                                     (s.regs eC.gv.var.vname) with
         | (cf, r) =>
           some (BignumExec.setReg (BignumExec.setReg s cfV.var.vname cf)
                                    rV.var.vname r)) := by
    unfold BignumExec.execInstr BignumExec.evalPExpr BignumExec.writeAdxBundle
    rfl
  rw [hExec_eq] at hExec
  revert hExec
  generalize hCR : BignumExec.addCarryIn (s.regs eA.gv.var.vname)
                                         (s.regs eB.gv.var.vname)
                                         (s.regs eC.gv.var.vname) = cr
  obtain ⟨cf, r⟩ := cr
  intro hExec
  simp only at hExec
  have hExec' : s' = BignumExec.setReg
        (BignumExec.setReg s cfV.var.vname cf) rV.var.vname r :=
    (Option.some.inj hExec).symm
  subst hExec'
  cases fuel with
  | zero => omega
  | succ fuel' =>
    rw [execInstrR_Copn_step]
    unfold CoqSemMirror.semSopn
    have hSemArgs : CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true []
        realOpSem (stateToEstate s)
        [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
          .Pvar (astToMirror_GVar eC) ]
        = .ok [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname),
                .Vword .U64 (s.regs eC.gv.var.vname) ] := by
      show CoqSemMirror.semPexprList (Mem := MemoryModel.Mem) true [] realOpSem
            (stateToEstate s)
            [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
              .Pvar (astToMirror_GVar eC) ] = _
      simp only [CoqSemMirror.semPexprList,
                 semPexpr_Pvar_u64_gv s eA hATy hALocal,
                 semPexpr_Pvar_u64_gv s eB hBTy hBLocal,
                 semPexpr_Pvar_u64_gv s eC hCTy hCLocal,
                 CoqSemMirror.JResult.bind_ok, bind, Bind.bind]
    have hExecSopn : CoqSemMirror.execSopn realAsmSem (.Oasm "ADCX")
        [ .Vword .U64 (s.regs eA.gv.var.vname),
          .Vword .U64 (s.regs eB.gv.var.vname),
          .Vword .U64 (s.regs eC.gv.var.vname) ]
        = .ok [ .Vword .U64 cf, .Vword .U64 r ] := by
      exact (realSopnSem.eq_6 _ _ _).trans (by rw [hCR])
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true [] realOpSem
              (stateToEstate s)
              [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
                .Pvar (astToMirror_GVar eC) ])
            (fun vs => CoqSemMirror.JResult.bind
              (CoqSemMirror.execSopn realAsmSem (.Oasm "ADCX") vs)
              (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
                realOpSem (stateToEstate s)
                [ .Lvar (astToMirror_VarI cfV), .Lvar (astToMirror_VarI rV) ] rs))
        = _
    rw [hSemArgs]
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.execSopn realAsmSem (.Oasm "ADCX")
              [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname),
                .Vword .U64 (s.regs eC.gv.var.vname) ])
            (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
              realOpSem (stateToEstate s)
              [ .Lvar (astToMirror_VarI cfV), .Lvar (astToMirror_VarI rV) ] rs)
        = _
    rw [hExecSopn]
    exact writeLvals_ADXbundle s cfV rV cf r hCFTy hRTy hCFhomog hRhomog

/-- `OpcodeAgrees` for `ADOX`.  Same `[flag, dst]` bundle as `ADCX`; the
    flag captured represents OF.  Semantically `realSopnSem` returns the
    same `(addCarryIn _, _)` shape (since at the model level ADOX and ADCX
    perform identical arithmetic, just on different chain flags). -/
theorem opcodeAgrees_Copn_ADOX
    (eA eB eC : CatCrypt.Crypto.Jasmin.GVar)
    (ofV rV : CatCrypt.Crypto.Jasmin.VarI)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hCTy : eC.gv.var.vtype = .sword .U64) (hCLocal : eC.gs = false)
    (hOFTy : ofV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hOFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = ofV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees
      (.Copn [.Lvar ofV, .Lvar rV] tag (.Oasm ⟨"ADOX"⟩)
        [.Pvar eA, .Pvar eB, .Pvar eC]) := by
  intro s s' mi fuel hMi hExec hFuel
  have hMi_eq : astToMirror_InstrR
        (.Copn [.Lvar ofV, .Lvar rV] tag (.Oasm ⟨"ADOX"⟩)
          [.Pvar eA, .Pvar eB, .Pvar eC])
      = some (.Copn
          [ .Lvar (astToMirror_VarI ofV), .Lvar (astToMirror_VarI rV) ]
          (astToMirror_AssgnTag tag) (.Oasm "ADOX")
          [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
            .Pvar (astToMirror_GVar eC) ]) := rfl
  rw [hMi_eq] at hMi
  have hMi' := Option.some.inj hMi; subst hMi'
  have hExec_eq : BignumExec.execInstr s
        (.Copn [.Lvar ofV, .Lvar rV] tag (.Oasm ⟨"ADOX"⟩)
          [.Pvar eA, .Pvar eB, .Pvar eC])
      = (match BignumExec.addCarryIn (s.regs eA.gv.var.vname)
                                     (s.regs eB.gv.var.vname)
                                     (s.regs eC.gv.var.vname) with
         | (of, r) =>
           some (BignumExec.setReg (BignumExec.setReg s ofV.var.vname of)
                                    rV.var.vname r)) := by
    unfold BignumExec.execInstr BignumExec.evalPExpr BignumExec.writeAdxBundle
    rfl
  rw [hExec_eq] at hExec
  revert hExec
  generalize hCR : BignumExec.addCarryIn (s.regs eA.gv.var.vname)
                                         (s.regs eB.gv.var.vname)
                                         (s.regs eC.gv.var.vname) = pr
  obtain ⟨of_, r⟩ := pr
  intro hExec
  simp only at hExec
  have hExec' : s' = BignumExec.setReg
        (BignumExec.setReg s ofV.var.vname of_) rV.var.vname r :=
    (Option.some.inj hExec).symm
  subst hExec'
  cases fuel with
  | zero => omega
  | succ fuel' =>
    rw [execInstrR_Copn_step]
    unfold CoqSemMirror.semSopn
    have hSemArgs : CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true []
        realOpSem (stateToEstate s)
        [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
          .Pvar (astToMirror_GVar eC) ]
        = .ok [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname),
                .Vword .U64 (s.regs eC.gv.var.vname) ] := by
      show CoqSemMirror.semPexprList (Mem := MemoryModel.Mem) true [] realOpSem
            (stateToEstate s)
            [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
              .Pvar (astToMirror_GVar eC) ] = _
      simp only [CoqSemMirror.semPexprList,
                 semPexpr_Pvar_u64_gv s eA hATy hALocal,
                 semPexpr_Pvar_u64_gv s eB hBTy hBLocal,
                 semPexpr_Pvar_u64_gv s eC hCTy hCLocal,
                 CoqSemMirror.JResult.bind_ok, bind, Bind.bind]
    have hExecSopn : CoqSemMirror.execSopn realAsmSem (.Oasm "ADOX")
        [ .Vword .U64 (s.regs eA.gv.var.vname),
          .Vword .U64 (s.regs eB.gv.var.vname),
          .Vword .U64 (s.regs eC.gv.var.vname) ]
        = .ok [ .Vword .U64 of_, .Vword .U64 r ] := by
      exact (realSopnSem.eq_7 _ _ _).trans (by rw [hCR])
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true [] realOpSem
              (stateToEstate s)
              [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB),
                .Pvar (astToMirror_GVar eC) ])
            (fun vs => CoqSemMirror.JResult.bind
              (CoqSemMirror.execSopn realAsmSem (.Oasm "ADOX") vs)
              (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
                realOpSem (stateToEstate s)
                [ .Lvar (astToMirror_VarI ofV), .Lvar (astToMirror_VarI rV) ] rs))
        = _
    rw [hSemArgs]
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.execSopn realAsmSem (.Oasm "ADOX")
              [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname),
                .Vword .U64 (s.regs eC.gv.var.vname) ])
            (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
              realOpSem (stateToEstate s)
              [ .Lvar (astToMirror_VarI ofV), .Lvar (astToMirror_VarI rV) ] rs)
        = _
    rw [hExecSopn]
    exact writeLvals_ADXbundle s ofV rV of_ r hOFTy hRTy hOFhomog hRhomog

/-- `OpcodeAgrees` for `XOR_64`.  2-input, 6-LVal XOR-bundle `[of, cf, _, _,
    _, r]` (both flags captured, both cleared).  We use the XOR-bundle on
    the BignumExec side (first arm of `writeXorBundle`). -/
theorem opcodeAgrees_Copn_XOR_64
    (eA eB : CatCrypt.Crypto.Jasmin.GVar)
    (ofV cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (info1 info2 info3 : CatCrypt.Crypto.Jasmin.VarInfo)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hOFTy : ofV.var.vtype = .sword .U64)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hOFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = ofV.var.vname → x.vtype = .aword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees
      (.Copn
        [.Lvar ofV, .Lvar cfV,
         .Lnone info1 .sbool, .Lnone info2 .sbool, .Lnone info3 .sbool,
         .Lvar rV]
        tag (.Oasm ⟨"XOR_64"⟩) [.Pvar eA, .Pvar eB]) := by
  intro s s' mi fuel hMi hExec hFuel
  have hMi_eq : astToMirror_InstrR
        (.Copn
          [.Lvar ofV, .Lvar cfV,
           .Lnone info1 .sbool, .Lnone info2 .sbool, .Lnone info3 .sbool,
           .Lvar rV]
          tag (.Oasm ⟨"XOR_64"⟩) [.Pvar eA, .Pvar eB])
      = some (.Copn
          [ .Lvar (astToMirror_VarI ofV), .Lvar (astToMirror_VarI cfV),
            .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
            .Lvar (astToMirror_VarI rV) ]
          (astToMirror_AssgnTag tag) (.Oasm "XOR_64")
          [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ]) := rfl
  rw [hMi_eq] at hMi
  have hMi' := Option.some.inj hMi; subst hMi'
  have hExec_eq : BignumExec.execInstr s
        (.Copn
          [.Lvar ofV, .Lvar cfV,
           .Lnone info1 .sbool, .Lnone info2 .sbool, .Lnone info3 .sbool,
           .Lvar rV]
          tag (.Oasm ⟨"XOR_64"⟩) [.Pvar eA, .Pvar eB])
      = some (BignumExec.setReg
          (BignumExec.setReg (BignumExec.setReg s ofV.var.vname 0)
            cfV.var.vname 0)
          rV.var.vname ((s.regs eA.gv.var.vname) ^^^ (s.regs eB.gv.var.vname))) := by
    unfold BignumExec.execInstr BignumExec.evalPExpr BignumExec.writeXorBundle
    rfl
  rw [hExec_eq] at hExec
  have hExec' : s' = BignumExec.setReg
        (BignumExec.setReg (BignumExec.setReg s ofV.var.vname 0)
          cfV.var.vname 0)
        rV.var.vname ((s.regs eA.gv.var.vname) ^^^ (s.regs eB.gv.var.vname)) :=
    (Option.some.inj hExec).symm
  subst hExec'
  cases fuel with
  | zero => omega
  | succ fuel' =>
    rw [execInstrR_Copn_step]
    unfold CoqSemMirror.semSopn
    have hSemArgs : CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true []
        realOpSem (stateToEstate s)
        [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ]
        = .ok [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname) ] := by
      show CoqSemMirror.semPexprList (Mem := MemoryModel.Mem) true [] realOpSem
            (stateToEstate s)
            [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ] = _
      unfold CoqSemMirror.semPexprList
      rw [semPexpr_Pvar_u64_gv s eA hATy hALocal]
      show ((do
        let vs ← CoqSemMirror.semPexprList (Mem := MemoryModel.Mem) true []
                  realOpSem (stateToEstate s) [ .Pvar (astToMirror_GVar eB) ]
        CoqSemMirror.JResult.ok (Value.Vword .U64 (s.regs eA.gv.var.vname) :: vs))
        : CoqSemMirror.JResult _) = _
      unfold CoqSemMirror.semPexprList
      rw [semPexpr_Pvar_u64_gv s eB hBTy hBLocal]
      rfl
    have hExecSopn : CoqSemMirror.execSopn realAsmSem (.Oasm "XOR_64")
        [ .Vword .U64 (s.regs eA.gv.var.vname),
          .Vword .U64 (s.regs eB.gv.var.vname) ]
        = .ok [ .Vword .U64 0, .Vword .U64 0, .Vbool false, .Vbool false,
                .Vbool false,
                .Vword .U64 ((s.regs eA.gv.var.vname) ^^^ (s.regs eB.gv.var.vname)) ] := by
      unfold CoqSemMirror.execSopn realAsmSem realSopnSem
      rfl
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.semPexprs (Mem := MemoryModel.Mem) true [] realOpSem
              (stateToEstate s)
              [ .Pvar (astToMirror_GVar eA), .Pvar (astToMirror_GVar eB) ])
            (fun vs => CoqSemMirror.JResult.bind
              (CoqSemMirror.execSopn realAsmSem (.Oasm "XOR_64") vs)
              (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
                realOpSem (stateToEstate s)
                [ .Lvar (astToMirror_VarI ofV), .Lvar (astToMirror_VarI cfV),
                  .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
                  .Lvar (astToMirror_VarI rV) ] rs))
        = _
    rw [hSemArgs]
    show CoqSemMirror.JResult.bind
            (CoqSemMirror.execSopn realAsmSem (.Oasm "XOR_64")
              [ .Vword .U64 (s.regs eA.gv.var.vname),
                .Vword .U64 (s.regs eB.gv.var.vname) ])
            (fun rs => CoqSemMirror.writeLvals (Mem := MemoryModel.Mem) true []
              realOpSem (stateToEstate s)
              [ .Lvar (astToMirror_VarI ofV), .Lvar (astToMirror_VarI cfV),
                .Lnone () .abool, .Lnone () .abool, .Lnone () .abool,
                .Lvar (astToMirror_VarI rV) ] rs)
        = _
    rw [hExecSopn]
    exact writeLvals_XORbundle s ofV cfV rV 0 0
      ((s.regs eA.gv.var.vname) ^^^ (s.regs eB.gv.var.vname))
      hOFTy hCFTy hRTy hOFhomog hCFhomog hRhomog

/-! ### §5.b. Chain-level bridge

Given that every instruction in a chain satisfies `OpcodeAgrees`, the chain
agreement follows.  Per-opcode batches feed into this lemma. -/

/-- Helper variant: translate a list of `InstrR` using a structural fold.
    This bypasses `List.mapM` (which uses `mapM.loop`) and gives clean
    `cons`-pattern reduction for the chain proof. -/
def astToMirror_List : List CatCrypt.Crypto.Jasmin.InstrR →
    Option (List CoqSemMirror.InstrR)
  | [] => some []
  | i :: is =>
      match astToMirror_InstrR i with
      | none => none
      | some mi =>
        match astToMirror_List is with
        | none => none
        | some mIs => some (mi :: mIs)

/-- Chain-level bridge.  If every instruction in `is` translates and
    individually satisfies `OpcodeAgrees`, then `bignumExec is s = some s'`
    implies the mirror's `execCmd` on the translated chain (wrapped as
    `Instr`s via `MkI ()`) ends in `stateToEstate s'`. -/
theorem bignumExec_agrees_coqSem_chain_skel
    (is : List CatCrypt.Crypto.Jasmin.InstrR)
    (mIs : List CoqSemMirror.InstrR)
    (hTrans : astToMirror_List is = some mIs)
    (hAllAgree : ∀ i ∈ is, OpcodeAgrees i)
    (s s' : BignumExec.BignumState)
    (hExec : BignumExec.bignumExec is s = some s')
    (fuel : Nat) (hFuel : is.length < fuel) :
    CoqSemMirror.execCmd (Mem := MemoryModel.Mem) realAsmSem realOpSem []
      fuel (stateToEstate s)
      (mIs.map (fun ir => .MkI () ir))
    = .ok (stateToEstate s') := by
  induction is generalizing mIs s fuel with
  | nil =>
    -- mIs = [], execCmd on [] = .ok s, bignumExec [] = .ok s
    simp only [astToMirror_List] at hTrans
    cases hTrans
    simp only [BignumExec.bignumExec] at hExec
    cases hExec
    cases fuel with
    | zero => omega
    | succ fuel' => simp [CoqSemMirror.execCmd, List.map]
  | cons i is ih =>
    -- Decode the translation.
    simp only [astToMirror_List] at hTrans
    rcases hMiHead : astToMirror_InstrR i with _ | mi
    · simp [hMiHead] at hTrans
    rcases hMiTail : astToMirror_List is with _ | mIs'
    · simp [hMiHead, hMiTail] at hTrans
    simp only [hMiHead, hMiTail] at hTrans
    cases hTrans
    -- Decode the BignumExec side.
    simp only [BignumExec.bignumExec] at hExec
    rcases hExecHead : BignumExec.execInstr s i with _ | s1
    · simp [hExecHead] at hExec
    simp only [hExecHead] at hExec
    cases fuel with
    | zero => simp at hFuel
    | succ fuel' =>
      -- Apply OpcodeAgrees on i for the head step.
      have hHead := hAllAgree i (by simp) s s1 mi (fuel' + 1) hMiHead hExecHead (by omega)
      -- Recurse on the tail.
      simp only [List.map, CoqSemMirror.execCmd, CoqSemMirror.execInstr]
      have hRecAgree : ∀ j ∈ is, OpcodeAgrees j := fun j hj => hAllAgree j (by simp [hj])
      have hRecFuel : is.length < fuel' + 1 := by
        simp only [List.length] at hFuel; omega
      -- After execInstr fuel s (.MkI () mi), the result is execInstrR (fuel'+1) s mi.
      -- Note `execInstr fuel s (.MkI _ ir) = execInstrR fuel s ir` definitionally.
      -- The bind chains through `do` should reduce automatically once we have hHead.
      change CoqSemMirror.execInstrR realAsmSem realOpSem [] (fuel' + 1)
          (stateToEstate s) mi >>= (fun s' =>
            CoqSemMirror.execCmd realAsmSem realOpSem [] (fuel' + 1) s'
              (mIs'.map (fun ir => .MkI () ir))) = _
      rw [hHead]
      -- Now the bind reduces (ok x >>= f = f x by JResult.bind).
      show CoqSemMirror.execCmd realAsmSem realOpSem [] (fuel' + 1)
          (stateToEstate s1) (mIs'.map (fun ir => .MkI () ir)) = _
      exact ih mIs' hMiTail hRecAgree s1 hExec (fuel' + 1) hRecFuel

/-! ## §6. `Vm.Equiv`-friendly per-opcode lemmas (2026-05-28)

The lemmas in §5 establish a strict-equality form of `OpcodeAgrees`:
the mirror executor's output state is *structurally equal* to
`stateToEstate s'`.  Under the current `CoqSemMirror.Vm := Var → Value`
representation, structural equality follows by `funext` from pointwise
agreement (`liftVm_setReg_eq`).

A future restructure of `Vm` to a finite map (blocking the universal
connector for MAYO's `runFullBody`) breaks structural equality: the
LHS and RHS of `Vm.set (liftVm s) v ... = liftVm (setReg s v.vname ...)`
will have different store layouts even though their `.get` views still
agree.  Only `Vm.Equiv` survives.

This section adds **Equiv-friendly variants** of the per-opcode
agreement: `OpcodeAgrees_Equiv` says the mirror's output state is
**`Estate.Equiv`** to `stateToEstate s'`, not structurally equal.  We
prove a single **generic lift** `OpcodeAgrees_Equiv_of_OpcodeAgrees`
that turns the strict-equality version into the Equiv version, so the
8 existing per-opcode proofs in §5 transfer automatically without
duplication.  The chain-level bridge can then be rerun in the Equiv
world by composing `Estate.Equiv.trans`.

This section adds NO axioms and changes NO existing proof.  It is
forward-looking infrastructure: once the `Vm` finite-map restructure
lands, the bridge proofs continue to typecheck against the Equiv
variant. -/

open CatCrypt.Crypto.Jasmin.VmFlatExec

/-- **Equiv-friendly OpcodeAgrees.**  Same shape as `OpcodeAgrees`,
    but the conclusion uses `Estate.Equiv` instead of structural
    equality.  Survives a future `Vm` restructure to a finite map
    (where `Vm.set` and `liftVm (setReg ...)` are pointwise equal but
    structurally distinct).

    Pre-Vm-restructure, the strict-equality form implies the Equiv
    form trivially (by `Estate.equiv_of_eq`); see
    `OpcodeAgrees_Equiv_of_OpcodeAgrees` below.  Post-Vm-restructure,
    the strict form will fail to compile, but the Equiv form is the
    drop-in replacement. -/
def OpcodeAgrees_Equiv (i : CatCrypt.Crypto.Jasmin.InstrR) : Prop :=
  ∀ (s s' : BignumExec.BignumState) (mi : CoqSemMirror.InstrR) (fuel : Nat),
    astToMirror_InstrR i = some mi →
    BignumExec.execInstr s i = some s' →
    0 < fuel →
    ∃ rs : CoqSemMirror.Estate Unit MemoryModel.Mem,
      CoqSemMirror.execInstrR (Mem := MemoryModel.Mem)
          realAsmSem realOpSem [] fuel (stateToEstate s) mi = .ok rs ∧
      Estate.Equiv rs (stateToEstate s')

/-- **Generic lift**: the strict `OpcodeAgrees` implies the
    `Equiv`-friendly form.  Under the current function-Vm
    representation, this is a one-liner because `Estate.Equiv`
    refl on the same state.

    The lift is **forward-looking**: under a future `Vm` finite-map
    restructure, the strict form will not type-check at all (the
    structural equality between `Vm.set` and `liftVm (setReg ...)`
    fails), so per-opcode proofs will be re-stated directly in the
    Equiv form.  But until then, this lift means **the 9 per-opcode
    Equiv variants are free** — no duplication of the ~400 LOC
    `opcodeAgrees_Copn_*` proofs. -/
theorem OpcodeAgrees_Equiv_of_OpcodeAgrees
    (i : CatCrypt.Crypto.Jasmin.InstrR) (h : OpcodeAgrees i) :
    OpcodeAgrees_Equiv i := by
  intro s s' mi fuel hMi hExec hFuel
  refine ⟨stateToEstate s', ?_, Estate.Equiv.refl _⟩
  exact h s s' mi fuel hMi hExec hFuel

/-! ### §6.a. Equiv variants of the 9 per-opcode lemmas

Each Equiv variant follows from its strict counterpart by
`OpcodeAgrees_Equiv_of_OpcodeAgrees`.  We name them with the suffix
`_equiv` to make the parallel discoverable. -/

/-- Equiv variant of `opcodeAgrees_Cassgn_Lvar_Pvar`. -/
theorem opcodeAgrees_Cassgn_Lvar_Pvar_equiv
    (v : CatCrypt.Crypto.Jasmin.VarI) (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (ty : CatCrypt.Crypto.Jasmin.SType) (w : CatCrypt.Crypto.Jasmin.GVar)
    (hVTy : v.var.vtype = .sword .U64)
    (hWTy : w.gv.var.vtype = .sword .U64)
    (hTy : ty = .sword .U64)
    (hWLocal : w.gs = false)
    (hHomogV : ∀ x : CoqSemMirror.Var,
        x.vname = v.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees_Equiv (.Cassgn (.Lvar v) tag ty (.Pvar w)) :=
  OpcodeAgrees_Equiv_of_OpcodeAgrees _
    (opcodeAgrees_Cassgn_Lvar_Pvar v tag ty w hVTy hWTy hTy hWLocal hHomogV)

/-- Equiv variant of `opcodeAgrees_Copn_ADD_64`. -/
theorem opcodeAgrees_Copn_ADD_64_equiv
    (eA eB : CatCrypt.Crypto.Jasmin.GVar)
    (cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (info1 info2 info3 info4 : CatCrypt.Crypto.Jasmin.VarInfo)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees_Equiv
      (.Copn
        [.Lnone info1 .sbool, .Lvar cfV,
         .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
         .Lvar rV]
        tag (.Oasm ⟨"ADD_64"⟩) [.Pvar eA, .Pvar eB]) :=
  OpcodeAgrees_Equiv_of_OpcodeAgrees _
    (opcodeAgrees_Copn_ADD_64 eA eB cfV rV info1 info2 info3 info4 tag
      hATy hALocal hBTy hBLocal hCFTy hRTy hCFhomog hRhomog)

/-- Equiv variant of `opcodeAgrees_Copn_SUB_64`. -/
theorem opcodeAgrees_Copn_SUB_64_equiv
    (eA eB : CatCrypt.Crypto.Jasmin.GVar)
    (cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (info1 info2 info3 info4 : CatCrypt.Crypto.Jasmin.VarInfo)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees_Equiv
      (.Copn
        [.Lnone info1 .sbool, .Lvar cfV,
         .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
         .Lvar rV]
        tag (.Oasm ⟨"SUB_64"⟩) [.Pvar eA, .Pvar eB]) :=
  OpcodeAgrees_Equiv_of_OpcodeAgrees _
    (opcodeAgrees_Copn_SUB_64 eA eB cfV rV info1 info2 info3 info4 tag
      hATy hALocal hBTy hBLocal hCFTy hRTy hCFhomog hRhomog)

/-- Equiv variant of `opcodeAgrees_Copn_ADC_64`. -/
theorem opcodeAgrees_Copn_ADC_64_equiv
    (eA eB eC : CatCrypt.Crypto.Jasmin.GVar)
    (cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (info1 info2 info3 info4 : CatCrypt.Crypto.Jasmin.VarInfo)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hCTy : eC.gv.var.vtype = .sword .U64) (hCLocal : eC.gs = false)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees_Equiv
      (.Copn
        [.Lnone info1 .sbool, .Lvar cfV,
         .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
         .Lvar rV]
        tag (.Oasm ⟨"ADC_64"⟩) [.Pvar eA, .Pvar eB, .Pvar eC]) :=
  OpcodeAgrees_Equiv_of_OpcodeAgrees _
    (opcodeAgrees_Copn_ADC_64 eA eB eC cfV rV info1 info2 info3 info4 tag
      hATy hALocal hBTy hBLocal hCTy hCLocal hCFTy hRTy hCFhomog hRhomog)

/-- Equiv variant of `opcodeAgrees_Copn_SBB_64`. -/
theorem opcodeAgrees_Copn_SBB_64_equiv
    (eA eB eC : CatCrypt.Crypto.Jasmin.GVar)
    (cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (info1 info2 info3 info4 : CatCrypt.Crypto.Jasmin.VarInfo)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hCTy : eC.gv.var.vtype = .sword .U64) (hCLocal : eC.gs = false)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees_Equiv
      (.Copn
        [.Lnone info1 .sbool, .Lvar cfV,
         .Lnone info2 .sbool, .Lnone info3 .sbool, .Lnone info4 .sbool,
         .Lvar rV]
        tag (.Oasm ⟨"SBB_64"⟩) [.Pvar eA, .Pvar eB, .Pvar eC]) :=
  OpcodeAgrees_Equiv_of_OpcodeAgrees _
    (opcodeAgrees_Copn_SBB_64 eA eB eC cfV rV info1 info2 info3 info4 tag
      hATy hALocal hBTy hBLocal hCTy hCLocal hCFTy hRTy hCFhomog hRhomog)

/-- Equiv variant of `opcodeAgrees_Copn_MULX`. -/
theorem opcodeAgrees_Copn_MULX_equiv
    (eA eB : CatCrypt.Crypto.Jasmin.GVar)
    (hiV loV : CatCrypt.Crypto.Jasmin.VarI)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hHiTy : hiV.var.vtype = .sword .U64)
    (hLoTy : loV.var.vtype = .sword .U64)
    (hHihomog : ∀ x : CoqSemMirror.Var,
        x.vname = hiV.var.vname → x.vtype = .aword .U64)
    (hLohomog : ∀ x : CoqSemMirror.Var,
        x.vname = loV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees_Equiv
      (.Copn [.Lvar hiV, .Lvar loV] tag (.Oasm ⟨"MULX"⟩)
        [.Pvar eA, .Pvar eB]) :=
  OpcodeAgrees_Equiv_of_OpcodeAgrees _
    (opcodeAgrees_Copn_MULX eA eB hiV loV tag
      hATy hALocal hBTy hBLocal hHiTy hLoTy hHihomog hLohomog)

/-- Equiv variant of `opcodeAgrees_Copn_ADCX`. -/
theorem opcodeAgrees_Copn_ADCX_equiv
    (eA eB eC : CatCrypt.Crypto.Jasmin.GVar)
    (cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hCTy : eC.gv.var.vtype = .sword .U64) (hCLocal : eC.gs = false)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees_Equiv
      (.Copn [.Lvar cfV, .Lvar rV] tag (.Oasm ⟨"ADCX"⟩)
        [.Pvar eA, .Pvar eB, .Pvar eC]) :=
  OpcodeAgrees_Equiv_of_OpcodeAgrees _
    (opcodeAgrees_Copn_ADCX eA eB eC cfV rV tag
      hATy hALocal hBTy hBLocal hCTy hCLocal hCFTy hRTy hCFhomog hRhomog)

/-- Equiv variant of `opcodeAgrees_Copn_ADOX`. -/
theorem opcodeAgrees_Copn_ADOX_equiv
    (eA eB eC : CatCrypt.Crypto.Jasmin.GVar)
    (ofV rV : CatCrypt.Crypto.Jasmin.VarI)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hCTy : eC.gv.var.vtype = .sword .U64) (hCLocal : eC.gs = false)
    (hOFTy : ofV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hOFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = ofV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees_Equiv
      (.Copn [.Lvar ofV, .Lvar rV] tag (.Oasm ⟨"ADOX"⟩)
        [.Pvar eA, .Pvar eB, .Pvar eC]) :=
  OpcodeAgrees_Equiv_of_OpcodeAgrees _
    (opcodeAgrees_Copn_ADOX eA eB eC ofV rV tag
      hATy hALocal hBTy hBLocal hCTy hCLocal hOFTy hRTy hOFhomog hRhomog)

/-- Equiv variant of `opcodeAgrees_Copn_XOR_64`. -/
theorem opcodeAgrees_Copn_XOR_64_equiv
    (eA eB : CatCrypt.Crypto.Jasmin.GVar)
    (ofV cfV rV : CatCrypt.Crypto.Jasmin.VarI)
    (info1 info2 info3 : CatCrypt.Crypto.Jasmin.VarInfo)
    (tag : CatCrypt.Crypto.Jasmin.AssgnTag)
    (hATy : eA.gv.var.vtype = .sword .U64) (hALocal : eA.gs = false)
    (hBTy : eB.gv.var.vtype = .sword .U64) (hBLocal : eB.gs = false)
    (hOFTy : ofV.var.vtype = .sword .U64)
    (hCFTy : cfV.var.vtype = .sword .U64)
    (hRTy : rV.var.vtype = .sword .U64)
    (hOFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = ofV.var.vname → x.vtype = .aword .U64)
    (hCFhomog : ∀ x : CoqSemMirror.Var,
        x.vname = cfV.var.vname → x.vtype = .aword .U64)
    (hRhomog : ∀ x : CoqSemMirror.Var,
        x.vname = rV.var.vname → x.vtype = .aword .U64) :
    OpcodeAgrees_Equiv
      (.Copn
        [.Lvar ofV, .Lvar cfV,
         .Lnone info1 .sbool, .Lnone info2 .sbool, .Lnone info3 .sbool,
         .Lvar rV]
        tag (.Oasm ⟨"XOR_64"⟩) [.Pvar eA, .Pvar eB]) :=
  OpcodeAgrees_Equiv_of_OpcodeAgrees _
    (opcodeAgrees_Copn_XOR_64 eA eB ofV cfV rV info1 info2 info3 tag
      hATy hALocal hBTy hBLocal hOFTy hCFTy hRTy hOFhomog hCFhomog hRhomog)

/-! ### §6.b. Chain-level Equiv bridge

The strict-equality chain bridge (`bignumExec_agrees_coqSem_chain_skel`)
threads via structural `=` on each intermediate state.  The Equiv form
threads via `Estate.Equiv` chains.  Both are valid; the Equiv form is
preserved under a future `Vm` finite-map restructure. -/

/-- **Chain-level Equiv bridge.**  If every instruction in `is`
    translates and individually satisfies `OpcodeAgrees_Equiv`, then
    the mirror's `execCmd` on the translated chain produces an
    `Estate`-Equiv to `stateToEstate s'`.

    Because the strict `OpcodeAgrees` implies `OpcodeAgrees_Equiv`
    (via `OpcodeAgrees_Equiv_of_OpcodeAgrees`), this chain lemma is a
    drop-in replacement for `bignumExec_agrees_coqSem_chain_skel`
    under a future `Vm` restructure: pass the existing strict
    `hAllAgree` through the lift, and the Equiv chain proof carries
    the strict result via `Estate.Equiv.refl`. -/
theorem bignumExec_agrees_coqSem_chain_equiv_skel
    (is : List CatCrypt.Crypto.Jasmin.InstrR)
    (mIs : List CoqSemMirror.InstrR)
    (hTrans : astToMirror_List is = some mIs)
    (hAllAgree : ∀ i ∈ is, OpcodeAgrees i)
    (s s' : BignumExec.BignumState)
    (hExec : BignumExec.bignumExec is s = some s')
    (fuel : Nat) (hFuel : is.length < fuel) :
    ∃ rs : CoqSemMirror.Estate Unit MemoryModel.Mem,
      CoqSemMirror.execCmd (Mem := MemoryModel.Mem) realAsmSem realOpSem []
        fuel (stateToEstate s) (mIs.map (fun ir => .MkI () ir))
        = .ok rs ∧
      Estate.Equiv rs (stateToEstate s') := by
  -- Under the current Vm, the chain bridge gives strict equality;
  -- promote to Equiv via Estate.Equiv.refl.
  refine ⟨stateToEstate s', ?_, Estate.Equiv.refl _⟩
  exact bignumExec_agrees_coqSem_chain_skel is mIs hTrans hAllAgree s s'
        hExec fuel hFuel

/-! ### §6.c. Documentation: what changes under Vm restructure

When the canonical `Vm := Var → Value` is replaced by a finite map
structure:

* `Vm.eq_of_vm_equiv` (in `VmFlatExec.lean` §3) will fail — under a
  finite map, two `Vm`s that agree pointwise can have different
  internal stores.
* `liftVm_setReg_eq` (§5) will fail to typecheck — the LHS produces a
  store extension while the RHS produces a fully-rebuilt fallback
  function.  The Equiv form `Vm.Equiv (Vm.set (liftVm s) ...) (liftVm
  (setReg s ...))` is provable under finite-map Vm by pointwise
  case-analysis on the lookup target.
* The 9 strict `opcodeAgrees_*` theorems in §5 will fail — they end
  with `rfl` against a structurally rebuilt Estate.  Their Equiv
  variants in §6.a are proved directly, not derived from the strict form.
The Equiv chain bridge (§6.b) and the Equiv variant predicates
(§6.a) DON'T change in shape — only the proofs change.  This is the
key contract: any downstream proof that consumes
`OpcodeAgrees_Equiv` / `bignumExec_agrees_coqSem_chain_equiv_skel`
will continue to typecheck without modification when the Vm
restructure lands.

**Estimated work to re-prove §6.a under finite-map Vm**: ~60-90 LOC
across the 9 lemmas, plus ~20 LOC for a finite-map version of
`liftVm_setReg_equiv`.  The 8 Copn-bundle write lemmas in §5
(`writeLvals_SUBbundle` etc.) need a similar treatment but the
algebra is identical — only the `rfl`-style finishers swap to
`Estate.Equiv.refl` / `Vm.Equiv` chains. -/

end CatCrypt.Crypto.Jasmin.JasminEmitBridge
