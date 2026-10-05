/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.BignumExec
public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

@[expose] public section

set_option autoImplicit false

/-!
# Translation of the bignum `InstrR` fragment to `JInstr 64`, with its simulation

`toJ` translates one instruction of the straight-line fragment that `bignumExec`
interprets into a list of `JInstr 64`, and `toJBlock` translates a body. The covered
shapes are the ones of `bignum_mod_p25519_4`:

* `Cassgn (Lvar x)` of `Pconst`, `Pvar`, `Pload U64 b (Pconst k)` and of `Papp2` with
  `Oland`/`Olor`/`Olxor` over two variables;
* `Cassgn (Lmem U64 b (Pconst k))` of a variable;
* `Copn` of `SUB_64` and `SBB_64` over variables, with the six-place output bundle
  `[_, cf, _, _, _, r]`.

`bignumExec` keeps a carry in a register holding `0` or `1`; the address-memory machine
`runBlockA` keeps it in `CF`. The translation moves the carry between the two: `SUB_64`
becomes `mov r, a; sub r, b; setc cf`, and `SBB_64` becomes
`bt c, 0; mov r, a; sbb r, b; setc cf`, so no flag is live across translated
instructions. A shape whose destination register is also its second source, or whose
carry output names its data output, translates to `none`.

`BJCorr s sa` relates a `BignumState` to an `AState`: equal register files, and every
defined byte of `s.mem` equal to the byte at the same address of `sa.mem`.

## Main definitions

* `toJ`, `toJBlock`: the translation.
* `BJMem`, `BJCorr`: the state relation.
* `liftA`: the `BignumState` with the registers and the (total) memory of an `AState`.
* `MemTotal`: every byte of a `BignumState` memory is defined.
* `amemNat4`: the four-limb little-endian value of an address memory at a base.

## Main results

* `load64Mem_read64`, `bjMem_store64`: loads and stores agree across `BJMem`.
* `toJ_sim`: one translated instruction preserves `BJCorr`.
* `bignumExec_runBlockA_sim`: a translated body preserves `BJCorr`.
* `bignumExec_progress`: on a total memory a translatable body runs to a total memory.
* `bjCorr_liftA`: `liftA sa` is related to `sa`.
-/

namespace CatCrypt.Crypto.Jasmin.BignumToJ

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

/-! ## The translation -/

/-- `x := a op b` as `mov x, a; op x, b`; `none` when `b` is `x`. -/
def logicJ (x a b : String) (op : String → JOperand → JInstr 64) :
    Option (List (JInstr 64)) :=
  if b = x then none else some [.mov x (.reg a), op x (.reg b)]

/-- The translation of `x := e`. -/
def assignJ (x : String) : PExpr → Option (List (JInstr 64))
  | .Pconst z => some [.mov x (.imm (BitVec.ofInt 64 z).toNat)]
  | .Pvar g => some [.mov x (.reg g.gv.var.vname)]
  | .Pload .U64 b (.Pconst k) => some [.loadMem x b.var.vname k]
  | .Papp2 (.Oland _) (.Pvar a) (.Pvar b) => logicJ x a.gv.var.vname b.gv.var.vname .and_
  | .Papp2 (.Olor _) (.Pvar a) (.Pvar b) => logicJ x a.gv.var.vname b.gv.var.vname .or_
  | .Papp2 (.Olxor _) (.Pvar a) (.Pvar b) => logicJ x a.gv.var.vname b.gv.var.vname .xor_
  | _ => none

/-- `cf, r := SUB_64 a b` as `mov r, a; sub r, b; setc cf`. -/
def subJ (cf r a b : String) : Option (List (JInstr 64)) :=
  if r = b ∨ cf = r then none else some [.mov r (.reg a), .sub r (.reg b), .setc cf]

/-- `cf, r := SBB_64 a b c` as `bt c, 0; mov r, a; sbb r, b; setc cf`. -/
def sbbJ (cf r a b c : String) : Option (List (JInstr 64)) :=
  if r = b ∨ cf = r then none
  else some [.bt c (.imm 0), .mov r (.reg a), .sbb r (.reg b), .setc cf]

/-- The translation of a `Copn` with output bundle `lvs`, operator `name` and arguments
    `args`. -/
def opnJ (name : String) (lvs : List LVal) (args : List PExpr) : Option (List (JInstr 64)) :=
  match lvs with
  | [.Lnone _ _, .Lvar cfV, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rV] =>
    match args with
    | [.Pvar a, .Pvar b] =>
      if name = "SUB_64" then subJ cfV.var.vname rV.var.vname a.gv.var.vname b.gv.var.vname
      else none
    | [.Pvar a, .Pvar b, .Pvar c] =>
      if name = "SBB_64" then
        sbbJ cfV.var.vname rV.var.vname a.gv.var.vname b.gv.var.vname c.gv.var.vname
      else none
    | _ => none
  | _ => none

/-- The translation of one instruction. -/
def toJ : InstrR → Option (List (JInstr 64))
  | .Cassgn (.Lvar x) _ _ e => assignJ x.var.vname e
  | .Cassgn (.Lmem .U64 b (.Pconst k)) _ _ (.Pvar g) =>
      some [.storeMem b.var.vname k (.reg g.gv.var.vname)]
  | .Copn lvs _ (.Oasm op) args => opnJ op.name lvs args
  | _ => none

/-- The translation of a body: the concatenation of the instruction translations. -/
def toJBlock : List InstrR → Option (List (JInstr 64))
  | [] => some []
  | i :: is => do
      let js ← toJ i
      let jss ← toJBlock is
      some (js ++ jss)

/-! ## The state relation -/

/-- Every defined byte of `m` is the byte at the same address of `am`. -/
def BJMem (m : Mem) (am : AMem) : Prop :=
  ∀ a b, m a = some b → am a.toBitVec = b.toBitVec

/-- Equal register files, and the memories related by `BJMem`. -/
def BJCorr (s : BignumState) (sa : AState) : Prop :=
  s.regs = sa.regs ∧ BJMem s.mem sa.mem

/-- Every byte of `m` is defined. -/
def MemTotal (m : Mem) : Prop := ∀ a, (m a).isSome

/-- The `BignumState` with the registers of `sa` and the bytes of `sa.mem`, all defined. -/
def liftA (sa : AState) : BignumState where
  regs := sa.regs
  mem := fun a => some (UInt8.ofBitVec (sa.mem a.toBitVec))

theorem bjCorr_liftA (sa : AState) : BJCorr (liftA sa) sa := by
  refine ⟨rfl, ?_⟩
  intro a b h
  simp only [liftA, Option.some.injEq] at h
  subst h
  rfl

theorem memTotal_liftA (sa : AState) : MemTotal (liftA sa).mem := fun _ => rfl

/-- The four-limb little-endian value of `m` at `base`. -/
def amemNat4 (m : AMem) (base : BitVec 64) : Nat :=
  (read64 m base).toNat + (read64 m (base + 8)).toNat * 2 ^ 64
    + (read64 m (base + 16)).toNat * 2 ^ 128 + (read64 m (base + 24)).toNat * 2 ^ 192

/-! ## Loads and stores across `BJMem` -/

theorem or_mul_eq_add (acc y i : Nat) (h : acc < 2 ^ i) :
    acc ||| y * 2 ^ i = acc + y * 2 ^ i := by
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.add_comm]

theorem ofNat_bytes (y0 y1 y2 y3 y4 y5 y6 y7 : BitVec 8) :
    BitVec.ofNat 64 (y0.toNat + 2 ^ 8 * y1.toNat + 2 ^ 16 * y2.toNat + 2 ^ 24 * y3.toNat
      + 2 ^ 32 * y4.toNat + 2 ^ 40 * y5.toNat + 2 ^ 48 * y6.toNat + 2 ^ 56 * y7.toNat) =
    (y0.setWidth 64 ||| y1.setWidth 64 <<< 8 ||| y2.setWidth 64 <<< 16
      ||| y3.setWidth 64 <<< 24 ||| y4.setWidth 64 <<< 32 ||| y5.setWidth 64 <<< 40
      ||| y6.setWidth 64 <<< 48 ||| y7.setWidth 64 <<< 56) := by
  apply BitVec.eq_of_toNat_eq
  have := y0.isLt; have := y1.isLt; have := y2.isLt; have := y3.isLt
  have := y4.isLt; have := y5.isLt; have := y6.isLt; have := y7.isLt
  simp only [BitVec.toNat_ofNat, BitVec.toNat_or, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth, Nat.shiftLeft_eq] at *
  generalize y0.toNat = x0 at *
  generalize y1.toNat = x1 at *
  generalize y2.toNat = x2 at *
  generalize y3.toNat = x3 at *
  generalize y4.toNat = x4 at *
  generalize y5.toNat = x5 at *
  generalize y6.toNat = x6 at *
  generalize y7.toNat = x7 at *
  rw [Nat.mod_eq_of_lt (a := x0) (by omega), Nat.mod_eq_of_lt (a := x1) (by omega),
    Nat.mod_eq_of_lt (a := x2) (by omega), Nat.mod_eq_of_lt (a := x3) (by omega),
    Nat.mod_eq_of_lt (a := x4) (by omega), Nat.mod_eq_of_lt (a := x5) (by omega),
    Nat.mod_eq_of_lt (a := x6) (by omega), Nat.mod_eq_of_lt (a := x7) (by omega),
    Nat.mod_eq_of_lt (a := x1 * 2 ^ 8) (by omega), Nat.mod_eq_of_lt (a := x2 * 2 ^ 16) (by omega),
    Nat.mod_eq_of_lt (a := x3 * 2 ^ 24) (by omega), Nat.mod_eq_of_lt (a := x4 * 2 ^ 32) (by omega),
    Nat.mod_eq_of_lt (a := x5 * 2 ^ 40) (by omega), Nat.mod_eq_of_lt (a := x6 * 2 ^ 48) (by omega),
    Nat.mod_eq_of_lt (a := x7 * 2 ^ 56) (by omega),
    or_mul_eq_add x0 x1 8 (by omega),
    or_mul_eq_add (x0 + x1 * 2 ^ 8) x2 16 (by omega),
    or_mul_eq_add (x0 + x1 * 2 ^ 8 + x2 * 2 ^ 16) x3 24 (by omega),
    or_mul_eq_add (x0 + x1 * 2 ^ 8 + x2 * 2 ^ 16 + x3 * 2 ^ 24) x4 32 (by omega),
    or_mul_eq_add (x0 + x1 * 2 ^ 8 + x2 * 2 ^ 16 + x3 * 2 ^ 24 + x4 * 2 ^ 32) x5 40 (by omega),
    or_mul_eq_add (x0 + x1 * 2 ^ 8 + x2 * 2 ^ 16 + x3 * 2 ^ 24 + x4 * 2 ^ 32 + x5 * 2 ^ 40) x6 48
      (by omega),
    or_mul_eq_add (x0 + x1 * 2 ^ 8 + x2 * 2 ^ 16 + x3 * 2 ^ 24 + x4 * 2 ^ 32 + x5 * 2 ^ 40
      + x6 * 2 ^ 48) x7 56 (by omega)]
  omega

theorem toBitVec_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (b0.toUInt64 ||| b1.toUInt64 <<< 8 ||| b2.toUInt64 <<< 16 ||| b3.toUInt64 <<< 24
      ||| b4.toUInt64 <<< 32 ||| b5.toUInt64 <<< 40 ||| b6.toUInt64 <<< 48
      ||| b7.toUInt64 <<< 56).toBitVec =
    (b0.toBitVec.setWidth 64 ||| b1.toBitVec.setWidth 64 <<< 8
      ||| b2.toBitVec.setWidth 64 <<< 16 ||| b3.toBitVec.setWidth 64 <<< 24
      ||| b4.toBitVec.setWidth 64 <<< 32 ||| b5.toBitVec.setWidth 64 <<< 40
      ||| b6.toBitVec.setWidth 64 <<< 48 ||| b7.toBitVec.setWidth 64 <<< 56) := by
  simp [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft]

/-- A word loaded from `m` is the word `read64` reads from a `BJMem`-related memory. -/
theorem load64Mem_read64 {m : Mem} {am : AMem} (h : BJMem m am) (a v : UInt64)
    (hl : load64Mem m a = some v) : read64 am a.toBitVec = v.toBitVec := by
  simp only [load64Mem, Mem.loadByte, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at hl
  obtain ⟨b0, h0, b1, h1, b2, h2, b3, h3, b4, h4, b5, h5, b6, h6, b7, h7, rfl⟩ := hl
  have e0 := h _ _ h0
  have e1 := h _ _ h1
  have e2 := h _ _ h2
  have e3 := h _ _ h3
  have e4 := h _ _ h4
  have e5 := h _ _ h5
  have e6 := h _ _ h6
  have e7 := h _ _ h7
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat] at e1 e2 e3 e4 e5 e6 e7
  rw [read64, e0, e1, e2, e3, e4, e5, e6, e7, ofNat_bytes, toBitVec_bytes]

theorem toBitVec_ofNat_toNat (x : BitVec 64) : (UInt64.ofNat x.toNat).toBitVec = x := by
  simp

theorem store64_add (m : Mem) (a v : UInt64) (k : Nat) (hk : k < 8) :
    m.store64 a v (a + UInt64.ofNat k) = some (byteAt v k) := by
  match k, hk with
  | 0, _ => simp [Mem.store64, Mem.storeByte]
  | 1, _ => simp [Mem.store64, Mem.storeByte]
  | 2, _ => simp [Mem.store64, Mem.storeByte]
  | 3, _ => simp [Mem.store64, Mem.storeByte]
  | 4, _ => simp [Mem.store64, Mem.storeByte]
  | 5, _ => simp [Mem.store64, Mem.storeByte]
  | 6, _ => simp [Mem.store64, Mem.storeByte]
  | 7, _ => simp [Mem.store64, Mem.storeByte]

theorem store64_of_not (m : Mem) (a v x : UInt64) (hx : ∀ k < 8, x ≠ a + UInt64.ofNat k) :
    m.store64 a v x = m x := by
  have h0 := hx 0 (by omega)
  have h1 := hx 1 (by omega)
  have h2 := hx 2 (by omega)
  have h3 := hx 3 (by omega)
  have h4 := hx 4 (by omega)
  have h5 := hx 5 (by omega)
  have h6 := hx 6 (by omega)
  have h7 := hx 7 (by omega)
  simp only [UInt64.reduceOfNat, UInt64.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7
  simp [Mem.store64, Mem.storeByte, h0, h1, h2, h3, h4, h5, h6, h7]

theorem toBitVec_byteAt (v : UInt64) (k : Nat) (hk : k < 8) :
    (byteAt v k).toBitVec = BitVec.ofNat 8 (v.toNat / 2 ^ (8 * k)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteAt, UInt8.toNat_toBitVec, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  rw [show 8 * k % 2 ^ 64 % 64 = 8 * k by omega]

/-- A store of `v` at `a` agrees with `write64` of the same word at the same address. -/
theorem bjMem_store64 {m : Mem} {am : AMem} (h : BJMem m am) (a v : UInt64) :
    BJMem (m.store64 a v) (write64 am a.toBitVec v.toBitVec) := by
  intro x b hx
  by_cases hin : InRange8 a.toBitVec x.toBitVec
  · have hx' : x = a + UInt64.ofNat (x.toBitVec - a.toBitVec).toNat := by
      apply UInt64.eq_of_toBitVec_eq
      rw [UInt64.toBitVec_add, toBitVec_ofNat_toNat]
      bv_omega
    obtain ⟨k, hk, rfl⟩ : ∃ k < 8, x = a + UInt64.ofNat k := ⟨_, hin, hx'⟩
    rw [store64_add _ _ _ _ hk, Option.some.injEq] at hx
    subst hx
    rw [UInt64.toBitVec_add, UInt64.toBitVec_ofNat', write64_add _ _ _ _ hk,
      toBitVec_byteAt _ _ hk]
    rfl
  · have hne : ∀ k < 8, x ≠ a + UInt64.ofNat k := by
      intro k hk heq
      apply hin
      subst heq
      simp only [InRange8, UInt64.toBitVec_add, UInt64.toBitVec_ofNat']
      rw [toNat_add_sub_self _ _ hk]
      exact hk
    rw [store64_of_not _ _ _ _ hne] at hx
    rw [write64_of_not_inRange _ _ _ _ hin]
    exact h x b hx

/-! ## Carries -/

theorem subBorrow_eq (a b : BitVec 64) :
    subBorrow a b = (if (x86_SUB a b).cf.getD false then 1 else 0, (x86_SUB a b).word) := by
  have hc : (((a - b).toNat : Int) ≠ (a.toNat : Int) - (b.toNat : Int)) ↔
      a.toNat < b.toNat := by
    rw [BitVec.toNat_sub]
    have := a.isLt
    have := b.isLt
    constructor <;> intro h <;> omega
  simp only [subBorrow, x86_SUB, wunsigned, Option.getD_some, BitVec.ult, decide_eq_true_eq,
    hc]

theorem subBorrowIn_eq (a b c : BitVec 64) :
    subBorrowIn a b c = (if (x86_SBB a b (c.getLsbD 0)).cf.getD false then 1 else 0,
      (x86_SBB a b (c.getLsbD 0)).word) := by
  have hsb : ∀ n : Nat, sub_borrow a b n = a - b - BitVec.ofNat 64 n := by
    intro n
    apply BitVec.eq_of_toNat_eq
    have := a.isLt
    have := b.isLt
    simp only [sub_borrow, BitVec.toNat_ofInt, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hcf : ∀ n : Nat, n ≤ 1 → ((((a - b - BitVec.ofNat 64 n).toNat : Int) ≠
      (a.toNat : Int) - ((b.toNat : Int) + (n : Int))) ↔ a.toNat < b.toNat + n) := by
    intro n hn
    rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := a.isLt
    have := b.isLt
    constructor <;> intro h <;> omega
  have hm : (c &&& 1).toNat = c.toNat % 2 := by simp [BitVec.toNat_and]
  have hb : c.getLsbD 0 = decide (c.toNat % 2 = 1) := by
    simp [BitVec.getLsbD, Nat.testBit_zero]
  cases hc : c.getLsbD 0
  · have h1 : c &&& 1 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [hm]
      rw [hb] at hc
      simp at hc ⊢
      omega
    simp only [subBorrowIn, x86_SBB, wunsigned, Option.getD_some, BitVec.ult, decide_eq_true_eq,
      h1, hsb, Bool.false_eq_true, if_false, hcf 0 (by omega)]
    by_cases h : a.toNat < b.toNat <;> simp [h]
  · have h1 : c &&& 1 = 1 := by
      apply BitVec.eq_of_toNat_eq
      rw [hm]
      rw [hb] at hc
      simp at hc ⊢
      omega
    simp only [subBorrowIn, x86_SBB, wunsigned, Option.getD_some, BitVec.ult, decide_eq_true_eq,
      h1, hsb, if_true, hcf 1 (by omega)]
    have he : ((a - b).toNat < (1 : BitVec 64).toNat) = (a.toNat = b.toNat) := by
      apply propext
      rw [BitVec.toNat_sub]
      have := a.isLt
      have := b.isLt
      have : (1 : BitVec 64).toNat = 1 := rfl
      omega
    simp only [he]
    by_cases h : a.toNat < b.toNat
    · simp only [h, show a.toNat ≠ b.toNat by omega, show a.toNat < b.toNat + 1 by omega,
        if_true, if_false]
      rfl
    · by_cases h' : a.toNat = b.toNat
      · simp [h']
      · simp [h, h', show ¬ a.toNat < b.toNat + 1 by omega]

/-! ## One instruction -/

theorem sim_mov {s : BignumState} {sa : AState} (hc : BJCorr s sa) (x : String) (w : BitVec 64)
    (o : JOperand) (ho : o.eval sa.view = w) :
    BJCorr (setReg s x w) (evalInstrA sa (.mov x o)) := by
  obtain ⟨hr, hm⟩ := hc
  refine ⟨?_, hm⟩
  funext y
  show (if y = x then w else s.regs y) = (if y = x then o.eval sa.view else sa.regs y)
  rw [ho, hr]

theorem sim_loadMem {s : BignumState} {sa : AState} (hc : BJCorr s sa) (x b : String) (k : Int)
    (v : UInt64)
    (hl : load64Mem s.mem (UInt64.ofNat (s.regs b + BitVec.ofInt 64 k).toNat) = some v) :
    BJCorr (setReg s x (BitVec.ofNat 64 v.toNat)) (evalInstrA sa (.loadMem x b k)) := by
  obtain ⟨hr, hm⟩ := hc
  have hv := load64Mem_read64 hm _ _ hl
  rw [toBitVec_ofNat_toNat, hr] at hv
  refine ⟨?_, hm⟩
  funext y
  show (if y = x then BitVec.ofNat 64 v.toNat else s.regs y) =
    (if y = x then read64 sa.mem (sa.regs b + BitVec.ofInt 64 k) else sa.regs y)
  rw [hv, hr]
  simp

theorem sim_storeMem {s : BignumState} {sa : AState} (hc : BJCorr s sa) (b src : String)
    (k : Int) :
    BJCorr (storeMem s (UInt64.ofNat (s.regs b + BitVec.ofInt 64 k).toNat)
        (UInt64.ofNat (s.regs src).toNat))
      (evalInstrA sa (.storeMem b k (.reg src))) := by
  obtain ⟨hr, hm⟩ := hc
  refine ⟨hr, ?_⟩
  have := bjMem_store64 hm (UInt64.ofNat (s.regs b + BitVec.ofInt 64 k).toNat)
    (UInt64.ofNat (s.regs src).toNat)
  rw [toBitVec_ofNat_toNat, toBitVec_ofNat_toNat] at this
  rw [hr] at this ⊢
  exact this

theorem sim_logic {s : BignumState} {sa : AState} (hc : BJCorr s sa) (x a b : String)
    (hb : b ≠ x) (op : String → JOperand → JInstr 64)
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hop : ∀ t : JState 64, (evalInstr t (op x (.reg b))).regs =
      fun r => if r = x then f (t.regs x) (t.regs b) else t.regs r)
    (hw : ∀ t : AState, writeAddr t (op x (.reg b)) = none) :
    BJCorr (setReg s x (f (s.regs a) (s.regs b)))
      (runBlockA sa [.mov x (.reg a), op x (.reg b)]) := by
  obtain ⟨hr, hm⟩ := hc
  refine ⟨?_, ?_⟩
  · funext y
    show (if y = x then f (s.regs a) (s.regs b) else s.regs y) =
      (evalInstr (evalInstrA sa (.mov x (.reg a))).view (op x (.reg b))).regs y
    rw [hop]
    simp only [evalInstrA, evalInstr, AState.view, JState.setReg, JOperand.eval, JState.get,
      x86_MOV, if_true, if_neg hb, hr]
    by_cases hy : y = x <;> simp [hy]
  · show BJMem s.mem (evalInstrA (evalInstrA sa (.mov x (.reg a))) (op x (.reg b))).mem
    simp only [evalInstrA, hw]
    exact hm

theorem sim_sub {s : BignumState} {sa : AState} (hc : BJCorr s sa) (cf r a b : String)
    (hrb : r ≠ b) (hcr : cf ≠ r) :
    BJCorr (setReg (setReg s cf (subBorrow (s.regs a) (s.regs b)).1) r
        (subBorrow (s.regs a) (s.regs b)).2)
      (runBlockA sa [.mov r (.reg a), .sub r (.reg b), .setc cf]) := by
  obtain ⟨hr, hm⟩ := hc
  refine ⟨?_, ?_⟩
  · funext y
    rw [subBorrow_eq]
    simp [setReg, evalInstrA, evalInstr, JState.setReg, JState.writeB5W, JState.flagB, x86_MOV,
      AState.view, hr]
    rw [if_neg (Ne.symm hrb)]
    by_cases h1 : y = r <;> by_cases h2 : y = cf <;> simp only [h1, h2, if_true, if_false] <;>
      (simp_all; try congr)
  · simpa [setReg, evalInstrA, writeAddr] using hm

theorem sim_sbb {s : BignumState} {sa : AState} (hc : BJCorr s sa) (cf r a b c : String)
    (hrb : r ≠ b) (hcr : cf ≠ r) :
    BJCorr (setReg (setReg s cf (subBorrowIn (s.regs a) (s.regs b) (s.regs c)).1) r
        (subBorrowIn (s.regs a) (s.regs b) (s.regs c)).2)
      (runBlockA sa [.bt c (.imm 0), .mov r (.reg a), .sbb r (.reg b), .setc cf]) := by
  obtain ⟨hr, hm⟩ := hc
  refine ⟨?_, ?_⟩
  · funext y
    rw [subBorrowIn_eq]
    simp [setReg, evalInstrA, evalInstr, JState.setReg, JState.writeB5W, JState.flagB, x86_MOV,
      x86_BT, wbit, AState.view, hr]
    rw [if_neg (Ne.symm hrb)]
    by_cases h1 : y = r <;> by_cases h2 : y = cf <;> simp only [h1, h2, if_true, if_false] <;>
      (simp_all; try congr)
  · simpa [setReg, evalInstrA, writeAddr] using hm

theorem toJ_sim {i : InstrR} {js : List (JInstr 64)} {s s' : BignumState} {sa : AState}
    (h : toJ i = some js) (hc : BJCorr s sa) (he : execInstr s i = some s') :
    BJCorr s' (runBlockA sa js) := by
  unfold toJ at h
  split at h
  · rename_i x _ _ e
    unfold assignJ at h
    split at h
    · cases h
      simp [execInstr, evalPExpr] at he
      subst he
      exact sim_mov hc _ _ _ (by simp only [JOperand.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    · cases h
      simp [execInstr, evalPExpr] at he
      subst he
      exact sim_mov hc _ _ _ (by simp [AState.view, hc.1])
    · cases h
      simp only [execInstr, evalPExpr, resolveAddr, Option.bind_eq_bind, Option.bind_some,
        Option.bind_eq_some_iff, Option.some.injEq] at he
      obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := he
      exact sim_loadMem hc _ _ _ v hv
    · unfold logicJ at h
      split at h
      · cases h
      · rename_i hb
        cases h
        simp [execInstr, evalPExpr] at he
        subst he
        exact sim_logic hc _ _ _ hb _ (· &&& ·) (fun _ => rfl) (fun _ => rfl)
    · unfold logicJ at h
      split at h
      · cases h
      · rename_i hb
        cases h
        simp [execInstr, evalPExpr] at he
        subst he
        exact sim_logic hc _ _ _ hb _ (· ||| ·) (fun _ => rfl) (fun _ => rfl)
    · unfold logicJ at h
      split at h
      · cases h
      · rename_i hb
        cases h
        simp [execInstr, evalPExpr] at he
        subst he
        exact sim_logic hc _ _ _ hb _ (· ^^^ ·) (fun _ => rfl) (fun _ => rfl)
    · cases h
  · cases h
    simp only [execInstr, evalPExpr, resolveAddr, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq] at he
    subst he
    exact sim_storeMem hc _ _ _
  · unfold opnJ at h
    split at h
    · split at h
      · split at h
        · rename_i hn
          unfold subJ at h
          split at h
          · cases h
          · rename_i hne
            cases h
            simp [execInstr, hn, evalPExpr, writeSubBundle] at he
            subst he
            exact sim_sub hc _ _ _ _ (fun e => hne (Or.inl e)) (fun e => hne (Or.inr e))
        · cases h
      · split at h
        · rename_i hn
          unfold sbbJ at h
          split at h
          · cases h
          · rename_i hne
            cases h
            simp [execInstr, hn, evalPExpr, writeSubBundle] at he
            subst he
            exact sim_sbb hc _ _ _ _ _ (fun e => hne (Or.inl e)) (fun e => hne (Or.inr e))
        · cases h
      · cases h
    · cases h
  · cases h

/-! ## Bodies -/

/-- A translated body preserves `BJCorr`. -/
theorem bignumExec_runBlockA_sim : ∀ (body : List InstrR) (blk : List (JInstr 64))
    (s s' : BignumState) (sa : AState), toJBlock body = some blk → BJCorr s sa →
    bignumExec body s = some s' → BJCorr s' (runBlockA sa blk)
  | [], blk, s, s', sa, h, hc, he => by
    simp only [toJBlock, Option.some.injEq] at h
    simp only [bignumExec, Option.some.injEq] at he
    subst h he
    exact hc
  | i :: is, blk, s, s', sa, h, hc, he => by
    simp only [toJBlock, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨js, hjs, jss, hjss, rfl⟩ := h
    simp only [bignumExec] at he
    split at he
    · rename_i s1 h1
      rw [runBlockA_append]
      exact bignumExec_runBlockA_sim is jss s1 s' _ hjss (toJ_sim hjs hc h1) he
    · simp at he

/-! ## Progress on a total memory -/

theorem load64Mem_of_memTotal {m : Mem} (ht : MemTotal m) (a : UInt64) :
    ∃ v, load64Mem m a = some v := by
  obtain ⟨b0, h0⟩ := Option.isSome_iff_exists.1 (ht a)
  obtain ⟨b1, h1⟩ := Option.isSome_iff_exists.1 (ht (a + 1))
  obtain ⟨b2, h2⟩ := Option.isSome_iff_exists.1 (ht (a + 2))
  obtain ⟨b3, h3⟩ := Option.isSome_iff_exists.1 (ht (a + 3))
  obtain ⟨b4, h4⟩ := Option.isSome_iff_exists.1 (ht (a + 4))
  obtain ⟨b5, h5⟩ := Option.isSome_iff_exists.1 (ht (a + 5))
  obtain ⟨b6, h6⟩ := Option.isSome_iff_exists.1 (ht (a + 6))
  obtain ⟨b7, h7⟩ := Option.isSome_iff_exists.1 (ht (a + 7))
  simp [load64Mem, Mem.loadByte, h0, h1, h2, h3, h4, h5, h6, h7]

theorem memTotal_store64 {m : Mem} (ht : MemTotal m) (a v : UInt64) :
    MemTotal (m.store64 a v) := by
  intro x
  simp only [Mem.store64, Mem.storeByte]
  split_ifs <;> simp [ht x]

/-- On a total memory, a translatable instruction runs, to a total memory. -/
theorem toJ_progress {i : InstrR} {js : List (JInstr 64)} {s : BignumState}
    (h : toJ i = some js) (ht : MemTotal s.mem) :
    ∃ s', execInstr s i = some s' ∧ MemTotal s'.mem := by
  unfold toJ at h
  split at h
  · unfold assignJ at h
    split at h
    · simpa [execInstr, evalPExpr, setReg] using ht
    · simpa [execInstr, evalPExpr, setReg] using ht
    · rename_i b k
      obtain ⟨v, hv⟩ := load64Mem_of_memTotal ht
        (UInt64.ofNat (s.regs b.var.vname + BitVec.ofInt 64 k).toNat)
      simp only [execInstr, evalPExpr, resolveAddr, Option.bind_eq_bind, hv, Option.bind_some]
      exact ⟨_, rfl, ht⟩
    · simpa [execInstr, evalPExpr, setReg] using ht
    · simpa [execInstr, evalPExpr, setReg] using ht
    · simpa [execInstr, evalPExpr, setReg] using ht
    · cases h
  · simpa [execInstr, evalPExpr, resolveAddr, storeMem] using memTotal_store64 ht _ _
  · unfold opnJ at h
    split at h
    · split at h
      · split at h
        · rename_i hn
          simpa [execInstr, hn, evalPExpr, writeSubBundle, setReg] using ht
        · cases h
      · split at h
        · rename_i hn
          simpa [execInstr, hn, evalPExpr, writeSubBundle, setReg] using ht
        · cases h
      · cases h
    · cases h
  · cases h

/-- On a total memory, a translatable body runs, to a total memory. -/
theorem bignumExec_progress : ∀ (body : List InstrR) (blk : List (JInstr 64))
    (s : BignumState), toJBlock body = some blk → MemTotal s.mem →
    ∃ s', bignumExec body s = some s' ∧ MemTotal s'.mem
  | [], _, s, _, ht => ⟨s, rfl, ht⟩
  | i :: is, blk, s, h, ht => by
    simp only [toJBlock, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨js, hjs, jss, hjss, rfl⟩ := h
    obtain ⟨s1, h1, ht1⟩ := toJ_progress hjs ht
    obtain ⟨s', h', ht'⟩ := bignumExec_progress is jss s1 hjss ht1
    exact ⟨s', by simp [bignumExec, h1, h'], ht'⟩

end CatCrypt.Crypto.Jasmin.BignumToJ
