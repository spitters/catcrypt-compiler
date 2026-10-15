/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemIdx

/-!
# Address memory for the `Linstr` machine: lowering memrefs to pointers

The typed machine over `LstateM` keys its arrays by name: `LOADIDX`/`STOREIDX` on the
operand `.arrIdx A idx _` read and write the array `larr A`. The physical export addresses
an array through a pointer: it keeps the pointer of each array argument in a frame slot,
reloads it into a scratch register before every access, and addresses
`(%scratch, %idx, 8)`. This module defines a machine with byte-addressed memory that runs
the pointer form, and proves that it simulates the name-keyed machine on the access
pattern of the export.

## The address machine

`LstateA` is a register file `LstateN` and a byte memory `AMem` of `Ascent.AddrMem`.
`fstepA frame` is the extended straight step `fstepF` with memory read at addresses:

* `MOVQ dst, q` or `MOV:64 dst, q` with `frame q = some a` loads the word at `a` into `dst`;
* `MOVQ q, src` or `MOV:64 q, src` with `frame q = some a` stores `src` at `a`, a one-bit
  `src` zero-extended to 64 bits;
* `CMP:64 d, x, q` with `frame q = some a` compares `x` with the word at `a`;
* `CMOV:64 d, [c, x, y]` with a frame slot among `x`, `y`, `d` selects between the words of
  `x` and `y` into the register `d` or the frame word of `d`;
* `ADCX:64`/`ADCXHI:64` with a frame slot among its operands reads a slot word source as the
  word at its address and a slot carry-in as the low bit of that word;
* `MOV:64 q, #v` writes the word of `v` at the address of `q`, and `MOV q, #v` its low
  32 bits;
* `LOADIDX dst, (base, idx, sc)` loads the word at `reg base + sc · reg idx`;
* `STOREIDX _, (base, idx, sc), val` stores `val` at `reg base + sc · reg idx`;
* `LOAD:64 d, mem.B.off` and `STORE:64 mem.B.off, v` load and store the word at
  `reg B + off`, a one-bit `v` zero-extended to 64 bits, and `LEA:64 d, mem.B.off` writes `reg B + off` to `d`;
* every other register-tagged instruction is `fstepF` on the register file.

`runStraightA` and `runBoundedStraightA` are the folds `runStraightF` and
`runBoundedStraightF` over `fstepA`.

## The refinement relation

A `Layout` gives each array name a base address, a word count and the name of the frame
slot that holds its pointer. `Rel L frame scr K s sa` relates a name-keyed state `s` and
an address state `sa`:

* the register files agree off the scratch register `scr` (`EqOff`);
* for each cell `(A, j)` of the cell predicate `K`, `j < L.len A`, the array `A` has
  shape `(64, L.len A)`, and the word at `L.base A + 8 · j` is its element `j`;
* the frame slot of each array holds the base address of the array.

`Layout.Sep` is the separation condition: two declared cells have equal addresses or
disjoint eight-byte ranges, and every declared cell is disjoint from every pointer slot.
Two names with the same base address denote one region; `Layout.sep_of_regions` derives
the cell condition from regions that are pairwise equal-based or disjoint.

The name-keyed store `dst := A[j ↦ v]` writes a new array under the name `dst`; `dst` and
`A` must name one region (`L.base dst = L.base A`, `L.len dst = L.len A`), and `dst = A`
is the in-place store. It replaces `K` by `afterStore L K dst A j`: under `dst`, the
written cell and the cells of `A` in `K` at another address; under every other name, the
cells of `K` at another address. When two names share a base, a store through one name
removes the cell of the other name at that address, since the name-keyed array of the
other name keeps its previous element.

## Main results

* `load_sim`, `store_sim`: one name-keyed `LOADIDX`/`STOREIDX` on array `A` is simulated
  by the reload of the pointer of `A` into `scr` followed by the access through `scr`.
* `reg_sim`: a register instruction that is independent of `scr` (`RegCompat`) is
  simulated by itself. `regCompat_cmp` and `regCompat_mov` are the flag compare and the
  register copy; `regCompat_of_unary` is an instruction that reads one register and writes
  a function of it, with instances `regCompat_addImmI` and `regCompat_subImmI` for the
  index increment and the counter decrement.
* `SimSeg`: the segment simulation quadruple, with `SimSeg.nil`, `SimSeg.append`,
  `SimSeg.weaken`, and the instruction rules `SimSeg.load`, `SimSeg.store`, `SimSeg.reg`.
* `runBounded_sim`: a trip-indexed family of segment simulations gives the simulation of
  the bounded fold `runBoundedStraightF` by `runBoundedStraightA`.
* `guardedFlagLoop_addr_sim`: the flag machine `lsemFuelMemF` halts on the guarded loop
  skeleton in a state that agrees on registers and arrays with the fold's final state, and
  that state is related to the final state of the address fold.
* `saveArgs_run`, `rel_of_entry`: the entry block that stores the pointer arguments into
  their slots establishes the slot component of `Rel`.
* `copyTrip_simSeg`: the trip `x := A[idx]; R := R[idx ↦ x]; idx += 1; n -= 1` with `A` and
  `R` at one region, from the cells `copyK L A R t` to `copyK L A R (t + 1)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemIdx (disjoint8_of_toNat)

/-! ## 1. The address machine -/

/-- A register file, a byte-addressed memory and the carry and overflow flags. -/
structure LstateA where
  /-- The width-tagged register file. -/
  reg : LstateN
  /-- The byte memory. -/
  mem : AMem
  /-- The carry flag. -/
  cf : Bool := false
  /-- The overflow flag. -/
  of : Bool := false

/-- Set the program counter. -/
def LstateA.setLpc (sa : LstateA) (pc : Nat) : LstateA :=
  { sa with reg := { sa.reg with lpc := pc } }

/-- The wire form `Lopn [.reg dst] m [.reg src]` of a 64-bit move, `m` one of `MOVQ` and
    `MOV:64`, as `(dst, src)`. -/
def slotMov? : LinstrR → Option (String × String)
  | .Lopn [.reg dst] opn [.reg src] =>
      if opn = "MOVQ" ∨ opn = "MOV:64" then some (dst, src) else none
  | _ => none

/-- The wire form `Lopn [.reg d] "CMP:64" [.reg x, .reg q]` of a register compare, as
    `(d, x, q)`. -/
def slotCmp? : LinstrR → Option (String × String × String)
  | .Lopn [.reg d] opn [.reg x, .reg q] => if opn = "CMP:64" then some (d, x, q) else none
  | _ => none

/-- The wire form `Lopn [.reg dst] "LOADIDX" [.arrIdx base idx sc]`, as
    `(dst, base, idx, sc)`. -/
def loadIdxA? : LinstrR → Option (String × String × String × Nat)
  | .Lopn [.reg dst] opn [.arrIdx base idx sc] =>
      if opn = "LOADIDX" then some (dst, base, idx, sc) else none
  | _ => none

/-- The wire form `Lopn [.reg _] "STOREIDX" [.arrIdx base idx sc, .reg val]`, as
    `(base, idx, sc, val)`. -/
def storeIdxA? : LinstrR → Option (String × String × Nat × String)
  | .Lopn [.reg _] opn [.arrIdx base idx sc, .reg val] =>
      if opn = "STOREIDX" then some (base, idx, sc, val) else none
  | _ => none

/-- The base register and the byte offset of a cell name `mem.<B>.<off>`
    (`JasminLprogExport.memName`); `none` for any other name. -/
def cellParts? (n : String) : Option (String × Nat) :=
  if hasPrefix n "mem." then
    match (n.toList.drop 4).span (· != '.') with
    | (base, '.' :: off) => (natOfDigits? off).map fun o => (String.ofList base, o)
    | _ => none
  else none

/-- An instruction on a cell name `mem.B.off`: a whole-word load of `[B + off]` into `d`, a
    whole-word store of `v` to `[B + off]`, or the address `B + off` into `d`. -/
inductive CellOp where
  /-- `LOAD:64 d, mem.B.off`: `d := [B + off]`. -/
  | ld (d b : String) (off : Nat)
  /-- `STORE:64 mem.B.off, v`: `[B + off] := v`. -/
  | st (b : String) (off : Nat) (v : String)
  /-- `LEA:64 d, mem.B.off`: `d := B + off`. -/
  | lea (d b : String) (off : Nat)

/-- The wire forms `Lopn [.reg d] "LOAD:64" [.reg n]`, `Lopn [.reg n] "STORE:64" [.reg v]` and
    `Lopn [.reg d] "LEA:64" [.reg n]` with `n` a cell name, as their cell operation. -/
def cellA? : LinstrR → Option CellOp
  | .Lopn [.reg d] opn [.reg n] =>
      if opn = "LOAD:64" then (cellParts? n).map fun p => .ld d p.1 p.2
      else if opn = "STORE:64" then (cellParts? d).map fun p => .st p.1 p.2 n
      else if opn = "LEA:64" then (cellParts? n).map fun p => .lea d p.1 p.2
      else none
  | _ => none

/-- The carry-chain add `ADCX:64 d, a, s, c` or its carry-out binding `ADCXHI:64 d, a, s, c`
    with a frame slot among `d`, `a`, `s`, `c`, as `(is the add, d, a, s, c)`. -/
def slotCarry? (frame : String → Option (BitVec 64)) :
    LinstrR → Option (Bool × String × String × String × String)
  | .Lopn [.reg d] o [.reg a, .reg s, .reg c] =>
      if (o == "ADCX:64" || o == "ADCXHI:64")
          && ((frame d).isSome || (frame a).isSome || (frame s).isSome || (frame c).isSome) then
        some (o == "ADCX:64", d, a, s, c)
      else none
  | _ => none

/-- The immediate move `MOV:64 q, #v` or `MOV q, #v` into a frame slot `q`, as the slot's
    address and `v`. -/
def slotImm? (frame : String → Option (BitVec 64)) : LinstrR → Option (BitVec 64 × Nat)
  | .Lopn [.reg q] o [.imm v] =>
      if o = "MOV:64" ∨ o = "MOV" then (frame q).map fun a => (a, v) else none
  | _ => none

/-- The frame word after an immediate move of `v` into a frame word holding `old`: the 64-bit
    word of `v` for `MOV:64`; for the 32-bit `MOV` (`movl $v, off(%rsp)`), the low 32 bits of
    `v` below the high 32 bits of `old`. -/
def immWordA : LinstrR → BitVec 64 → Nat → BitVec 64
  | .Lopn _ o _, old, v =>
      if o = "MOV" then (old &&& 0xFFFFFFFF00000000#64) ||| BitVec.ofNat 64 (v % 2 ^ 32)
      else BitVec.ofNat 64 v
  | _, _, v => BitVec.ofNat 64 v

/-- The select `CMOV:64 d, [c, a, b]` with a frame slot among the destination `d` and the
    values `a`, `b`, as `(d, c, a, b)`. -/
def slotCmov? (frame : String → Option (BitVec 64)) :
    LinstrR → Option (String × String × String × String)
  | .Lopn [.reg d] o [.reg c, .reg a, .reg b] =>
      if o == "CMOV:64" && ((frame d).isSome || (frame a).isSome || (frame b).isSome) then
        some (d, c, a, b)
      else none
  | _ => none

/-- The word a name holds on the address machine: the memory word at its frame address for a
    frame slot, its 64-bit register value otherwise. -/
def wordA (frame : String → Option (BitVec 64)) (sa : LstateA) (x : String) :
    Option (BitVec 64) :=
  match frame x with
  | some ad => some (read64 sa.mem ad)
  | none => sa.reg.getW x 64

/-- The bit a carry-in holds on the address machine: the low bit of the memory word at its
    frame address for a frame slot (`bt $0` of the reloaded word), its one-bit register value
    otherwise. -/
def bitA (frame : String → Option (BitVec 64)) (sa : LstateA) (x : String) :
    Option (BitVec 1) :=
  match frame x with
  | some ad => some ((read64 sa.mem ad).setWidth 1)
  | none => sa.reg.getW x 1

theorem bitA_of_none {frame : String → Option (BitVec 64)} {x : String} (h : frame x = none)
    (sa : LstateA) : bitA frame sa x = sa.reg.getW x 1 := by
  simp [bitA, h]

/-- The low bit of the frame word after the 32-bit immediate move `MOV q, #v` is the low bit
    of `v`. -/
theorem immWordA_mov_setWidth (ds ss : List LOperand) (old : BitVec 64) (v : Nat) :
    (immWordA (.Lopn ds "MOV" ss) old v).setWidth 1 = BitVec.ofNat 1 v := by
  simp only [immWordA, if_true]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  have e : BitVec.ofNat 1 (v % 4294967296) = BitVec.ofNat 1 v := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  simp [e]

/-- The frame word after `setc` of the bit `c` into the frame word holding `old`
    (`setc off(%rsp)`): the low byte is the zero-extension of `c`, the high 56 bits are those
    of `old`. -/
def setcWordA (old : BitVec 64) (c : BitVec 1) : BitVec 64 :=
  (old &&& 0xFFFFFFFFFFFFFF00#64) ||| c.setWidth 64

/-- The low bit of the frame word after `setc` of `c` is `c`. -/
theorem setcWordA_setWidth (old : BitVec 64) (c : BitVec 1) :
    (setcWordA old c).setWidth 1 = c := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  simp [setcWordA]

/-- The register-file step: `fstepF` on a state with the given registers and flags. -/
def regStepA (i : LinstrRM) (sa : LstateA) (zf : Bool) : Option (LstateA × Bool) :=
  (fstepF i { reg := sa.reg, cf := sa.cf, of := sa.of } zf).map fun bz =>
    ({ sa with reg := bz.1.reg, cf := bz.1.cf, of := bz.1.of }, bz.2)

/-- One step of the address machine. `frame` maps a frame-slot name to its address. A move
    from or to a frame slot and a compare against one read or write the memory at the
    slot's address, a store of a one-bit register writing its zero-extension (the word of
    `mov $0, r; set<cc> r8b; mov r, off(%rsp)`); a whole-word access of a cell `mem.B.off`
    reads or writes the memory at the address in `B` plus `off`, a store of a one-bit
    register writing its zero-extension; the address of a cell `LEA:64 d, mem.B.off` writes
    the address in `B` plus `off` to `d`, with no memory access; a carry-chain add or carry-out binding with a frame-slot
    operand reads its slot word sources and a slot carry-in (the low bit of the word) at the
    slot's address and writes a slot destination at the slot's address, the whole word for
    the add and the low byte (`setcWordA`) for the carry-out binding; an immediate move
    into a frame slot writes the immediate at the slot's address, all 64 bits for `MOV:64`
    and the low 32 bits for `MOV`; a select with a frame-slot value or destination reads that
    value and writes that destination at the slot's address. -/
def fstepA (frame : String → Option (BitVec 64)) (i : LinstrRM) (sa : LstateA) (zf : Bool) :
    Option (LstateA × Bool) :=
  match i.snd with
  | .load _ _ =>
      match loadIdxA? i.fst with
      | some (dst, base, idx, sc) =>
          match sa.reg.getW base 64, sa.reg.getW idx 64 with
          | some p, some vi =>
              some ({ sa with reg := (sa.reg.setReg dst
                (read64 sa.mem (p + BitVec.ofNat 64 (sc * vi.toNat)))).nextPc }, zf)
          | _, _ => none
      | none => none
  | .store _ _ =>
      match storeIdxA? i.fst with
      | some (base, idx, sc, val) =>
          match sa.reg.getW base 64, sa.reg.getW idx 64, sa.reg.getW val 64 with
          | some p, some vi, some v =>
              some ({ sa with
                reg := sa.reg.nextPc
                mem := write64 sa.mem (p + BitVec.ofNat 64 (sc * vi.toNat)) v }, zf)
          | _, _, _ => none
      | none => none
  | .reg _ =>
      match slotMov? i.fst with
      | some (dst, src) =>
          match frame src, frame dst with
          | some a, _ => some ({ sa with reg := (sa.reg.setReg dst (read64 sa.mem a)).nextPc }, zf)
          | none, some a =>
              match sa.reg.getW src 64 with
              | some v => some ({ sa with reg := sa.reg.nextPc, mem := write64 sa.mem a v }, zf)
              | none =>
                  match sa.reg.getW src 1 with
                  | some b => some ({ sa with
                      reg := sa.reg.nextPc
                      mem := write64 sa.mem a (b.setWidth 64) }, zf)
                  | none => none
          | none, none => regStepA i sa zf
      | none =>
          match slotCmp? i.fst with
          | some (d, x, q) =>
              match frame q with
              | some a =>
                  regStepA (.Lopn [.reg d] "CMP:64" [.reg x, .imm (read64 sa.mem a).toNat],
                    i.snd) sa zf
              | none => regStepA i sa zf
          | none =>
              match cellA? i.fst with
              | some (.ld d b off) =>
                  match sa.reg.getW b 64 with
                  | some p => some ({ sa with reg := (sa.reg.setReg d
                      (read64 sa.mem (p + BitVec.ofNat 64 off))).nextPc }, zf)
                  | none => none
              | some (.st b off v) =>
                  match sa.reg.getW b 64, sa.reg.getW v 64 with
                  | some p, some x =>
                      some ({ sa with
                        reg := sa.reg.nextPc
                        mem := write64 sa.mem (p + BitVec.ofNat 64 off) x }, zf)
                  | some p, none =>
                      match sa.reg.getW v 1 with
                      | some c =>
                          some ({ sa with
                            reg := sa.reg.nextPc
                            mem := write64 sa.mem (p + BitVec.ofNat 64 off) (c.setWidth 64) }, zf)
                      | none => none
                  | none, _ => none
              | some (.lea d b off) =>
                  match sa.reg.getW b 64 with
                  | some p => some ({ sa with reg := (sa.reg.setReg d
                      (p + BitVec.ofNat 64 off)).nextPc }, zf)
                  | none => none
              | none =>
                  match slotCarry? frame i.fst with
                  | some (lo, d, a, s, c) =>
                      match wordA frame sa a, wordA frame sa s, bitA frame sa c with
                      | some va, some vb, some vc =>
                          if lo then
                            match frame d with
                            | some ad =>
                                some ({ sa with
                                  reg := sa.reg.nextPc
                                  mem := write64 sa.mem ad (addCarryWord va vb vc) }, zf)
                            | none =>
                                some ({ sa with
                                  reg := (sa.reg.setReg d (addCarryWord va vb vc)).nextPc }, zf)
                          else
                            match frame d with
                            | some ad =>
                                some ({ sa with
                                  reg := sa.reg.nextPc
                                  mem := write64 sa.mem ad
                                    (setcWordA (read64 sa.mem ad) (carryOutBit va vb vc)) }, zf)
                            | none =>
                                some ({ sa with
                                  reg := (sa.reg.setReg d (carryOutBit va vb vc)).nextPc }, zf)
                      | _, _, _ => none
                  | none =>
                      match slotImm? frame i.fst with
                      | some (a, v) =>
                          some ({ sa with
                            reg := sa.reg.nextPc
                            mem := write64 sa.mem a (immWordA i.fst (read64 sa.mem a) v) }, zf)
                      | none =>
                          match slotCmov? frame i.fst with
                          | some (d, c, a, b) =>
                              match sa.reg.getW c 1, wordA frame sa a, wordA frame sa b with
                              | some vc, some va, some vb =>
                                  match frame d with
                                  | some ad =>
                                      some ({ sa with
                                        reg := sa.reg.nextPc
                                        mem := write64 sa.mem ad (selectW vc va vb) }, zf)
                                  | none =>
                                      some ({ sa with
                                        reg := (sa.reg.setReg d (selectW vc va vb)).nextPc }, zf)
                              | _, _, _ => none
                          | none => regStepA i sa zf
  | _ => none

/-- **A frame-word store of a one-bit register.** `MOVQ q, S` or `MOV:64 q, S`, `q` a frame
    slot and `S` a register holding the bit `b`, writes the zero-extension of `b` at the
    address of `q`. -/
theorem fstepA_slotStore1 (frame : String → Option (BitVec 64)) {x : LinstrR} {q S : String}
    (h : slotMov? x = some (q, S)) (hS : frame S = none) {a : BitVec 64} (ha : frame q = some a)
    (sa : LstateA) (zf : Bool) {b : BitVec 1} (hb : sa.reg.lvm S = ⟨1, b⟩) :
    fstepA frame (x, .reg none) sa zf
      = some ({ sa with reg := sa.reg.nextPc, mem := write64 sa.mem a (b.setWidth 64) }, zf) := by
  have h64 : sa.reg.getW S 64 = none := by simp [LstateN.getW, hb]
  have h1 : sa.reg.getW S 1 = some b := getW_eq_some_iff.mpr hb
  simp [fstepA, h, ha, hS, h64, h1]

/-- **The carry-chain add with a frame-slot operand.** `ADCX:64 D, A, S, C`, one of `D`,
    `A`, `S`, `C` a frame slot, writes `addCarryWord` of the words of `A`, `S` and the carry-in
    bit of `C` (`bitA`) to the slot of `D` or to the register `D`. -/
theorem fstepA_adcxSlotBit (frame : String → Option (BitVec 64)) (D A S C : String)
    (sa : LstateA) (zf : Bool)
    (hsl : ((frame D).isSome || (frame A).isSome || (frame S).isSome || (frame C).isSome)
      = true)
    {va vb : BitVec 64} (hA : wordA frame sa A = some va) (hS : wordA frame sa S = some vb) :
    fstepA frame (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C], .reg none) sa zf
      = (bitA frame sa C).map fun vc =>
          ((match frame D with
            | some ad => { sa with
                reg := sa.reg.nextPc
                mem := write64 sa.mem ad (addCarryWord va vb vc) }
            | none => { sa with reg := (sa.reg.setReg D (addCarryWord va vb vc)).nextPc }), zf) := by
  cases hc : bitA frame sa C <;> cases hD : frame D <;>
    simp_all [fstepA, slotMov?, slotCmp?, cellA?, slotCarry?]

/-- **The carry-chain add with a frame-slot word operand and a register carry-in.**
    `ADCX:64 D, A, S, C`, one of `D`, `A`, `S` a frame slot and `C` a register, writes
    `addCarryWord` of the words of `A`, `S` and the one-bit `C` to the slot of `D` or to the
    register `D`. -/
theorem fstepA_adcxSlot (frame : String → Option (BitVec 64)) (D A S C : String)
    (sa : LstateA) (zf : Bool)
    (hsl : ((frame D).isSome || (frame A).isSome || (frame S).isSome) = true)
    {va vb : BitVec 64} (hA : wordA frame sa A = some va) (hS : wordA frame sa S = some vb)
    (hC : frame C = none) :
    fstepA frame (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C], .reg none) sa zf
      = (sa.reg.getW C 1).map fun vc =>
          ((match frame D with
            | some ad => { sa with
                reg := sa.reg.nextPc
                mem := write64 sa.mem ad (addCarryWord va vb vc) }
            | none => { sa with reg := (sa.reg.setReg D (addCarryWord va vb vc)).nextPc }), zf) := by
  rw [fstepA_adcxSlotBit frame D A S C sa zf (by simp [hsl]) hA hS, bitA_of_none hC]

/-- **The carry-out binding with a frame-slot operand.** `ADCXHI:64 O, A, S, C`, one of `O`,
    `A`, `S`, `C` a frame slot, writes the one-bit `carryOutBit` of the words of `A`, `S` and
    the carry-in bit of `C` (`bitA`) into the low byte of the slot of `O` (`setcWordA`) or to
    the register `O`. -/
theorem fstepA_adcxhiSlotBit (frame : String → Option (BitVec 64)) (O A S C : String)
    (sa : LstateA) (zf : Bool)
    (hsl : ((frame O).isSome || (frame A).isSome || (frame S).isSome || (frame C).isSome)
      = true)
    {va vb : BitVec 64} (hA : wordA frame sa A = some va) (hS : wordA frame sa S = some vb) :
    fstepA frame (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C], .reg none) sa zf
      = (bitA frame sa C).map fun vc =>
          ((match frame O with
            | some ad => { sa with
                reg := sa.reg.nextPc
                mem := write64 sa.mem ad (setcWordA (read64 sa.mem ad) (carryOutBit va vb vc)) }
            | none => { sa with reg := (sa.reg.setReg O (carryOutBit va vb vc)).nextPc }), zf) := by
  cases hc : bitA frame sa C <;> cases hO : frame O <;>
    simp_all [fstepA, slotMov?, slotCmp?, cellA?, slotCarry?]

/-- **The carry-out binding into a register with a frame-slot word source and a register
    carry-in.** `ADCXHI:64 O, A, S, C`, `O` and `C` registers and one of `A`, `S` a frame slot,
    writes the one-bit `carryOutBit` of the words of `A`, `S` and the one-bit `C` to `O`. -/
theorem fstepA_adcxhiSlot (frame : String → Option (BitVec 64)) (O A S C : String)
    (sa : LstateA) (zf : Bool)
    (hsl : ((frame O).isSome || (frame A).isSome || (frame S).isSome) = true)
    {va vb : BitVec 64} (hA : wordA frame sa A = some va) (hS : wordA frame sa S = some vb)
    (hC : frame C = none) (hO : frame O = none) :
    fstepA frame (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C], .reg none) sa zf
      = (sa.reg.getW C 1).map fun vc =>
          ({ sa with reg := (sa.reg.setReg O (carryOutBit va vb vc)).nextPc }, zf) := by
  rw [fstepA_adcxhiSlotBit frame O A S C sa zf (by simp [hsl]) hA hS, bitA_of_none hC, hO]

/-- **The cell load.** `LOAD:64 D, n`, `n` the cell `[B + off]`, writes the word at the
    address in `B` plus `off` to `D`. -/
theorem fstepA_ldm (frame : String → Option (BitVec 64)) {D n B : String} {off : Nat}
    (hn : cellParts? n = some (B, off)) {sa : LstateA} {p : BitVec 64}
    (hB : sa.reg.getW B 64 = some p) (zf : Bool) :
    fstepA frame (.Lopn [.reg D] "LOAD:64" [.reg n], .reg none) sa zf
      = some ({ sa with reg := (sa.reg.setReg D
          (read64 sa.mem (p + BitVec.ofNat 64 off))).nextPc }, zf) := by
  simp [fstepA, slotMov?, slotCmp?, cellA?, hn, hB]

/-- **The cell store.** `STORE:64 n, S`, `n` the cell `[B + off]`, writes the value of `S`
    to the address in `B` plus `off`. -/
theorem fstepA_stm (frame : String → Option (BitVec 64)) {n S B : String} {off : Nat}
    (hn : cellParts? n = some (B, off)) {sa : LstateA} {p v : BitVec 64}
    (hB : sa.reg.getW B 64 = some p) (hS : sa.reg.getW S 64 = some v) (zf : Bool) :
    fstepA frame (.Lopn [.reg n] "STORE:64" [.reg S], .reg none) sa zf
      = some ({ sa with
          reg := sa.reg.nextPc
          mem := write64 sa.mem (p + BitVec.ofNat 64 off) v }, zf) := by
  simp [fstepA, slotMov?, slotCmp?, cellA?, hn, hB, hS]

/-- **The address of a cell.** `LEA:64 D, n`, `n` the cell `[B + off]`, writes the address in
    `B` plus `off` to `D`; the memory and the flags are unchanged. -/
theorem fstepA_lea (frame : String → Option (BitVec 64)) {D n B : String} {off : Nat}
    (hn : cellParts? n = some (B, off)) {sa : LstateA} {p : BitVec 64}
    (hB : sa.reg.getW B 64 = some p) (zf : Bool) :
    fstepA frame (.Lopn [.reg D] "LEA:64" [.reg n], .reg none) sa zf
      = some ({ sa with reg := (sa.reg.setReg D (p + BitVec.ofNat 64 off)).nextPc }, zf) := by
  simp [fstepA, slotMov?, slotCmp?, cellA?, hn, hB]

/-- **The immediate store into a frame slot.** `MOV:64 q, #v` with `q` a frame slot at `a`
    writes the 64-bit word of `v` at `a`. -/
theorem fstepA_slotImm (frame : String → Option (BitVec 64)) {q : String} {a : BitVec 64}
    (hq : frame q = some a) (v : Nat) (tag : Option Nat) (sa : LstateA) (zf : Bool) :
    fstepA frame (.Lopn [.reg q] "MOV:64" [.imm v], .reg tag) sa zf
      = some ({ sa with reg := sa.reg.nextPc, mem := write64 sa.mem a (BitVec.ofNat 64 v) },
          zf) := by
  simp [fstepA, slotMov?, slotCmp?, cellA?, slotCarry?, slotImm?, immWordA, hq]

/-- **The 32-bit immediate store into a frame slot.** `MOV q, #v` with `q` a frame slot at
    `a` (`movl $v, off(%rsp)`) writes the low 32 bits of `v` at `a` and keeps the high 32 bits
    of the word at `a`. -/
theorem fstepA_slotBit (frame : String → Option (BitVec 64)) {q : String} {a : BitVec 64}
    (hq : frame q = some a) (v : Nat) (tag : Option Nat) (sa : LstateA) (zf : Bool) :
    fstepA frame (.Lopn [.reg q] "MOV" [.imm v], .reg tag) sa zf
      = some ({ sa with
          reg := sa.reg.nextPc
          mem := write64 sa.mem a
            ((read64 sa.mem a &&& 0xFFFFFFFF00000000#64) ||| BitVec.ofNat 64 (v % 2 ^ 32)) },
          zf) := by
  simp [fstepA, slotMov?, slotCmp?, cellA?, slotCarry?, slotImm?, immWordA, hq]

/-- **The select with a frame-slot value.** `CMOV:64 D, [C, A, B]`, `D` a register and one
    of `A`, `B` a frame slot, writes to `D` the select of the one-bit `C` between the words
    of `A` and `B`. -/
theorem fstepA_slotCmov (frame : String → Option (BitVec 64)) {D C A B : String}
    (hD : frame D = none) (hsl : ((frame A).isSome || (frame B).isSome) = true)
    (tag : Option Nat) (sa : LstateA) (zf : Bool) {va vb : BitVec 64}
    (hA : wordA frame sa A = some va) (hB : wordA frame sa B = some vb) :
    fstepA frame (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], .reg tag) sa zf
      = (sa.reg.getW C 1).map fun vc =>
          ({ sa with reg := (sa.reg.setReg D (selectW vc va vb)).nextPc }, zf) := by
  cases hc : sa.reg.getW C 1 <;>
    simp_all [fstepA, slotMov?, slotCmp?, cellA?, slotCarry?, slotImm?, slotCmov?]

/-- **The select into a frame slot.** `CMOV:64 D, [C, A, B]` with `D` a frame slot at `ad`
    writes at `ad` the select of the one-bit `C` between the words of `A` and `B`. -/
theorem fstepA_slotCmovDst (frame : String → Option (BitVec 64)) {D C A B : String}
    {ad : BitVec 64} (hD : frame D = some ad) (tag : Option Nat) (sa : LstateA) (zf : Bool)
    {va vb : BitVec 64} (hA : wordA frame sa A = some va) (hB : wordA frame sa B = some vb) :
    fstepA frame (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], .reg tag) sa zf
      = (sa.reg.getW C 1).map fun vc =>
          ({ sa with reg := sa.reg.nextPc, mem := write64 sa.mem ad (selectW vc va vb) }, zf) := by
  cases hc : sa.reg.getW C 1 <;>
    simp_all [fstepA, slotMov?, slotCmp?, cellA?, slotCarry?, slotImm?, slotCmov?]

/-- The straight fold of `fstepA`. -/
def runStraightA (frame : String → Option (BitVec 64)) :
    List LinstrRM → LstateA → Bool → Option (LstateA × Bool)
  | [], sa, zf => some (sa, zf)
  | i :: is, sa, zf => (fstepA frame i sa zf).bind fun bz => runStraightA frame is bz.1 bz.2

theorem runStraightA_append (frame : String → Option (BitVec 64)) (xs ys : List LinstrRM)
    (sa : LstateA) (zf : Bool) :
    runStraightA frame (xs ++ ys) sa zf
      = (runStraightA frame xs sa zf).bind fun bz => runStraightA frame ys bz.1 bz.2 := by
  induction xs generalizing sa zf with
  | nil => rfl
  | cons i is ih =>
      simp only [List.cons_append, runStraightA]
      cases fstepA frame i sa zf with
      | none => rfl
      | some bz => simp only [Option.bind_some, ih]

/-- `m` passes of `runStraightA`, each entered with the flag clear and the program counter
    reset to `q` after the pass. -/
def runBoundedStraightA (frame : String → Option (BitVec 64)) (body : List LinstrRM)
    (q : Nat) : Nat → LstateA → Option LstateA
  | 0, sa => some sa
  | k + 1, sa =>
      (runStraightA frame body sa false).bind fun bz =>
        runBoundedStraightA frame body q k (bz.1.setLpc q)

/-! ## 2. The layout and the relation -/

/-- The placement of the named arrays: base address, word count, and the frame slot that
    holds the pointer. -/
structure Layout where
  /-- The base address of the array. -/
  base : String → BitVec 64
  /-- The number of 64-bit words of the array. -/
  len : String → Nat
  /-- The frame slot holding the pointer of the array. -/
  slot : String → Option String

/-- The address of word `j` of array `A`. -/
def Layout.addr (L : Layout) (A : String) (j : Nat) : BitVec 64 :=
  L.base A + BitVec.ofNat 64 (8 * j)

/-- Separation: two declared cells have the same address or disjoint ranges, and a declared
    cell is disjoint from every pointer slot. -/
structure Layout.Sep (L : Layout) (frame : String → Option (BitVec 64)) : Prop where
  cells : ∀ A j A' j', j < L.len A → j' < L.len A' →
    L.addr A j = L.addr A' j' ∨ Disjoint8 (L.addr A j) (L.addr A' j')
  slots : ∀ A j B q a, j < L.len A → L.slot B = some q → frame q = some a →
    Disjoint8 (L.addr A j) a

/-- The register stores agree off the register `scr`. -/
def EqOff (scr : String) (r r' : LstateN) : Prop := ∀ x, x ≠ scr → r.lvm x = r'.lvm x

/-- The refinement relation on the cells `K`. -/
structure Rel (L : Layout) (frame : String → Option (BitVec 64)) (scr : String)
    (K : String → Nat → Prop) (s : LstateM) (sa : LstateA) : Prop where
  regs : EqOff scr s.reg sa.reg
  cells : ∀ A j, K A j → j < L.len A ∧ ∃ arr : Fin (L.len A) → BitVec 64,
    s.getArr A 64 (L.len A) = some arr ∧ read64 sa.mem (L.addr A j) = stackGet arr j
  slots : ∀ A q, L.slot A = some q → ∃ a, frame q = some a ∧ read64 sa.mem a = L.base A
  /-- The carry and overflow flags agree. -/
  flags : sa.cf = s.cf ∧ sa.of = s.of

/-- The cells after the store `dst := A[j ↦ _]`: under the name `dst`, the written cell and
    the cells of `A` in `K` at another address; under every other name, the cells of `K` at
    another address. -/
def afterStore (L : Layout) (K : String → Nat → Prop) (dst A : String) (j : Nat) :
    String → Nat → Prop :=
  fun A' j' =>
    (A' = dst ∧ (j' = j ∨ (K A j' ∧ L.addr A j' ≠ L.addr A j)))
      ∨ (A' ≠ dst ∧ K A' j' ∧ L.addr A' j' ≠ L.addr A j)

/-! ### Register-file lemmas -/

theorem EqOff.getW {scr : String} {r r' : LstateN} (h : EqOff scr r r') {x : String}
    (hx : x ≠ scr) (w : Nat) : r.getW x w = r'.getW x w := by
  unfold LstateN.getW
  rw [h x hx]

theorem EqOff.nextPc_left {scr : String} {r r' : LstateN} (h : EqOff scr r r') :
    EqOff scr r.nextPc r' := h

theorem EqOff.nextPc_right {scr : String} {r r' : LstateN} (h : EqOff scr r r') :
    EqOff scr r r'.nextPc := h

theorem EqOff.setReg {scr : String} {r r' : LstateN} (h : EqOff scr r r') (d : String)
    {w : Nat} (v : BitVec w) : EqOff scr (r.setReg d v) (r'.setReg d v) := by
  intro x hx
  simp only [LstateN.lvm_setReg]
  split
  · rfl
  · exact h x hx

theorem EqOff.setReg_scr_right {scr : String} {r r' : LstateN} (h : EqOff scr r r')
    {w : Nat} (v : BitVec w) : EqOff scr r (r'.setReg scr v) := by
  intro x hx
  simp only [LstateN.lvm_setReg, if_neg hx]
  exact h x hx

theorem EqOff.of_lvm {scr : String} {r r₁ r' : LstateN} (h : EqOff scr r r')
    (h1 : r₁.lvm = r.lvm) : EqOff scr r₁ r' := fun x hx => by rw [h1]; exact h x hx

/-! ### Array lemmas -/

theorem stackGet_stackSet_same {n : Nat} (arr : Fin n → BitVec 64) (j : Nat) (v : BitVec 64)
    (hj : j < n) : stackGet (stackSet arr j v) j = v := by
  cases n with
  | zero => omega
  | succ m => simp [stackGet, stackSet]

theorem stackGet_stackSet_ne {n : Nat} (arr : Fin n → BitVec 64) (j j' : Nat) (v : BitVec 64)
    (hj : j < n) (hj' : j' < n) (h : j' ≠ j) :
    stackGet (stackSet arr j v) j' = stackGet arr j' := by
  cases n with
  | zero => omega
  | succ m =>
      simp only [stackGet, stackSet]
      rw [if_neg]
      intro hc
      have := congrArg Fin.val hc
      simp only [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at this
      exact h this

/-- `Rel` reads the name-keyed state through its register store and its array carrier. -/
theorem Rel.congr {L : Layout} {frame : String → Option (BitVec 64)} {scr : String}
    {K : String → Nat → Prop} {s s₁ : LstateM} {sa : LstateA} (h : Rel L frame scr K s sa)
    (hreg : s₁.reg.lvm = s.reg.lvm) (harr : s₁.larr = s.larr)
    (hfl : s₁.cf = s.cf ∧ s₁.of = s.of) : Rel L frame scr K s₁ sa where
  regs := h.regs.of_lvm hreg
  cells := fun A j hK => by
    obtain ⟨hj, arr, ha, hr⟩ := h.cells A j hK
    refine ⟨hj, arr, ?_, hr⟩
    unfold LstateM.getArr at ha ⊢
    rw [harr]
    exact ha
  slots := h.slots
  flags := ⟨h.flags.1.trans hfl.1.symm, h.flags.2.trans hfl.2.symm⟩

/-- `Rel` is monotone in the cell predicate. -/
theorem Rel.mono {L : Layout} {frame : String → Option (BitVec 64)} {scr : String}
    {K K' : String → Nat → Prop} {s : LstateM} {sa : LstateA} (h : Rel L frame scr K s sa)
    (hK : ∀ A j, K' A j → K A j) : Rel L frame scr K' s sa where
  regs := h.regs
  cells := fun A j hk => h.cells A j (hK A j hk)
  slots := h.slots
  flags := h.flags

/-- `Rel` ignores the program counters. -/
theorem Rel.setLpc {L : Layout} {frame : String → Option (BitVec 64)} {scr : String}
    {K : String → Nat → Prop} {s : LstateM} {sa : LstateA} (h : Rel L frame scr K s sa)
    (q q' : Nat) : Rel L frame scr K (s.setLpc q) (sa.setLpc q') where
  regs := h.regs
  cells := h.cells
  slots := h.slots
  flags := h.flags

/-! ## 3. One access -/

/-- The reload of the pointer slot `q` into `scr`. -/
def reloadI (scr q : String) : LinstrRM := (.Lopn [.reg scr] "MOVQ" [.reg q], MemTag.reg none)

/-- The name-keyed load of `A[idx]` into `dst`. -/
def loadN (L : Layout) (dst A idx : String) : LinstrRM :=
  (.Lopn [.reg dst] "LOADIDX" [.arrIdx A idx 8], MemTag.load 64 (L.len A))

/-- The pointer form of `loadN`: reload, then load through `scr`. -/
def loadA (L : Layout) (scr q dst A idx : String) : List LinstrRM :=
  [reloadI scr q, (.Lopn [.reg dst] "LOADIDX" [.arrIdx scr idx 8], MemTag.load 64 (L.len A))]

/-- The name-keyed store `dst := A[idx ↦ val]`. The store is in place when `dst = A`. -/
def storeN (L : Layout) (dst A idx val : String) : LinstrRM :=
  (.Lopn [.reg dst] "STOREIDX" [.arrIdx A idx 8, .reg val], MemTag.store 64 (L.len A))

/-- The pointer form of `storeN`: reload, then store through `scr`. -/
def storeA (L : Layout) (scr q dst A idx val : String) : List LinstrRM :=
  [reloadI scr q,
   (.Lopn [.reg dst] "STOREIDX" [.arrIdx scr idx 8, .reg val], MemTag.store 64 (L.len A))]

theorem fstepF_loadN (L : Layout) (dst A idx : String) (s : LstateM) (zf : Bool) :
    fstepF (loadN L dst A idx) s zf = (lsemStepMem (loadN L dst A idx) s).map (·, zf) := by
  simp only [fstepF, loadN, cmpArgs?, movRegArgs?]
  rw [stepMemF_of_quiet rfl rfl rfl]

theorem fstepF_storeN (L : Layout) (dst A idx val : String) (s : LstateM) (zf : Bool) :
    fstepF (storeN L dst A idx val) s zf
      = (lsemStepMem (storeN L dst A idx val) s).map (·, zf) := by
  simp [fstepF, storeN, cmpArgs?, movRegArgs?, withWidthTag, stepMemF_of_quiet, aluFlagOp?,
    carryArgs?, wideArgs?]

theorem fstepA_reload (frame : String → Option (BitVec 64)) (scr q : String) (a : BitVec 64)
    (hq : frame q = some a) (sa : LstateA) (zf : Bool) :
    fstepA frame (reloadI scr q) sa zf
      = some ({ sa with reg := (sa.reg.setReg scr (read64 sa.mem a)).nextPc }, zf) := by
  simp [fstepA, reloadI, slotMov?, hq]

/-- **Load.** The name-keyed load of `A[idx]` is simulated by the reload of the pointer of
    `A` followed by the load through `scr`, when the index cell is in `K`. -/
theorem load_sim {L : Layout} {frame : String → Option (BitVec 64)} {scr : String}
    {K : String → Nat → Prop} {s : LstateM} {sa : LstateA} (hrel : Rel L frame scr K s sa)
    (dst A idx q : String) (hslot : L.slot A = some q) (hidx : idx ≠ scr)
    (hK : ∀ vi, s.reg.getW idx 64 = some vi → K A vi.toNat)
    (zf : Bool) (b : LstateM) (z : Bool)
    (hstep : fstepF (loadN L dst A idx) s zf = some (b, z)) :
    ∃ sa', runStraightA frame (loadA L scr q dst A idx) sa zf = some (sa', z)
      ∧ Rel L frame scr K b sa' := by
  rw [fstepF_loadN] at hstep
  obtain ⟨b', hb', hbz⟩ := Option.map_eq_some_iff.mp hstep
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hbz
  simp only [lsemStepMem, loadN, loadStruct?, if_true] at hb'
  cases harr : s.getArr A 64 (L.len A) with
  | none => simp [harr] at hb'
  | some arr =>
    cases hvi : s.reg.getW idx 64 with
    | none => simp [harr, hvi] at hb'
    | some vi =>
      simp only [harr, hvi, Option.some.injEq] at hb'
      subst hb'
      obtain ⟨a, hq, hptr⟩ := hrel.slots A q hslot
      obtain ⟨hj, arr', harr', hcell⟩ := hrel.cells A vi.toNat (hK vi hvi)
      rw [harr] at harr'
      obtain rfl := Option.some.inj harr'
      have hvia : sa.reg.getW idx 64 = some vi := by rw [← hrel.regs.getW hidx, hvi]
      simp only [loadA, runStraightA, fstepA_reload frame scr q a hq, Option.bind_some]
      simp only [fstepA, loadIdxA?, if_true, LstateN.getW_nextPc, LstateN.getW_setReg_same,
        LstateN.getW_setReg_other _ _ _ _ _ hidx, hvia, Option.bind_some]
      refine ⟨_, rfl, ?_⟩
      · refine ⟨?_, ?_, ?_, hrel.flags⟩
        · show EqOff scr ((s.reg.setReg dst _).nextPc) _
          simp only [hptr]
          have hc : read64 sa.mem (L.base A + BitVec.ofNat 64 (8 * vi.toNat))
              = stackGet arr vi.toNat := hcell
          rw [hc]
          exact ((hrel.regs.setReg_scr_right _).nextPc_right.setReg dst _)
        · intro A' j' hk
          obtain ⟨hj', arr'', ha'', hr''⟩ := hrel.cells A' j' hk
          exact ⟨hj', arr'', by simpa using ha'', hr''⟩
        · exact hrel.slots

/-- **Store.** The name-keyed store `dst := A[idx ↦ val]`, where `dst` and `A` name the
    same region, is simulated by the reload of the pointer of `A` followed by the store
    through `scr`, when the index is in bounds. The cells become `afterStore L K dst A j`. -/
theorem store_sim {L : Layout} {frame : String → Option (BitVec 64)} {scr : String}
    (hsep : L.Sep frame)
    {K : String → Nat → Prop} {s : LstateM} {sa : LstateA} (hrel : Rel L frame scr K s sa)
    (dst A idx val q : String) (hbase : L.base dst = L.base A) (hlen : L.len dst = L.len A)
    (hslot : L.slot A = some q) (hidx : idx ≠ scr) (hval : val ≠ scr)
    (j : Nat) (hj : j < L.len A) (hvj : ∀ vi, s.reg.getW idx 64 = some vi → vi.toNat = j)
    (zf : Bool) (b : LstateM) (z : Bool)
    (hstep : fstepF (storeN L dst A idx val) s zf = some (b, z)) :
    ∃ sa', runStraightA frame (storeA L scr q dst A idx val) sa zf = some (sa', z)
      ∧ Rel L frame scr (afterStore L K dst A j) b sa' := by
  have haddr : ∀ j', L.addr dst j' = L.addr A j' := fun j' => by
    unfold Layout.addr; rw [hbase]
  rw [fstepF_storeN] at hstep
  obtain ⟨b', hb', hbz⟩ := Option.map_eq_some_iff.mp hstep
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hbz
  simp only [lsemStepMem, storeN, storeStruct?, if_true] at hb'
  cases harr : s.getArr A 64 (L.len A) with
  | none => simp [harr] at hb'
  | some arr =>
    cases hvi : s.reg.getW idx 64 with
    | none => simp [harr, hvi] at hb'
    | some vi =>
      cases hvv : s.reg.getW val 64 with
      | none => simp [harr, hvi, hvv] at hb'
      | some vv =>
        simp only [harr, hvi, hvv, Option.some.injEq] at hb'
        subst hb'
        obtain rfl := hvj vi hvi
        obtain ⟨a, hq, hptr⟩ := hrel.slots A q hslot
        have hvia : sa.reg.getW idx 64 = some vi := by rw [← hrel.regs.getW hidx, hvi]
        have hvva : sa.reg.getW val 64 = some vv := by rw [← hrel.regs.getW hval, hvv]
        simp only [storeA, runStraightA, fstepA_reload frame scr q a hq, Option.bind_some]
        simp only [fstepA, storeIdxA?, if_true, LstateN.getW_nextPc, LstateN.getW_setReg_same,
          LstateN.getW_setReg_other _ _ _ _ _ hidx, LstateN.getW_setReg_other _ _ _ _ _ hval,
          hvia, hvva, Option.bind_some]
        refine ⟨_, rfl, ?_⟩
        · simp only [hptr]
          refine ⟨?_, ?_, ?_, hrel.flags⟩
          · exact (hrel.regs.setReg_scr_right _).nextPc_right
          · intro A' j' hk
            show j' < L.len A' ∧ ∃ arr' : Fin (L.len A') → BitVec 64,
              ((s.setArr dst (stackSet arr vi.toNat vv)).nextPc).getArr A' 64 (L.len A')
                = some arr'
              ∧ read64 (write64 sa.mem (L.addr A vi.toNat) vv) (L.addr A' j') = stackGet arr' j'
            have hdisj : ∀ B k, K B k → L.addr B k ≠ L.addr A vi.toNat →
                Disjoint8 (L.addr A vi.toNat) (L.addr B k) := fun B k hBk hne => by
              rcases hsep.cells A vi.toNat B k hj (hrel.cells B k hBk).1 with h | h
              · exact absurd h.symm hne
              · exact h
            rcases hk with ⟨rfl, hk⟩ | ⟨hA, hk, hne⟩
            · rw [haddr, hlen]
              rcases hk with rfl | ⟨hk, hne⟩
              · refine ⟨hj, stackSet arr vi.toNat vv, by simp, ?_⟩
                rw [read64_write64_same, stackGet_stackSet_same _ _ _ hj]
              · obtain ⟨hj', arr', ha', hr'⟩ := hrel.cells A j' hk
                rw [harr] at ha'
                obtain rfl := Option.some.inj ha'
                refine ⟨hj', stackSet arr vi.toNat vv, by simp, ?_⟩
                rw [read64_write64_of_disjoint _ _ _ _ (hdisj A j' hk hne), hr',
                  stackGet_stackSet_ne _ _ _ _ hj hj']
                rintro rfl
                exact hne rfl
            · obtain ⟨hj', arr', ha', hr'⟩ := hrel.cells A' j' hk
              rw [read64_write64_of_disjoint _ _ _ _ (hdisj A' j' hk hne)]
              exact ⟨hj', arr', by simpa [hA] using ha', hr'⟩
          · intro B qB hB
            obtain ⟨aB, hqB, hpB⟩ := hrel.slots B qB hB
            refine ⟨aB, hqB, ?_⟩
            show read64 (write64 sa.mem (L.addr A vi.toNat) vv) aB = L.base B
            rw [read64_write64_of_disjoint _ _ _ _ (hsep.slots A vi.toNat B qB aB hj hB hqB)]
            exact hpB

/-! ## 4. Register instructions -/

/-- A register-tagged instruction that is no frame-slot move, no compare against a frame
    slot, no cell access, no carry-chain instruction with a frame-slot operand, no
    immediate move into a frame slot and no select with a frame-slot value. -/
def IsRegInstr (frame : String → Option (BitVec 64)) (i : LinstrRM) : Prop :=
  (∃ c, i.snd = MemTag.reg c) ∧
    (∀ d src, slotMov? i.fst = some (d, src) → frame src = none ∧ frame d = none) ∧
    (∀ d x q, slotCmp? i.fst = some (d, x, q) → frame q = none) ∧ cellA? i.fst = none
      ∧ slotCarry? frame i.fst = none ∧ slotImm? frame i.fst = none
      ∧ slotCmov? frame i.fst = none

/-- The step of `i` is independent of the register `scr`: from register stores that agree
    off `scr` and the same carry and overflow flags, a successful step is matched by a step
    with the same zero flag, the results agree off `scr` and on the carry and overflow
    flags, and the array carrier is unchanged. -/
def RegCompat (scr : String) (i : LinstrRM) : Prop :=
  ∀ (s : LstateM) (ra : LstateN) (zf : Bool) (b : LstateM) (z : Bool),
    EqOff scr s.reg ra → fstepF i s zf = some (b, z) →
    ∃ b' : LstateM, fstepF i { reg := ra, cf := s.cf, of := s.of } zf = some (b', z)
      ∧ EqOff scr b.reg b'.reg ∧ b.larr = s.larr ∧ b'.cf = b.cf ∧ b'.of = b.of

theorem fstepA_reg {frame : String → Option (BitVec 64)} {i : LinstrRM}
    (hi : IsRegInstr frame i) (sa : LstateA) (zf : Bool) :
    fstepA frame i sa zf = regStepA i sa zf := by
  obtain ⟨⟨c, hc⟩, hs, hq, hcl, hsc, hsi, hsv⟩ := hi
  unfold fstepA
  rw [hc]
  simp only
  cases hm : slotMov? i.fst with
  | none =>
      simp only
      cases hk : slotCmp? i.fst with
      | none => simp only [hcl, hsc, hsi, hsv]
      | some dxq =>
          obtain ⟨d, x, q⟩ := dxq
          simp only [hq d x q hk]
  | some ds =>
      obtain ⟨d, src⟩ := ds
      obtain ⟨h1, h2⟩ := hs d src hm
      simp only [h1, h2]

/-- **Register instruction.** An instruction independent of `scr` is simulated by itself. -/
theorem reg_sim {L : Layout} {frame : String → Option (BitVec 64)} {scr : String}
    {K : String → Nat → Prop} {s : LstateM} {sa : LstateA} (hrel : Rel L frame scr K s sa)
    (i : LinstrRM) (hi : IsRegInstr frame i) (hc : RegCompat scr i)
    (zf : Bool) (b : LstateM) (z : Bool) (hstep : fstepF i s zf = some (b, z)) :
    ∃ sa', runStraightA frame [i] sa zf = some (sa', z) ∧ Rel L frame scr K b sa' := by
  obtain ⟨b', hb', heq, hlarr, hcf, hof⟩ := hc s sa.reg zf b z hrel.regs hstep
  refine ⟨{ sa with reg := b'.reg, cf := b'.cf, of := b'.of }, ?_, ?_⟩
  · have hsa : ({ reg := sa.reg, cf := sa.cf, of := sa.of } : LstateM)
        = { reg := sa.reg, cf := s.cf, of := s.of } := by rw [hrel.flags.1, hrel.flags.2]
    simp only [runStraightA, fstepA_reg hi, regStepA, hsa, hb', Option.map_some,
      Option.bind_some]
  · refine ⟨heq, ?_, hrel.slots, hcf, hof⟩
    intro A j hk
    obtain ⟨hj, arr, ha, hr⟩ := hrel.cells A j hk
    refine ⟨hj, arr, ?_, hr⟩
    unfold LstateM.getArr at ha ⊢
    rw [hlarr]
    exact ha

theorem evalOperandN_eqOff {scr : String} {r r' : LstateN} (h : EqOff scr r r')
    (o : LOperand) (ho : o ≠ .reg scr) : evalOperandN r 64 o = evalOperandN r' 64 o := by
  cases o with
  | reg x => exact h.getW (fun hx => ho (by rw [hx])) 64
  | _ => rfl

/-- The operands `aluFlagOp?` returns are the two sources of the instruction. -/
theorem aluFlagOp?_ops {d : List LOperand} {opn : String} {x y : LOperand} {t : MemTag}
    {p : AluOp × LOperand × LOperand} (h : aluFlagOp? (.Lopn d opn [x, y], t) = some p) :
    p.2.1 = x ∧ p.2.2 = y := by
  unfold aluFlagOp? at h
  dsimp only at h
  split at h
  · rename_i heq
    simp only [LinstrR.Lopn.injEq, List.cons.injEq] at heq
    obtain ⟨-, -, rfl, rfl, -⟩ := heq
    split_ifs at h <;> cases h <;> exact ⟨rfl, rfl⟩
  · cases h

/-- The flags `withALUFlags` writes from register stores that agree off `scr` are equal, when
    the operands it reads are not `scr`. -/
theorem withALUFlags_eqOff {scr : String} {i : LinstrRM}
    (hflag : ∀ p, aluFlagOp? i = some p → p.2.1 ≠ .reg scr ∧ p.2.2 ≠ .reg scr)
    {s0 s0' b b' : LstateM} (heq : EqOff scr s0.reg s0'.reg) (hb : b'.cf = b.cf ∧ b'.of = b.of) :
    (withALUFlags i s0' b').cf = (withALUFlags i s0 b).cf
      ∧ (withALUFlags i s0' b').of = (withALUFlags i s0 b).of := by
  unfold withALUFlags
  cases h : aluFlagOp? i with
  | none => exact hb
  | some p =>
      obtain ⟨op, a, c⟩ := p
      obtain ⟨ha, hc⟩ := hflag _ h
      simp only [← evalOperandN_eqOff heq a ha, ← evalOperandN_eqOff heq c hc]
      split
      · exact ⟨rfl, rfl⟩
      · exact hb

/-- The flag compare is independent of `scr` when neither operand is `scr`. -/
theorem regCompat_cmp (scr : String) (i : LinstrRM) (a c : LOperand)
    (hcmp : cmpArgs? i = some (a, c)) (ha : a ≠ .reg scr) (hcn : c ≠ .reg scr) :
    RegCompat scr i := by
  intro s ra zf b z heq hstep
  unfold fstepF at hstep ⊢
  simp only [hcmp] at hstep ⊢
  rw [← evalOperandN_eqOff heq a ha, ← evalOperandN_eqOff heq c hcn]
  cases h1 : evalOperandN s.reg 64 a with
  | none => simp [h1] at hstep
  | some va =>
    cases h2 : evalOperandN s.reg 64 c with
    | none => simp [h1, h2] at hstep
    | some vc =>
      simp only [h1, h2, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨_, rfl, heq, rfl, rfl, rfl⟩

/-- The register copy is independent of `scr` when its source is not `scr`. -/
theorem regCompat_mov (scr : String) (i : LinstrRM) (dst src : String)
    (hcmp : cmpArgs? i = none) (hmov : movRegArgs? i = some (dst, src)) (hsrc : src ≠ scr) :
    RegCompat scr i := by
  intro s ra zf b z heq hstep
  unfold fstepF at hstep ⊢
  simp only [hcmp, hmov, readReg, Option.some.injEq, Prod.mk.injEq] at hstep ⊢
  obtain ⟨rfl, rfl⟩ := hstep
  refine ⟨_, ⟨rfl, rfl⟩, ?_, rfl, rfl, rfl⟩
  show EqOff scr ((s.reg.setReg dst (s.reg.lvm src).2).nextPc)
    ((ra.setReg dst (ra.lvm src).2).nextPc)
  intro x hx
  simp only [LstateN.lvm_nextPc, LstateN.lvm_setReg]
  split
  · rw [heq src hsrc]
  · exact heq x hx

/-- An instruction whose step reads one register `a ≠ scr` at its stored width and writes
    a function of the value to `dst` is independent of `scr`. -/
theorem regCompat_of_unary (scr : String) (i : LinstrRM) (dst a : String) (ha : a ≠ scr)
    (hflag : ∀ p, aluFlagOp? i = some p → p.2.1 ≠ .reg scr ∧ p.2.2 ≠ .reg scr)
    (g : (w : Nat) → BitVec w → BitVec w)
    (h : ∀ (s : LstateM) (zf : Bool) (w : Nat) (va : BitVec w), s.reg.getW a w = some va →
      fstepF i s zf = some (withALUFlags i s ((s.setReg dst (g w va)).nextPc), zf)) :
    RegCompat scr i := by
  intro s ra zf b z heq hstep
  rcases hs : s.reg.lvm a with ⟨w, va⟩
  have hg : s.reg.getW a w = some va := getW_eq_some_iff.mpr hs
  have hga : ({ reg := ra, cf := s.cf, of := s.of } : LstateM).reg.getW a w = some va := by
    show ra.getW a w = some va
    rw [← heq.getW ha]; exact hg
  rw [h s zf w va hg] at hstep
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hstep
  have hw := withALUFlags_eqOff (i := i) hflag (s0 := s)
    (s0' := { reg := ra, cf := s.cf, of := s.of }) (b := (s.setReg dst (g w va)).nextPc)
    (b' := (({ reg := ra, cf := s.cf, of := s.of } : LstateM).setReg dst (g w va)).nextPc)
    heq ⟨rfl, rfl⟩
  refine ⟨_, h _ zf w va hga, ?_, by rw [withALUFlags_larr]; rfl, hw.1, hw.2⟩
  rw [withALUFlags_reg, withALUFlags_reg]
  exact heq.setReg dst _

/-- The instruction `ADD:64 dst, a, #k`. -/
def addImmI (dst a : String) (k : Nat) : LinstrRM :=
  (LinstrR.Lopn [.reg dst] "ADD:64" [.reg a, .imm k], MemTag.reg none)

/-- The instruction `SUB:64 dst, a, #k`. -/
def subImmI (dst a : String) (k : Nat) : LinstrRM :=
  (LinstrR.Lopn [.reg dst] "SUB:64" [.reg a, .imm k], MemTag.reg none)

theorem fstepF_addImmI (dst a : String) (k : Nat) (s : LstateM) (zf : Bool) {w : Nat}
    (va : BitVec w) (hg : s.reg.getW a w = some va) :
    fstepF (addImmI dst a k) s zf
      = some (withALUFlags (addImmI dst a k) s
          ((s.setReg dst (va + BitVec.ofNat w k)).nextPc), zf) := by
  have hL := JasminLsemMemSourceTieUncond.lsemStepMem_add64Imm dst a k va s hg
  simp only [addImmI, fstepF, cmpArgs?, movRegArgs?, withWidthTag] at hL ⊢
  simp [stepMemF_of_lsemStepMem hL]

theorem fstepF_subImmI (dst a : String) (k : Nat) (s : LstateM) (zf : Bool) {w : Nat}
    (va : BitVec w) (hg : s.reg.getW a w = some va) :
    fstepF (subImmI dst a k) s zf
      = some (withALUFlags (subImmI dst a k) s
          ((s.setReg dst (va - BitVec.ofNat w k)).nextPc), zf) := by
  have hL := JasminLsemMemSourceTieUncond.lsemStepMem_sub64Imm dst a k va s hg
  simp only [subImmI, fstepF, cmpArgs?, movRegArgs?, withWidthTag] at hL ⊢
  simp [stepMemF_of_lsemStepMem hL]

/-- `ADD:64 dst, a, #k` is independent of `scr` when `a ≠ scr`. -/
theorem regCompat_addImmI (scr dst a : String) (k : Nat) (ha : a ≠ scr) :
    RegCompat scr (addImmI dst a k) :=
  regCompat_of_unary scr _ dst a ha
    (fun _ hp => by
      obtain ⟨h1, h2⟩ := aluFlagOp?_ops hp
      rw [h1, h2]
      exact ⟨fun he => ha (LOperand.reg.inj he), fun he => LOperand.noConfusion he⟩)
    (fun w va => va + BitVec.ofNat w k)
    fun s zf _ va hg => fstepF_addImmI dst a k s zf va hg

/-- `SUB:64 dst, a, #k` is independent of `scr` when `a ≠ scr`. -/
theorem regCompat_subImmI (scr dst a : String) (k : Nat) (ha : a ≠ scr) :
    RegCompat scr (subImmI dst a k) :=
  regCompat_of_unary scr _ dst a ha
    (fun _ hp => by
      obtain ⟨h1, h2⟩ := aluFlagOp?_ops hp
      rw [h1, h2]
      exact ⟨fun he => ha (LOperand.reg.inj he), fun he => LOperand.noConfusion he⟩)
    (fun w va => va - BitVec.ofNat w k)
    fun s zf _ va hg => fstepF_subImmI dst a k s zf va hg

theorem isRegInstr_addImmI (frame : String → Option (BitVec 64)) (dst a : String) (k : Nat) :
    IsRegInstr frame (addImmI dst a k) :=
  ⟨⟨none, rfl⟩, fun d src h => by simp [addImmI, slotMov?] at h,
    fun d x q h => by simp [addImmI, slotCmp?] at h, by simp [addImmI, cellA?],
    by simp [addImmI, slotCarry?], by simp [addImmI, slotImm?], by simp [addImmI, slotCmov?]⟩

theorem isRegInstr_subImmI (frame : String → Option (BitVec 64)) (dst a : String) (k : Nat) :
    IsRegInstr frame (subImmI dst a k) :=
  ⟨⟨none, rfl⟩, fun d src h => by simp [subImmI, slotMov?] at h,
    fun d x q h => by simp [subImmI, slotCmp?] at h, by simp [subImmI, cellA?],
    by simp [subImmI, slotCarry?], by simp [subImmI, slotImm?], by simp [subImmI, slotCmov?]⟩

/-! ## 5. Segments -/

/-- The segment simulation quadruple: from `Rel` on `K` and the name-side precondition `P`,
    a successful name-keyed run of `seg` is matched by a run of `segA` with the same flag,
    ending in `Rel` on `K'` with the name-side postcondition `Q`. -/
def SimSeg (L : Layout) (frame : String → Option (BitVec 64)) (scr : String)
    (K : String → Nat → Prop) (P : LstateM → Prop) (seg segA : List LinstrRM)
    (K' : String → Nat → Prop) (Q : LstateM → Prop) : Prop :=
  ∀ (s : LstateM) (sa : LstateA) (zf : Bool) (b : LstateM) (z : Bool),
    P s → Rel L frame scr K s sa → runStraightF seg s zf = some (b, z) →
    ∃ sa', runStraightA frame segA sa zf = some (sa', z) ∧ Rel L frame scr K' b sa' ∧ Q b

variable {L : Layout} {frame : String → Option (BitVec 64)} {scr : String}

theorem SimSeg.nil (K : String → Nat → Prop) (P : LstateM → Prop) :
    SimSeg L frame scr K P [] [] K P := by
  intro s sa zf b z hP hrel hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrun
  exact ⟨sa, rfl, hrel, hP⟩

theorem runStraightF_append (xs ys : List LinstrRM) (s : LstateM) (zf : Bool) :
    runStraightF (xs ++ ys) s zf
      = (runStraightF xs s zf).bind fun bz => runStraightF ys bz.1 bz.2 := by
  induction xs generalizing s zf with
  | nil => rfl
  | cons i is ih =>
      simp only [List.cons_append, runStraightF_cons]
      cases fstepF i s zf with
      | none => rfl
      | some bz => simp only [Option.bind_some, ih]

theorem SimSeg.append {K K₁ K₂ : String → Nat → Prop} {P Q₁ Q₂ : LstateM → Prop}
    {seg₁ segA₁ seg₂ segA₂ : List LinstrRM}
    (h₁ : SimSeg L frame scr K P seg₁ segA₁ K₁ Q₁)
    (h₂ : SimSeg L frame scr K₁ Q₁ seg₂ segA₂ K₂ Q₂) :
    SimSeg L frame scr K P (seg₁ ++ seg₂) (segA₁ ++ segA₂) K₂ Q₂ := by
  intro s sa zf b z hP hrel hrun
  rw [runStraightF_append] at hrun
  cases h : runStraightF seg₁ s zf with
  | none => simp [h] at hrun
  | some bz =>
      obtain ⟨b₁, z₁⟩ := bz
      rw [h, Option.bind_some] at hrun
      obtain ⟨sa₁, hA₁, hrel₁, hQ₁⟩ := h₁ s sa zf b₁ z₁ hP hrel h
      obtain ⟨sa₂, hA₂, hrel₂, hQ₂⟩ := h₂ b₁ sa₁ z₁ b z hQ₁ hrel₁ hrun
      exact ⟨sa₂, by rw [runStraightA_append, hA₁, Option.bind_some]; exact hA₂, hrel₂, hQ₂⟩

/-- Consequence: strengthen the precondition, shrink the final cells, weaken the
    postcondition. -/
theorem SimSeg.weaken {K K' K'' : String → Nat → Prop} {P P' Q Q' : LstateM → Prop}
    {seg segA : List LinstrRM} (h : SimSeg L frame scr K P seg segA K' Q)
    (hP : ∀ s, P' s → P s) (hK : ∀ A j, K'' A j → K' A j) (hQ : ∀ s, Q s → Q' s) :
    SimSeg L frame scr K P' seg segA K'' Q' := by
  intro s sa zf b z hp hrel hrun
  obtain ⟨sa', hA, hrel', hq⟩ := h s sa zf b z (hP s hp) hrel hrun
  exact ⟨sa', hA, hrel'.mono hK, hQ b hq⟩

theorem runStraightF_singleton (i : LinstrRM) (s : LstateM) (zf : Bool) :
    runStraightF [i] s zf = fstepF i s zf := by
  rw [runStraightF_cons]
  cases fstepF i s zf with
  | none => rfl
  | some bz => rfl

/-- The load rule. -/
theorem SimSeg.load (K : String → Nat → Prop) (P Q : LstateM → Prop)
    (dst A idx q : String) (hslot : L.slot A = some q) (hidx : idx ≠ scr)
    (hK : ∀ s vi, P s → s.reg.getW idx 64 = some vi → K A vi.toNat)
    (hQ : ∀ s zf b z, P s → fstepF (loadN L dst A idx) s zf = some (b, z) → Q b) :
    SimSeg L frame scr K P [loadN L dst A idx] (loadA L scr q dst A idx) K Q := by
  intro s sa zf b z hP hrel hrun
  rw [runStraightF_singleton] at hrun
  obtain ⟨sa', hA, hrel'⟩ := load_sim hrel dst A idx q hslot hidx (fun vi => hK s vi hP)
    zf b z hrun
  exact ⟨sa', hA, hrel', hQ s zf b z hP hrun⟩

/-- The store rule. -/
theorem SimSeg.store (hsep : L.Sep frame) (K : String → Nat → Prop) (P Q : LstateM → Prop)
    (dst A idx val q : String) (hbase : L.base dst = L.base A) (hlen : L.len dst = L.len A)
    (hslot : L.slot A = some q) (hidx : idx ≠ scr) (hval : val ≠ scr)
    (j : Nat) (hj : j < L.len A)
    (hvj : ∀ s vi, P s → s.reg.getW idx 64 = some vi → vi.toNat = j)
    (hQ : ∀ s zf b z, P s → fstepF (storeN L dst A idx val) s zf = some (b, z) → Q b) :
    SimSeg L frame scr K P [storeN L dst A idx val] (storeA L scr q dst A idx val)
      (afterStore L K dst A j) Q := by
  intro s sa zf b z hP hrel hrun
  rw [runStraightF_singleton] at hrun
  obtain ⟨sa', hA, hrel'⟩ := store_sim hsep hrel dst A idx val q hbase hlen hslot hidx hval j hj
    (fun vi => hvj s vi hP) zf b z hrun
  exact ⟨sa', hA, hrel', hQ s zf b z hP hrun⟩

/-- The register-instruction rule. -/
theorem SimSeg.reg (K : String → Nat → Prop) (P Q : LstateM → Prop) (i : LinstrRM)
    (hi : IsRegInstr frame i) (hc : RegCompat scr i)
    (hQ : ∀ s zf b z, P s → fstepF i s zf = some (b, z) → Q b) :
    SimSeg L frame scr K P [i] [i] K Q := by
  intro s sa zf b z hP hrel hrun
  rw [runStraightF_singleton] at hrun
  obtain ⟨sa', hA, hrel'⟩ := reg_sim hrel i hi hc zf b z hrun
  exact ⟨sa', hA, hrel', hQ s zf b z hP hrun⟩

/-! ## 6. The loop -/

/-- **The bounded fold.** A family of segment simulations indexed by the trip gives the
    simulation of `m` passes. The cells and the name-side invariant are indexed by the
    trip; the postcondition of trip `t` is the invariant of trip `t + 1` after the program
    counter reset. -/
theorem runBounded_sim (K : Nat → String → Nat → Prop) (P : Nat → LstateM → Prop)
    (body bodyA : List LinstrRM) (q qA : Nat) (m : Nat)
    (hbody : ∀ t, t < m →
      SimSeg L frame scr (K t) (P t) body bodyA (K (t + 1)) (fun b => P (t + 1) (b.setLpc q))) :
    ∀ (k t : Nat), t + k = m → ∀ (s : LstateM) (sa : LstateA) (bfin : LstateM),
      P t s → Rel L frame scr (K t) s sa →
      runBoundedStraightF body q k s = some bfin →
      ∃ safin, runBoundedStraightA frame bodyA qA k sa = some safin
        ∧ Rel L frame scr (K m) bfin safin ∧ P m bfin := by
  intro k
  induction k with
  | zero =>
      intro t ht s sa bfin hP hrel hrun
      obtain rfl : t = m := by omega
      obtain rfl := Option.some.inj hrun
      exact ⟨sa, rfl, hrel, hP⟩
  | succ k ih =>
      intro t ht s sa bfin hP hrel hrun
      rw [runBoundedStraightF_succ] at hrun
      cases h : runStraightF body s false with
      | none => simp [h] at hrun
      | some bz =>
          obtain ⟨b, z⟩ := bz
          rw [h, Option.bind_some] at hrun
          obtain ⟨sa', hA, hrel', hQ⟩ := hbody t (by omega) s sa false b z hP hrel h
          obtain ⟨safin, hAfin, hrelfin, hPfin⟩ := ih (t + 1) (by omega) (b.setLpc q)
            (sa'.setLpc qA) bfin hQ (hrel'.setLpc q qA) hrun
          refine ⟨safin, ?_, hrelfin, hPfin⟩
          simp only [runBoundedStraightA, hA, Option.bind_some]
          exact hAfin

/-- **The guarded flag loop.** When the flag machine runs the guarded loop skeleton over
    `body` from a counter `v0 ≠ 0` under the schedule hypotheses of
    `guardedFlagLoop_runBounded_general`, the fold's final state is related on `K m` to the
    final state of `m` passes of the pointer-form body on the address machine, and the
    halting state agrees with the fold's final state on the registers and the arrays. -/
theorem guardedFlagLoop_addr_sim (K : Nat → String → Nat → Prop) (P : Nat → LstateM → Prop)
    (fn : String) (top endL : LLabel) (nReg : String) (body bodyA : List LinstrRM)
    (hlopn : ∀ i ∈ body, IsLopn i) (hne : top ≠ endL)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (v0 : BitVec 64) (hv0 : b0.reg.getW nReg 64 = some v0) (hv0ne : (v0 == 0#64) = false)
    (m : Nat) (hm : 0 < m) (bfin : LstateM)
    (hbound : runBoundedStraightF body 3 m (b0.setLpc 3) = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi,
      runBoundedStraightF body 3 i (b0.setLpc 3) = some bi → condNZ bi (.reg nReg) = true)
    (hzero : bfin.reg.getW nReg 64 = some 0#64)
    (hbody : ∀ t, t < m →
      SimSeg L frame scr (K t) (P t) body bodyA (K (t + 1)) (fun b => P (t + 1) (b.setLpc 3)))
    (sa : LstateA) (qA : Nat) (hP0 : P 0 (b0.setLpc 3)) (hrel : Rel L frame scr (K 0) b0 sa) :
    ∃ (n : Nat) (t : LstateMF) (safin : LstateA),
      lsemFuelMemF (singletonProgM fn (guardedFlagLoopLinstrRM top endL nReg body)) n
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ runBoundedStraightA frame bodyA qA m sa = some safin
        ∧ Rel L frame scr (K m) bfin safin
        ∧ t.prog.base.reg.lvm = bfin.reg.lvm ∧ t.prog.base.larr = bfin.larr ∧ t.zf = true := by
  obtain ⟨n, t, ht, hlvm, hlarr, hz⟩ := guardedFlagLoop_runBounded_general fn top endL nReg
    body hlopn hne b0 zf hpc v0 hv0 hv0ne m hm bfin hbound htaken hzero
  obtain ⟨safin, hA, hrelfin, _⟩ := runBounded_sim K P body bodyA 3 qA m hbody m 0 (by omega)
    (b0.setLpc 3) sa bfin hP0 (hrel.congr rfl rfl ⟨rfl, rfl⟩) hbound
  exact ⟨n, t, safin, ht, hA, hrelfin, hlvm, hlarr, hz⟩

/-! ## 7. Regions -/

theorem Layout.addr_toNat (L : Layout) (A : String) (j : Nat) (hj : j < L.len A)
    (hw : (L.base A).toNat + 8 * L.len A ≤ 2 ^ 64) :
    (L.addr A j).toNat = (L.base A).toNat + 8 * j := by
  unfold Layout.addr
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 8 * j) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- Regions that lie in the address space without wrapping, and that pairwise have the
    same base or are disjoint, satisfy the cell condition of `Layout.Sep`. Two names with
    the same base denote one region. -/
theorem Layout.sep_of_regions (L : Layout)
    (hw : ∀ A, (L.base A).toNat + 8 * L.len A ≤ 2 ^ 64)
    (hreg : ∀ A A', L.base A = L.base A'
      ∨ (L.base A).toNat + 8 * L.len A ≤ (L.base A').toNat
      ∨ (L.base A').toNat + 8 * L.len A' ≤ (L.base A).toNat) :
    ∀ A j A' j', j < L.len A → j' < L.len A' →
      L.addr A j = L.addr A' j' ∨ Disjoint8 (L.addr A j) (L.addr A' j') := by
  intro A j A' j' hj hj'
  have h1 := L.addr_toNat A j hj (hw A)
  have h2 := L.addr_toNat A' j' hj' (hw A')
  have hwA := hw A
  have hwA' := hw A'
  rcases hreg A A' with hb | hd | hd
  · by_cases hjj : j = j'
    · left
      subst hjj
      unfold Layout.addr
      rw [hb]
    · right
      have hbn : (L.base A).toNat = (L.base A').toNat := by rw [hb]
      exact disjoint8_of_toNat _ _ (by omega) (by omega) (by omega)
  · exact Or.inr (disjoint8_of_toNat _ _ (by omega) (by omega) (by omega))
  · exact Or.inr (disjoint8_of_toNat _ _ (by omega) (by omega) (by omega))

/-! ## 8. Entry -/

/-- The entry block that stores each pointer argument register `r` into its slot `q`. -/
def saveArgs (args : List (String × String)) : List LinstrRM :=
  args.map fun qr => (.Lopn [.reg qr.1] "MOVQ" [.reg qr.2], MemTag.reg none)

/-- The entry block runs, leaves the register store unchanged, leaves every word disjoint
    from the written slots unchanged, and leaves in each slot the value of its argument
    register, when the slots are pairwise disjoint and no argument register is a slot. -/
theorem saveArgs_run (frame : String → Option (BitVec 64)) :
    ∀ (args : List (String × String)) (sa : LstateA) (zf : Bool),
      (∀ qr ∈ args, frame qr.2 = none ∧ ∃ a, frame qr.1 = some a) →
      (∀ qr ∈ args, ∃ p, sa.reg.getW qr.2 64 = some p) →
      args.Pairwise (fun qr qr' => ∀ a a', frame qr.1 = some a → frame qr'.1 = some a' →
        Disjoint8 a' a) →
      ∃ sa', runStraightA frame (saveArgs args) sa zf = some (sa', zf)
        ∧ sa'.reg.lvm = sa.reg.lvm
        ∧ (∀ x, (∀ qr ∈ args, ∀ a, frame qr.1 = some a → Disjoint8 a x) →
            read64 sa'.mem x = read64 sa.mem x)
        ∧ ∀ qr ∈ args, ∀ a, frame qr.1 = some a →
            sa.reg.getW qr.2 64 = some (read64 sa'.mem a) := by
  intro args
  induction args with
  | nil =>
      intro sa zf _ _ _
      exact ⟨sa, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (by simp)⟩
  | cons qr rest ih =>
      intro sa zf hfr hreg hpw
      obtain ⟨hsrc, a, ha⟩ := hfr qr (by simp)
      obtain ⟨p, hp⟩ := hreg qr (by simp)
      have hstep : fstepA frame (.Lopn [.reg qr.1] "MOVQ" [.reg qr.2], MemTag.reg none) sa zf
          = some ({ sa with reg := sa.reg.nextPc, mem := write64 sa.mem a p }, zf) := by
        simp [fstepA, slotMov?, hsrc, ha, hp]
      rw [List.pairwise_cons] at hpw
      obtain ⟨sa', hrun, hlvm, hframe, hslots⟩ :=
        ih { sa with reg := sa.reg.nextPc, mem := write64 sa.mem a p } zf
          (fun x hx => hfr x (by simp [hx]))
          (fun x hx => by
            obtain ⟨p', hp'⟩ := hreg x (by simp [hx])
            exact ⟨p', by simpa using hp'⟩)
          hpw.2
      refine ⟨sa', ?_, ?_, ?_, ?_⟩
      · simp only [saveArgs, List.map_cons, runStraightA, hstep, Option.bind_some]
        exact hrun
      · rw [hlvm]; rfl
      · intro x hx
        rw [hframe x (fun y hy => hx y (by simp [hy]))]
        exact read64_write64_of_disjoint _ _ _ _ (hx qr (by simp) a ha)
      · intro y hy a' ha'
        rcases List.mem_cons.mp hy with rfl | hy
        · rw [ha] at ha'
          obtain rfl := Option.some.inj ha'
          rw [hframe a (fun y hy b hb => hpw.1 y hy a b ha hb), read64_write64_same, hp]
        · have := hslots y hy a' ha'
          simpa using this

/-- **Entry.** What the ABI entry provides, and what it yields: an address state whose
    registers agree with the name-keyed state off `scr`, whose memory holds each declared
    array at its base, and whose pointer slots hold the bases, is related on `K`. After
    `saveArgs`, the slot condition is `saveArgs_run` at argument registers holding the
    bases. -/
theorem rel_of_entry (L : Layout) (frame : String → Option (BitVec 64)) (scr : String)
    (K : String → Nat → Prop) (s : LstateM) (sa : LstateA)
    (hregs : EqOff scr s.reg sa.reg)
    (hK : ∀ A j, K A j → j < L.len A)
    (harr : ∀ A j, K A j → ∃ arr : Fin (L.len A) → BitVec 64,
      s.getArr A 64 (L.len A) = some arr ∧ read64 sa.mem (L.addr A j) = stackGet arr j)
    (hslots : ∀ A q, L.slot A = some q → ∃ a, frame q = some a ∧ read64 sa.mem a = L.base A)
    (hflags : sa.cf = s.cf ∧ sa.of = s.of) :
    Rel L frame scr K s sa :=
  ⟨hregs, fun A j hk => ⟨hK A j hk, harr A j hk⟩, hslots, hflags⟩

/-! ## 9. Instance: the copy trip with source and destination at one region

The trip `x := A[idx]; R := R[idx ↦ x]; idx += 1; n -= 1`, where the names `A` and `R`
have the same base. At trip `t` the cells are the words `j ≥ t` under `A` and the words
`j < t` under `R`: the store of trip `t` moves word `t` from the name `A` to the name
`R`. -/

theorem fstepF_loadN_getW {L : Layout} {dst A idx : String} {s b : LstateM} {zf z : Bool}
    (h : fstepF (loadN L dst A idx) s zf = some (b, z)) (x : String) (hx : x ≠ dst)
    (w : Nat) : b.reg.getW x w = s.reg.getW x w := by
  rw [fstepF_loadN] at h
  obtain ⟨b', hb', hbz⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hbz
  simp only [lsemStepMem, loadN, loadStruct?, if_true] at hb'
  split at hb'
  · obtain rfl := Option.some.inj hb'
    simp [hx]
  · cases hb'

theorem fstepF_storeN_getW {L : Layout} {dst A idx val : String} {s b : LstateM} {zf z : Bool}
    (h : fstepF (storeN L dst A idx val) s zf = some (b, z)) (x : String) (w : Nat) :
    b.reg.getW x w = s.reg.getW x w := by
  rw [fstepF_storeN] at h
  obtain ⟨b', hb', hbz⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hbz
  simp only [lsemStepMem, storeN, storeStruct?, if_true] at hb'
  split at hb'
  · obtain rfl := Option.some.inj hb'
    simp
  · cases hb'

/-- The name-keyed copy trip. -/
def copyTrip (L : Layout) (x A R idx n : String) : List LinstrRM :=
  [loadN L x A idx] ++ ([storeN L R R idx x] ++ ([addImmI idx idx 1] ++ [subImmI n n 1]))

/-- The pointer form of the copy trip. -/
def copyTripA (L : Layout) (scr qA qR x A R idx n : String) : List LinstrRM :=
  loadA L scr qA x A idx ++ (storeA L scr qR R R idx x
    ++ ([addImmI idx idx 1] ++ [subImmI n n 1]))

/-- The cells of the copy loop at trip `t`. -/
def copyK (L : Layout) (A R : String) (t : Nat) : String → Nat → Prop :=
  fun B j => (B = A ∧ t ≤ j ∧ j < L.len A) ∨ (B = R ∧ j < t ∧ j < L.len R)

/-- **The copy trip.** With `A` and `R` at one region, trip `t` of the name-keyed copy is
    simulated by its pointer form; the cells move from `copyK t` to `copyK (t + 1)`. -/
theorem copyTrip_simSeg {L : Layout} {frame : String → Option (BitVec 64)} {scr : String}
    (hsep : L.Sep frame) (x A R idx n qA qR : String)
    (hw : (L.base A).toNat + 8 * L.len A ≤ 2 ^ 64)
    (hAR : A ≠ R) (hbase : L.base R = L.base A) (hlen : L.len R = L.len A)
    (hqA : L.slot A = some qA) (hqR : L.slot R = some qR)
    (hidx : idx ≠ scr) (hx : x ≠ scr) (hn : n ≠ scr) (hxi : idx ≠ x) (hni : idx ≠ n)
    (t : Nat) (ht : t < L.len A) (ht64 : t < 2 ^ 64) :
    SimSeg L frame scr (copyK L A R t) (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t))
      (copyTrip L x A R idx n) (copyTripA L scr qA qR x A R idx n)
      (copyK L A R (t + 1)) (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 (t + 1))) := by
  have htn : ∀ vi : BitVec 64, some (BitVec.ofNat 64 t) = some vi → vi.toNat = t := by
    intro vi h
    obtain rfl := Option.some.inj h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht64]
  have hload := SimSeg.load (L := L) (frame := frame) (scr := scr) (copyK L A R t)
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t))
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t)) x A idx qA hqA hidx
    (fun s vi hP hvi => by
      rw [htn vi (hP ▸ hvi)]
      exact Or.inl ⟨rfl, le_refl t, ht⟩)
    (fun s zf b z hP h => by rw [fstepF_loadN_getW h idx hxi, hP])
  have hstore := SimSeg.store (L := L) (frame := frame) (scr := scr) hsep (copyK L A R t)
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t))
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t)) R R idx x qR rfl rfl hqR hidx hx
    t (hlen ▸ ht) (fun s vi hP hvi => htn vi (hP ▸ hvi))
    (fun s zf b z hP h => by rw [fstepF_storeN_getW h, hP])
  have hadd := SimSeg.reg (L := L) (frame := frame) (scr := scr)
    (afterStore L (copyK L A R t) R R t)
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t))
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 (t + 1))) (addImmI idx idx 1)
    (isRegInstr_addImmI frame idx idx 1) (regCompat_addImmI scr idx idx 1 hidx)
    (fun s zf b z hP h => by
      rw [fstepF_addImmI idx idx 1 s zf _ hP] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      simp [BitVec.ofNat_add])
  have hsub := SimSeg.reg (L := L) (frame := frame) (scr := scr)
    (afterStore L (copyK L A R t) R R t)
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 (t + 1)))
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 (t + 1))) (subImmI n n 1)
    (isRegInstr_subImmI frame n n 1)
    (regCompat_subImmI scr n n 1 hn)
    (fun s zf b z hP h => by
      rcases hs : s.reg.lvm n with ⟨w, va⟩
      rw [fstepF_subImmI n n 1 s zf va (getW_eq_some_iff.mpr hs)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      simpa [hni] using hP)
  refine (hload.append (hstore.append (hadd.append hsub))).weaken (fun _ h => h) ?_ (fun _ h => h)
  intro B j hk
  have hne : ∀ j', j' < L.len A → j' ≠ t → L.addr R j' ≠ L.addr R t := by
    intro j' hj' hjt hc
    have h1 := L.addr_toNat R j' (hlen ▸ hj') (by rw [hbase, hlen]; exact hw)
    have h2 := L.addr_toNat R t (hlen ▸ ht) (by rw [hbase, hlen]; exact hw)
    rw [hc] at h1
    omega
  have haddr : ∀ j', L.addr A j' = L.addr R j' := fun j' => by
    unfold Layout.addr; rw [hbase]
  rcases hk with ⟨rfl, hle, hj⟩ | ⟨rfl, hlt, hj⟩
  · refine Or.inr ⟨hAR, Or.inl ⟨rfl, by omega, hj⟩, ?_⟩
    rw [haddr]
    exact hne j hj (by omega)
  · by_cases hjt : j = t
    · exact Or.inl ⟨rfl, Or.inl hjt⟩
    · exact Or.inl ⟨rfl, Or.inr ⟨Or.inr ⟨rfl, by omega, hj⟩, hne j (hlen ▸ hj) hjt⟩⟩

/-! ## 10. Two-source and carry register instructions -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast

/-- An instruction whose step reads `a` at its stored width `w` and `b` at `w`, and writes
    a partial function of the two values to `dst`, is independent of `scr` when neither
    source is `scr`. -/
theorem regCompat_of_binary (scr : String) (i : LinstrRM) (dst a b : String)
    (ha : a ≠ scr) (hb : b ≠ scr)
    (hflag : ∀ p, aluFlagOp? i = some p → p.2.1 ≠ .reg scr ∧ p.2.2 ≠ .reg scr)
    (g : (w : Nat) → BitVec w → BitVec w → Option (BitVec w))
    (h : ∀ (s : LstateM) (zf : Bool) (w : Nat) (va : BitVec w), s.reg.getW a w = some va →
      fstepF i s zf = (s.reg.getW b w).bind fun vb =>
        (g w va vb).map fun v => (withALUFlags i s ((s.setReg dst v).nextPc), zf)) :
    RegCompat scr i := by
  intro s ra zf bst z heq hstep
  rcases hs : s.reg.lvm a with ⟨w, va⟩
  have hg : s.reg.getW a w = some va := getW_eq_some_iff.mpr hs
  have hga : ({ reg := ra, cf := s.cf, of := s.of } : LstateM).reg.getW a w = some va := by
    show ra.getW a w = some va
    rw [← heq.getW ha]; exact hg
  have hgb : ({ reg := ra, cf := s.cf, of := s.of } : LstateM).reg.getW b w
      = s.reg.getW b w := (heq.getW hb w).symm
  rw [h s zf w va hg] at hstep
  rw [h _ zf w va hga, hgb]
  cases hvb : s.reg.getW b w with
  | none => simp [hvb] at hstep
  | some vb =>
    cases hv : g w va vb with
    | none => simp [hvb, hv] at hstep
    | some v =>
      simp only [hvb, hv, Option.bind_some, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hstep ⊢
      obtain ⟨rfl, rfl⟩ := hstep
      have hw := withALUFlags_eqOff (i := i) hflag (s0 := s)
        (s0' := { reg := ra, cf := s.cf, of := s.of }) (b := (s.setReg dst v).nextPc)
        (b' := (({ reg := ra, cf := s.cf, of := s.of } : LstateM).setReg dst v).nextPc)
        heq ⟨rfl, rfl⟩
      refine ⟨_, ⟨rfl, rfl⟩, ?_, by rw [withALUFlags_larr]; rfl, hw.1, hw.2⟩
      rw [withALUFlags_reg, withALUFlags_reg]
      exact heq.setReg dst _

/-- An instruction whose step reads `a` at its stored width `w`, `b` at `w` and `c` at
    width 1, and writes a function of the three values to `dst`, is independent of `scr`
    when no source is `scr`. The written width is the width of the function value. -/
theorem regCompat_of_ternary (scr : String) (i : LinstrRM) (dst a b c : String)
    (ha : a ≠ scr) (hb : b ≠ scr) (hcs : c ≠ scr)
    (g : (w : Nat) → BitVec w → BitVec w → BitVec 1 → Σ w', BitVec w')
    (h : ∀ (s : LstateM) (zf : Bool) (w : Nat) (va : BitVec w), s.reg.getW a w = some va →
      fstepF i s zf = (s.reg.getW b w).bind fun vb => (s.reg.getW c 1).map fun vc =>
        ((s.setReg dst (g w va vb vc).2).nextPc, zf)) :
    RegCompat scr i := by
  intro s ra zf bst z heq hstep
  rcases hs : s.reg.lvm a with ⟨w, va⟩
  have hg : s.reg.getW a w = some va := getW_eq_some_iff.mpr hs
  have hga : ({ reg := ra, cf := s.cf, of := s.of } : LstateM).reg.getW a w = some va := by
    show ra.getW a w = some va
    rw [← heq.getW ha]; exact hg
  have hgb : ({ reg := ra, cf := s.cf, of := s.of } : LstateM).reg.getW b w
      = s.reg.getW b w := (heq.getW hb w).symm
  have hgc : ({ reg := ra, cf := s.cf, of := s.of } : LstateM).reg.getW c 1
      = s.reg.getW c 1 := (heq.getW hcs 1).symm
  rw [h s zf w va hg] at hstep
  rw [h _ zf w va hga, hgb, hgc]
  cases hvb : s.reg.getW b w with
  | none => simp [hvb] at hstep
  | some vb =>
    cases hvc : s.reg.getW c 1 with
    | none => simp [hvb, hvc] at hstep
    | some vc =>
      simp only [hvb, hvc, Option.bind_some, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hstep ⊢
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨_, ⟨rfl, rfl⟩, heq.setReg dst _, rfl, rfl, rfl⟩

/-- The two-source register instruction `opn dst, a, b`. -/
def binRegI (opn dst a b : String) : LinstrRM :=
  (LinstrR.Lopn [.reg dst] opn [.reg a, .reg b], MemTag.reg none)

/-- The carry-chain register instruction `opn dst, a, b, c`, with `c` the width-1 carry
    register. -/
def carryRegI (opn dst a b c : String) : LinstrRM :=
  (LinstrR.Lopn [.reg dst] opn [.reg a, .reg b, .reg c], MemTag.reg none)

/-- A two-source instruction whose stripped mnemonic is none of `ADC`, `SBB`, `ADCX`,
    `ADOX` is not a carry-family instruction. -/
theorem carryArgs?_binRegI {opn base dst a b : String} (hstrip : stripWidthTag opn = base)
    (hcarry : base ≠ "ADC" ∧ base ≠ "SBB" ∧ base ≠ "ADCX" ∧ base ≠ "ADOX") :
    carryArgs? (binRegI opn dst a b) = none := by
  obtain ⟨h1, h2, h3, h4⟩ := hcarry
  simp only [carryArgs?, binRegI]
  split_ifs with e1 e2 e3 e4
  · subst e1
    exact absurd (hstrip.symm.trans (by decide +kernel)) h1
  · subst e2
    exact absurd (hstrip.symm.trans (by decide +kernel)) h2
  · subst e3
    exact absurd (hstrip.symm.trans (by decide +kernel)) h3
  · subst e4
    exact absurd (hstrip.symm.trans (by decide +kernel)) h4
  · rfl

/-- The step of a two-source instruction whose stripped mnemonic `base` is an `applyOpnN`
    opcode and neither a carry-family mnemonic nor `MOV`: `b` is read at the stored width
    of `a`, `applyOpnN` is written to `dst`, and the carry and overflow flags are those of
    `withALUFlags`. -/
theorem fstepF_binRegI (opn base dst a b : String) (hstrip : stripWidthTag opn = base)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (hmul : base ≠ "MULXHI")
    (hcarry : base ≠ "ADC" ∧ base ≠ "SBB" ∧ base ≠ "ADCX" ∧ base ≠ "ADOX")
    (hmov : base ≠ "MOV")
    (s : LstateM) (zf : Bool) {w : Nat} (va : BitVec w) (hg : s.reg.getW a w = some va)
    (hset : cmpOfName? base = none := by rfl) :
    fstepF (binRegI opn dst a b) s zf = (s.reg.getW b w).bind fun vb =>
      (applyOpnN w base [va, vb]).map fun v =>
        (withALUFlags (binRegI opn dst a b) s ((s.setReg dst v).nextPc), zf) := by
  have hc : cmpArgs? (binRegI opn dst a b) = none := by
    simp only [cmpArgs?, binRegI, if_neg hcmp]
  have hm : movRegArgs? (binRegI opn dst a b) = none := rfl
  have hk := carryArgs?_binRegI (dst := dst) (a := a) (b := b) hstrip hcarry
  have hw : wideArgs? (binRegI opn dst a b) = none := by
    simp only [wideArgs?, binRegI]
    rw [if_neg]
    intro he
    subst he
    exact hmov (hstrip.symm.trans (by decide +kernel))
  have hstep : lsemStepCast (LinstrR.Lopn [.reg dst] opn [.reg a, .reg b], none) s.reg
      = (s.reg.getW b w).bind fun vb =>
          (applyOpnN w base [va, vb]).map fun v => (s.reg.setReg dst v).nextPc := by
    rw [lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ (by simp only [mulhiStruct?, hstrip, if_neg hmul])
        rfl rfl rfl rfl,
      lsemStepSh_of_not_sar _ _ rfl]
    simp only [lsemStepN, readReg_of_getW hg, evalOperandN, hstrip]
    cases s.reg.getW b w with
    | none => rfl
    | some vb => cases hv : applyOpnN w base [va, vb] <;>
      simp only [hv, hset, Option.bind_some, Option.map_some, Option.map_none]
  unfold fstepF stepMemF
  simp only [hc, hm, hk, hw]
  rw [binRegI, lsemStepMem_reg, hstep]
  cases s.reg.getW b w with
  | none => rfl
  | some vb =>
    cases hv : applyOpnN w base [va, vb] with
    | none => simp only [hv, Option.bind_some, Option.map_none]
    | some v => simp only [hv, Option.bind_some, Option.map_some]; rfl

/-- A mnemonic that `applyOpnN` evaluates on two sources is not `MOV`. -/
theorem ne_mov_of_applyOpnN {base : String} {f : BitVec 64 → BitVec 64 → BitVec 64}
    (hf : ∀ x y, applyOpnN 64 base [x, y] = some (f x y)) : base ≠ "MOV" := by
  intro he
  subst he
  simpa [applyOpnN] using hf 0 0

/-- A two-source `applyOpnN` instruction is independent of `scr` when neither source is
    `scr`. -/
theorem regCompat_binRegI (scr opn base dst a b : String) (hstrip : stripWidthTag opn = base)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (hmul : base ≠ "MULXHI")
    (hcarry : base ≠ "ADC" ∧ base ≠ "SBB" ∧ base ≠ "ADCX" ∧ base ≠ "ADOX")
    (hmov : base ≠ "MOV")
    (ha : a ≠ scr) (hb : b ≠ scr) (hset : cmpOfName? base = none := by rfl) :
    RegCompat scr (binRegI opn dst a b) :=
  regCompat_of_binary scr _ dst a b ha hb
    (fun _ hp => by
      obtain ⟨h1, h2⟩ := aluFlagOp?_ops hp
      rw [h1, h2]
      exact ⟨fun he => ha (LOperand.reg.inj he), fun he => hb (LOperand.reg.inj he)⟩)
    (fun w va vb => applyOpnN w base [va, vb])
    fun s zf _ va hg =>
      fstepF_binRegI opn base dst a b hstrip hcmp hmul hcarry hmov s zf va hg hset

theorem isRegInstr_binRegI (frame : String → Option (BitVec 64)) (opn dst a b : String)
    (hopn : opn ≠ "CMP:64") :
    IsRegInstr frame (binRegI opn dst a b) :=
  ⟨⟨none, rfl⟩, fun d src h => by simp [binRegI, slotMov?] at h,
    fun d x q h => by simp [binRegI, slotCmp?, hopn] at h, by simp [binRegI, cellA?],
    by simp [binRegI, slotCarry?], by simp [binRegI, slotImm?], by simp [binRegI, slotCmov?]⟩

theorem isRegInstr_carryRegI (frame : String → Option (BitVec 64)) (opn dst a b c : String)
    (hd : frame dst = none) (ha : frame a = none) (hb : frame b = none)
    (hc : frame c = none) :
    IsRegInstr frame (carryRegI opn dst a b c) :=
  ⟨⟨none, rfl⟩, fun d src h => by simp [carryRegI, slotMov?] at h,
    fun d x q h => by simp [carryRegI, slotCmp?] at h, by simp [carryRegI, cellA?],
    by simp [carryRegI, slotCarry?, hd, ha, hb, hc], by simp [carryRegI, slotImm?],
    by simp [carryRegI, slotCmov?, hd, hb, hc]⟩

/-- A two-source `applyOpnN` step leaves every register other than `dst` unchanged. -/
theorem fstepF_binRegI_getW {opn base dst a b : String} (hstrip : stripWidthTag opn = base)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (hmul : base ≠ "MULXHI")
    (hcarry : base ≠ "ADC" ∧ base ≠ "SBB" ∧ base ≠ "ADCX" ∧ base ≠ "ADOX")
    (hmov : base ≠ "MOV") {s bst : LstateM} {zf z : Bool}
    (h : fstepF (binRegI opn dst a b) s zf = some (bst, z)) (x : String) (hx : x ≠ dst)
    (w : Nat) (hset : cmpOfName? base = none := by rfl) : bst.reg.getW x w = s.reg.getW x w := by
  rcases hs : s.reg.lvm a with ⟨wa, va⟩
  rw [fstepF_binRegI opn base dst a b hstrip hcmp hmul hcarry hmov s zf va
    (getW_eq_some_iff.mpr hs) hset] at h
  cases hvb : s.reg.getW b wa with
  | none => simp [hvb] at h
  | some vb =>
    cases hv : applyOpnN wa base [va, vb] with
    | none => simp [hvb, hv] at h
    | some v =>
      simp only [hvb, hv, Option.bind_some, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [withALUFlags_reg, LstateM.setReg, LstateM.nextPc, hx]

theorem stripWidthTag_AND64 : stripWidthTag "AND:64" = "AND" := by decide +kernel

theorem stripWidthTag_OR64 : stripWidthTag "OR:64" = "OR" := by decide +kernel

theorem stripWidthTag_XOR64 : stripWidthTag "XOR:64" = "XOR" := by decide +kernel

/-- `AND:64 dst, a, b`. -/
def andI (dst a b : String) : LinstrRM := binRegI "AND:64" dst a b

/-- `OR:64 dst, a, b`. -/
def orI (dst a b : String) : LinstrRM := binRegI "OR:64" dst a b

/-- `XOR:64 dst, a, b`. -/
def xorI (dst a b : String) : LinstrRM := binRegI "XOR:64" dst a b

/-- `ADD:64 dst, a, b`. -/
def addI (dst a b : String) : LinstrRM := binRegI "ADD:64" dst a b

/-- `SUB:64 dst, a, b`. -/
def subI (dst a b : String) : LinstrRM := binRegI "SUB:64" dst a b

theorem regCompat_andI (scr dst a b : String) (ha : a ≠ scr) (hb : b ≠ scr) :
    RegCompat scr (andI dst a b) :=
  regCompat_binRegI scr _ "AND" dst a b stripWidthTag_AND64 (by decide +kernel) (by decide) (by decide)
    (by decide) ha hb

theorem regCompat_orI (scr dst a b : String) (ha : a ≠ scr) (hb : b ≠ scr) :
    RegCompat scr (orI dst a b) :=
  regCompat_binRegI scr _ "OR" dst a b stripWidthTag_OR64 (by decide +kernel) (by decide) (by decide)
    (by decide) ha hb

theorem regCompat_xorI (scr dst a b : String) (ha : a ≠ scr) (hb : b ≠ scr) :
    RegCompat scr (xorI dst a b) :=
  regCompat_binRegI scr _ "XOR" dst a b stripWidthTag_XOR64 (by decide +kernel) (by decide) (by decide)
    (by decide) ha hb

theorem regCompat_addI (scr dst a b : String) (ha : a ≠ scr) (hb : b ≠ scr) :
    RegCompat scr (addI dst a b) :=
  regCompat_binRegI scr _ "ADD" dst a b JasminLsemMemSourceTieUncond.stripWidthTag_ADD64
    (by decide +kernel) (by decide) (by decide) (by decide) ha hb

theorem regCompat_subI (scr dst a b : String) (ha : a ≠ scr) (hb : b ≠ scr) :
    RegCompat scr (subI dst a b) :=
  regCompat_binRegI scr _ "SUB" dst a b JasminLsemMemSourceTieUncond.stripWidthTag_SUB64
    (by decide +kernel) (by decide) (by decide) (by decide) ha hb

/-- The step of `AND:64 dst, a, b` from the two register reads. -/
theorem fstepF_andI (dst a b : String) (s : LstateM) (zf : Bool) {w : Nat}
    (va vb : BitVec w) (hga : s.reg.getW a w = some va) (hgb : s.reg.getW b w = some vb) :
    fstepF (andI dst a b) s zf
      = some (withALUFlags (andI dst a b) s ((s.setReg dst (va &&& vb)).nextPc), zf) := by
  rw [andI, fstepF_binRegI _ "AND" dst a b stripWidthTag_AND64 (by decide +kernel) (by decide)
    (by decide) (by decide) s zf va hga, hgb]
  rfl

/-! ### The carry forms

The carry forms `ADCX`, `ADCXHI`, `SBB`, `SBBHI` read the carry from a width-1 register
`c` and the carry-out forms write a width-1 register; the flag `zf` is neither read nor
written. Independence of `scr` requires `c ≠ scr` in addition to the two data sources. -/

/-- The step of `ADCX dst, a, b, c`. -/
theorem fstepF_adcx (opn dst a b c : String) (hstrip : stripWidthTag opn = "ADCX")
    (s : LstateM) (zf : Bool) {w : Nat} (va : BitVec w) (hg : s.reg.getW a w = some va) :
    fstepF (carryRegI opn dst a b c) s zf = (s.reg.getW b w).bind fun vb =>
      (s.reg.getW c 1).map fun vc => ((s.setReg dst (addCarryWord va vb vc)).nextPc, zf) := by
  have hstep : lsemStepCast (LinstrR.Lopn [.reg dst] opn [.reg a, .reg b, .reg c], none) s.reg
      = (s.reg.getW b w).bind fun vb => (s.reg.getW c 1).map fun vc =>
          (s.reg.setReg dst (addCarryWord va vb vc)).nextPc := by
    rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
    simp only [lsemStepMC, mulhiStruct?, adcxStruct?, hstrip, if_true, readReg_of_getW hg]
    cases s.reg.getW b w <;> cases s.reg.getW c 1 <;> rfl
  unfold fstepF
  simp only [show cmpArgs? (carryRegI opn dst a b c) = none from rfl,
    show movRegArgs? (carryRegI opn dst a b c) = none from rfl]
  rw [stepMemF_of_quiet rfl rfl rfl, carryRegI, lsemStepMem_reg, hstep]
  cases s.reg.getW b w <;> cases s.reg.getW c 1 <;> rfl

/-- `ADCX dst, a, b, c` is independent of `scr` when no source is `scr`. -/
theorem regCompat_adcx (scr opn dst a b c : String) (hstrip : stripWidthTag opn = "ADCX")
    (ha : a ≠ scr) (hb : b ≠ scr) (hc : c ≠ scr) : RegCompat scr (carryRegI opn dst a b c) :=
  regCompat_of_ternary scr _ dst a b c ha hb hc (fun _ va vb vc => ⟨_, addCarryWord va vb vc⟩)
    fun s zf _ va hg => fstepF_adcx opn dst a b c hstrip s zf va hg

/-- The step of `ADCXHI dst, a, b, c`: the carry-out bit is written at width 1. -/
theorem fstepF_adcxhi (opn dst a b c : String) (hstrip : stripWidthTag opn = "ADCXHI")
    (s : LstateM) (zf : Bool) {w : Nat} (va : BitVec w) (hg : s.reg.getW a w = some va) :
    fstepF (carryRegI opn dst a b c) s zf = (s.reg.getW b w).bind fun vb =>
      (s.reg.getW c 1).map fun vc => ((s.setReg dst (carryOutBit va vb vc)).nextPc, zf) := by
  have hstep : lsemStepCast (LinstrR.Lopn [.reg dst] opn [.reg a, .reg b, .reg c], none) s.reg
      = (s.reg.getW b w).bind fun vb => (s.reg.getW c 1).map fun vc =>
          (s.reg.setReg dst (carryOutBit va vb vc)).nextPc := by
    rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
    simp only [lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, hstrip, if_true,
      show ¬ ("ADCXHI" = "ADCX") by decide, if_false, readReg_of_getW hg]
    cases s.reg.getW b w <;> cases s.reg.getW c 1 <;> rfl
  unfold fstepF
  simp only [show cmpArgs? (carryRegI opn dst a b c) = none from rfl,
    show movRegArgs? (carryRegI opn dst a b c) = none from rfl]
  rw [stepMemF_of_quiet rfl rfl rfl, carryRegI, lsemStepMem_reg, hstep]
  cases s.reg.getW b w <;> cases s.reg.getW c 1 <;> rfl

/-- `ADCXHI dst, a, b, c` is independent of `scr` when no source is `scr`. -/
theorem regCompat_adcxhi (scr opn dst a b c : String) (hstrip : stripWidthTag opn = "ADCXHI")
    (ha : a ≠ scr) (hb : b ≠ scr) (hc : c ≠ scr) : RegCompat scr (carryRegI opn dst a b c) :=
  regCompat_of_ternary scr _ dst a b c ha hb hc (fun _ va vb vc => ⟨_, carryOutBit va vb vc⟩)
    fun s zf _ va hg => fstepF_adcxhi opn dst a b c hstrip s zf va hg

/-- The step of `SBB dst, a, b, c`. -/
theorem fstepF_sbb (opn dst a b c : String) (hstrip : stripWidthTag opn = "SBB")
    (s : LstateM) (zf : Bool) {w : Nat} (va : BitVec w) (hg : s.reg.getW a w = some va) :
    fstepF (carryRegI opn dst a b c) s zf = (s.reg.getW b w).bind fun vb =>
      (s.reg.getW c 1).map fun vc => ((s.setReg dst (subBorrowWord va vb vc)).nextPc, zf) := by
  have hstep : lsemStepCast (LinstrR.Lopn [.reg dst] opn [.reg a, .reg b, .reg c], none) s.reg
      = (s.reg.getW b w).bind fun vb => (s.reg.getW c 1).map fun vc =>
          (s.reg.setReg dst (subBorrowWord va vb vc)).nextPc := by
    rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
    simp only [lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?, hstrip, if_true,
      show ¬ ("SBB" = "ADCX") by decide, show ¬ ("SBB" = "ADCXHI") by decide, if_false,
      readReg_of_getW hg]
    cases s.reg.getW b w <;> cases s.reg.getW c 1 <;> rfl
  unfold fstepF
  simp only [show cmpArgs? (carryRegI opn dst a b c) = none from rfl,
    show movRegArgs? (carryRegI opn dst a b c) = none from rfl]
  rw [stepMemF_of_quiet rfl rfl rfl, carryRegI, lsemStepMem_reg, hstep]
  cases s.reg.getW b w <;> cases s.reg.getW c 1 <;> rfl

/-- `SBB dst, a, b, c` is independent of `scr` when no source is `scr`. -/
theorem regCompat_sbb (scr opn dst a b c : String) (hstrip : stripWidthTag opn = "SBB")
    (ha : a ≠ scr) (hb : b ≠ scr) (hc : c ≠ scr) : RegCompat scr (carryRegI opn dst a b c) :=
  regCompat_of_ternary scr _ dst a b c ha hb hc (fun _ va vb vc => ⟨_, subBorrowWord va vb vc⟩)
    fun s zf _ va hg => fstepF_sbb opn dst a b c hstrip s zf va hg

/-- The step of `SBBHI dst, a, b, c`: the borrow-out bit is written at width 1. -/
theorem fstepF_sbbhi (opn dst a b c : String) (hstrip : stripWidthTag opn = "SBBHI")
    (s : LstateM) (zf : Bool) {w : Nat} (va : BitVec w) (hg : s.reg.getW a w = some va) :
    fstepF (carryRegI opn dst a b c) s zf = (s.reg.getW b w).bind fun vb =>
      (s.reg.getW c 1).map fun vc => ((s.setReg dst (borrowOutBit va vb vc)).nextPc, zf) := by
  have hstep : lsemStepCast (LinstrR.Lopn [.reg dst] opn [.reg a, .reg b, .reg c], none) s.reg
      = (s.reg.getW b w).bind fun vb => (s.reg.getW c 1).map fun vc =>
          (s.reg.setReg dst (borrowOutBit va vb vc)).nextPc := by
    rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
    simp only [lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?, sbbhiStruct?,
      hstrip, if_true, show ¬ ("SBBHI" = "ADCX") by decide,
      show ¬ ("SBBHI" = "ADCXHI") by decide, show ¬ ("SBBHI" = "SBB") by decide, if_false,
      readReg_of_getW hg]
    cases s.reg.getW b w <;> cases s.reg.getW c 1 <;> rfl
  unfold fstepF
  simp only [show cmpArgs? (carryRegI opn dst a b c) = none from rfl,
    show movRegArgs? (carryRegI opn dst a b c) = none from rfl]
  rw [stepMemF_of_quiet rfl rfl rfl, carryRegI, lsemStepMem_reg, hstep]
  cases s.reg.getW b w <;> cases s.reg.getW c 1 <;> rfl

/-- `SBBHI dst, a, b, c` is independent of `scr` when no source is `scr`. -/
theorem regCompat_sbbhi (scr opn dst a b c : String) (hstrip : stripWidthTag opn = "SBBHI")
    (ha : a ≠ scr) (hb : b ≠ scr) (hc : c ≠ scr) : RegCompat scr (carryRegI opn dst a b c) :=
  regCompat_of_ternary scr _ dst a b c ha hb hc (fun _ va vb vc => ⟨_, borrowOutBit va vb vc⟩)
    fun s zf _ va hg => fstepF_sbbhi opn dst a b c hstrip s zf va hg

/-! ## 11. Instance: the AND trip

The trip `x := A[idx]; y := B[idx]; z := x AND y; R := R[idx ↦ z]; idx += 1; n -= 1`,
where `R` has the base of `A`, and `B` either has the base of `A` or occupies a region
disjoint from it. At trip `t` the cells are the words `j ≥ t` under `A`, the words `j < t`
under `R`, and under `B` the words `j ≥ t` when `B` shares the base and every word
otherwise. -/

/-- The name-keyed AND trip. -/
def andTrip (L : Layout) (x y z A B R idx n : String) : List LinstrRM :=
  [loadN L x A idx] ++ ([loadN L y B idx] ++ ([andI z x y] ++ ([storeN L R R idx z]
    ++ ([addImmI idx idx 1] ++ [subImmI n n 1]))))

/-- The pointer form of the AND trip. -/
def andTripA (L : Layout) (scr qA qB qR x y z A B R idx n : String) : List LinstrRM :=
  loadA L scr qA x A idx ++ (loadA L scr qB y B idx ++ ([andI z x y]
    ++ (storeA L scr qR R R idx z ++ ([addImmI idx idx 1] ++ [subImmI n n 1]))))

/-- The cells of the AND loop at trip `t`. -/
def andK (L : Layout) (A B R : String) (t : Nat) : String → Nat → Prop :=
  fun C j => (C = A ∧ t ≤ j ∧ j < L.len A)
    ∨ (C = B ∧ j < L.len B ∧ (L.base B = L.base A → t ≤ j))
    ∨ (C = R ∧ j < t ∧ j < L.len R)

/-- **The AND trip.** With `R` at the region of `A`, and `B` at that region or at a region
    disjoint from it, trip `t` of the name-keyed AND loop is simulated by its pointer form;
    the cells move from `andK t` to `andK (t + 1)`. -/
theorem andTrip_simSeg {L : Layout} {frame : String → Option (BitVec 64)} {scr : String}
    (hsep : L.Sep frame) (x y z A B R idx n qA qB qR : String)
    (hw : (L.base A).toNat + 8 * L.len A ≤ 2 ^ 64)
    (hAR : A ≠ R) (hBR : B ≠ R) (hbase : L.base R = L.base A) (hlen : L.len R = L.len A)
    (hlenB : L.len B = L.len A)
    (hB : L.base B = L.base A ∨
      ∀ j j', j < L.len B → j' < L.len A → L.addr B j ≠ L.addr A j')
    (hqA : L.slot A = some qA) (hqB : L.slot B = some qB) (hqR : L.slot R = some qR)
    (hidx : idx ≠ scr) (hx : x ≠ scr) (hy : y ≠ scr) (hz : z ≠ scr) (hn : n ≠ scr)
    (hxi : idx ≠ x) (hyi : idx ≠ y) (hzi : idx ≠ z) (hni : idx ≠ n)
    (t : Nat) (ht : t < L.len A) (ht64 : t < 2 ^ 64) :
    SimSeg L frame scr (andK L A B R t) (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t))
      (andTrip L x y z A B R idx n) (andTripA L scr qA qB qR x y z A B R idx n)
      (andK L A B R (t + 1)) (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 (t + 1))) := by
  have htn : ∀ vi : BitVec 64, some (BitVec.ofNat 64 t) = some vi → vi.toNat = t := by
    intro vi h
    obtain rfl := Option.some.inj h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht64]
  have hloadA := SimSeg.load (L := L) (frame := frame) (scr := scr) (andK L A B R t)
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t))
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t)) x A idx qA hqA hidx
    (fun s vi hP hvi => by
      rw [htn vi (hP ▸ hvi)]
      exact Or.inl ⟨rfl, le_refl t, ht⟩)
    (fun s zf b z hP h => by rw [fstepF_loadN_getW h idx hxi, hP])
  have hloadB := SimSeg.load (L := L) (frame := frame) (scr := scr) (andK L A B R t)
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t))
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t)) y B idx qB hqB hidx
    (fun s vi hP hvi => by
      rw [htn vi (hP ▸ hvi)]
      exact Or.inr (Or.inl ⟨rfl, hlenB ▸ ht, fun _ => le_refl t⟩))
    (fun s zf b z hP h => by rw [fstepF_loadN_getW h idx hyi, hP])
  have hand := SimSeg.reg (L := L) (frame := frame) (scr := scr) (andK L A B R t)
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t))
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t)) (andI z x y)
    (isRegInstr_binRegI frame _ z x y (by decide)) (regCompat_andI scr z x y hx hy)
    (fun s zf b z' hP h => by
      rw [fstepF_binRegI_getW stripWidthTag_AND64 (by decide +kernel) (by decide) (by decide)
        (by decide) h idx hzi, hP])
  have hstore := SimSeg.store (L := L) (frame := frame) (scr := scr) hsep (andK L A B R t)
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t))
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t)) R R idx z qR rfl rfl hqR hidx hz
    t (hlen ▸ ht) (fun s vi hP hvi => htn vi (hP ▸ hvi))
    (fun s zf b z hP h => by rw [fstepF_storeN_getW h, hP])
  have hadd := SimSeg.reg (L := L) (frame := frame) (scr := scr)
    (afterStore L (andK L A B R t) R R t)
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 t))
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 (t + 1))) (addImmI idx idx 1)
    (isRegInstr_addImmI frame idx idx 1) (regCompat_addImmI scr idx idx 1 hidx)
    (fun s zf b z hP h => by
      rw [fstepF_addImmI idx idx 1 s zf _ hP] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      simp [BitVec.ofNat_add])
  have hsub := SimSeg.reg (L := L) (frame := frame) (scr := scr)
    (afterStore L (andK L A B R t) R R t)
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 (t + 1)))
    (fun s => s.reg.getW idx 64 = some (BitVec.ofNat 64 (t + 1))) (subImmI n n 1)
    (isRegInstr_subImmI frame n n 1)
    (regCompat_subImmI scr n n 1 hn)
    (fun s zf b z hP h => by
      rcases hs : s.reg.lvm n with ⟨w, va⟩
      rw [fstepF_subImmI n n 1 s zf va (getW_eq_some_iff.mpr hs)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      simpa [hni] using hP)
  refine (hloadA.append (hloadB.append (hand.append (hstore.append
    (hadd.append hsub))))).weaken (fun _ h => h) ?_ (fun _ h => h)
  intro C j hk
  have hne : ∀ j', j' < L.len A → j' ≠ t → L.addr R j' ≠ L.addr R t := by
    intro j' hj' hjt hc
    have h1 := L.addr_toNat R j' (hlen ▸ hj') (by rw [hbase, hlen]; exact hw)
    have h2 := L.addr_toNat R t (hlen ▸ ht) (by rw [hbase, hlen]; exact hw)
    rw [hc] at h1
    omega
  have haddr : ∀ j', L.addr A j' = L.addr R j' := fun j' => by
    unfold Layout.addr; rw [hbase]
  rcases hk with ⟨rfl, hle, hj⟩ | ⟨rfl, hj, hle⟩ | ⟨rfl, hlt, hj⟩
  · refine Or.inr ⟨hAR, Or.inl ⟨rfl, by omega, hj⟩, ?_⟩
    rw [haddr]
    exact hne j hj (by omega)
  · refine Or.inr ⟨hBR, Or.inr (Or.inl ⟨rfl, hj, fun h => by have := hle h; omega⟩), ?_⟩
    rcases hB with hB | hB
    · have hBa : L.addr C j = L.addr R j := by unfold Layout.addr; rw [hB, hbase]
      rw [hBa]
      exact hne j (hlenB ▸ hj) (by have := hle hB; omega)
    · rw [← haddr]
      exact hB j t hj ht
  · by_cases hjt : j = t
    · exact Or.inl ⟨rfl, Or.inl hjt⟩
    · exact Or.inl ⟨rfl, Or.inr ⟨Or.inr (Or.inr ⟨rfl, by omega, hj⟩), hne j (hlen ▸ hj) hjt⟩⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
