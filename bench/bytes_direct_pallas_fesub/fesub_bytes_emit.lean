/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors

Pallas base-field subtract leaf, verified-bytes-direct + text-path differential KAT.

Mirrors `../SSProve-lean/bench/bytes_direct_p256_fesub/fesub_bytes_emit.lean`, but for the Pasta
Pallas base field
  p = 2^254 + 45560315531419706090280762371685220353
    = 0x40000000…224698fc094cf91b992d30ed00000001  (255-bit).
This is a concrete instantiation of the prime-parametrized completed subtract
(`EcFeSubComplete.feSubFrameComplete` / `EcFeSubPastaComplete.feSubFrameAtPallas_value`),
demonstrating the generic masked add-back at a Pasta prime (non-trivial top limb
`0x4000000000000000 < 2^63`, zero middle limb `p2 = 0`). The kernel is:

  d = x − y  (4-limb SBB borrow chain, CF = borrow)
  m = 0 − CF (all-ones iff a borrow occurred)
  t_i = p_i & m   (masked prime limbs, all four)
  d += t   (full-width masked add-back of the prime, carry discarded)
  store d

Pallas prime little-endian limbs:
  p0 = 0x992d30ed00000001, p1 = 0x224698fc094cf91b,
  p2 = 0x0000000000000000, p3 = 0x4000000000000000

Invoke: lake env lean bench/bytes_direct_pallas_fesub/fesub_bytes_emit.lean
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes

@[expose] public section

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject

/-! ## 1. The Pallas base-field subtract block

`z := (x − y) mod (2^254 + 45560315531419706090280762371685220353)`, branchless.
The masked add-back of the full prime `p` on borrow, all four limbs masked. -/
def pallasSubBlock : List (JInstr 64) :=
  [ .loadMem "d0" "x" 0
  , .loadMem "lo" "y" 0,  .sub "d0" (.reg "lo")
  , .loadMem "d1" "x" 8
  , .loadMem "lo" "y" 8,  .sbb "d1" (.reg "lo")
  , .loadMem "d2" "x" 16
  , .loadMem "lo" "y" 16, .sbb "d2" (.reg "lo")
  , .loadMem "d3" "x" 24
  , .loadMem "lo" "y" 24, .sbb "d3" (.reg "lo")
  -- mask m = 0 − CF  (all-ones iff borrow)
  , .mov "m" (.imm 0), .sbb "m" (.imm 0)
  -- masked prime limbs t_i = p_i & m  (all four; then the ADC ripple-add)
  , .mov "t0" (.imm 0x992d30ed00000001), .and_ "t0" (.reg "m")
  , .mov "t1" (.imm 0x224698fc094cf91b), .and_ "t1" (.reg "m")
  , .mov "t2" (.imm 0x0000000000000000), .and_ "t2" (.reg "m")
  , .mov "t3" (.imm 0x4000000000000000), .and_ "t3" (.reg "m")
  , .add "d0" (.reg "t0")
  , .adc "d1" (.reg "t1")
  , .adc "d2" (.reg "t2")
  , .adc "d3" (.reg "t3")
  , .storeMem "z" 0 (.reg "d0")
  , .storeMem "z" 8 (.reg "d1")
  , .storeMem "z" 16 (.reg "d2")
  , .storeMem "z" 24 (.reg "d3") ]

/-- Pointer args pinned to their System-V homes: `out=z`→%rdi, `a=x`→%rsi,
    `b=y`→%rdx. -/
def pallasSubPinned : GpAlloc := [("z", "%rdi"), ("x", "%rsi"), ("y", "%rdx")]

/-- The full allocation: pinned pointers + internal SSA names to the GP pool. -/
def pallasSubAlloc : GpAlloc := allocGp pallasSubPinned pallasSubBlock

def pallasSubArgs : List AbiArg :=
  [ ⟨"z", .intPtr⟩, ⟨"x", .intPtr⟩, ⟨"y", .intPtr⟩ ]

def pallasSubSaved : List String := usedCalleeSaved pallasSubAlloc

def pallasSubLeaf : Leaf :=
  emitLeafBytes "pallas_fe_sub" pallasSubAlloc pallasSubArgs pallasSubBlock pallasSubSaved

def pallasSubTextBytes : List (BitVec 8) := pallasSubLeaf.text

def pallasSubElfObject : List (BitVec 8) := buildElfObjectMulti [pallasSubLeaf]

def pallasSubTextS : String :=
  renderLeafFn "pallas_fe_sub"
    (pallasSubSaved.map (fun r => "\tpushq " ++ r))
    (renderBlockBody pallasSubAlloc pallasSubBlock)
    (pallasSubSaved.reverse.map (fun r => "\tpopq " ++ r) ++ [ "\tret" ])

/-! ## 2. Driver -/

def hexOf (bs : List (BitVec 8)) : String :=
  let digits : List Char := "0123456789abcdef".toList
  let nib : Nat → Char := fun k => digits[k]?.getD '?'
  let hexByte : BitVec 8 → String := fun b =>
    let n := b.toNat; String.ofList [nib (n / 16), nib (n % 16)]
  String.intercalate " " (bs.map hexByte)

def toByteArray (bs : List (BitVec 8)) : ByteArray :=
  ⟨(bs.map (fun b => UInt8.ofNat b.toNat)).toArray⟩

def main : IO Unit := do
  IO.FS.createDirAll "bench/bytes_direct_pallas_fesub/gen"
  IO.FS.writeBinFile "bench/bytes_direct_pallas_fesub/gen/pallas_fe_sub_bytes.o"
    (toByteArray pallasSubElfObject)
  IO.FS.writeFile "bench/bytes_direct_pallas_fesub/gen/pallas_fe_sub_text.s" pallasSubTextS
  IO.FS.writeFile "bench/bytes_direct_pallas_fesub/gen/pallas_fe_sub_text_bytes.hex"
    (hexOf pallasSubTextBytes ++ "\n")
  IO.println s!"WROTE gen/pallas_fe_sub_bytes.o  ({pallasSubElfObject.length} bytes ELF64 .o, no assembler)"
  IO.println s!"WROTE gen/pallas_fe_sub_text.s   (text path, for the as-baseline KAT)"
  IO.println s!"pallas_fe_sub .text = {pallasSubTextBytes.length} bytes:"
  IO.println ("  " ++ hexOf pallasSubTextBytes)

#eval main
