/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

@[expose] public section

set_option autoImplicit false

/-!
# The FRONT-sourced runtime-N mpn loop kernels as verified-encoder ELF objects

The five deployed `mpn_{add,sub,and,ior,xor}_n_loop_owned` kernels
(`MpnLoopFrontEmit`: rolled-loop front → `ComL.toLprogPhysAbi(-ScalarAcc)`
owned-RA `Lprog`) byte-encoded by the looped-backend encoder
(`LprogBytes.encodeLprogChecked`: two-pass label resolution with rel8/rel32
relaxation, SIB streaming operands, the reg-reg `CMP` loop guard) and stitched
into single-symbol ELF64 relocatable objects (`ElfObject.buildElfObjectMulti`).
No assembler is on this artifact path: the `.o` under
`bench/integration_owned/gen_bytes/` are encoder output, byte for byte.

Each object carries the same deployed symbol as the `renderLprogAtt` `.s`
route (`bench/integration/gen_com/`), so the `integration_owned` seam links
either kernel set through one adapter and one conformance driver — and
`make -C bench/integration_owned diff-bytes` compares the two `.text`s
byte-for-byte, with GNU `as` demoted from trusted assembler to differential
oracle.

The `#guard`s pin, at compile time and with no axiom, that every front `Lprog`
is inside the byte encoder's fragment (`encodableLcmd` per function body), so
the gated encoder returns `some` and the driver cannot write an object short by
an instruction.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopBytesEmit

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

/-- The gated object bytes of a front-compiled `Lprog`: `none` when the front
    declined the source or a body instruction is outside the encoder fragment. -/
def objBytes (p : Option Lprog) : Option (List (BitVec 8)) :=
  p.bind encodeLprogChecked

/-- The eight seam kernels, keyed by their artifact base name: the five
    arithmetic/logical kernels and the three adapter kernels the seam calls
    for zero-extension and length normalization. -/
def kernels (_ : Unit) : List (String × Option Lprog) :=
  [ ("mpn_add_n_loop_owned", MpnLoopFrontEmit.addLprogFront ())
  , ("mpn_sub_n_loop_owned", MpnLoopFrontEmit.subLprogFront ())
  , ("mpn_and_n_loop_owned", MpnLoopFrontEmit.andLprog ())
  , ("mpn_ior_n_loop_owned", MpnLoopFrontEmit.iorLprog ())
  , ("mpn_xor_n_loop_owned", MpnLoopFrontEmit.xorLprog ())
  , ("mpn_copyi_loop_owned", MpnLoopFrontEmit.copyLprog ())
  , ("mpn_zero_loop_owned", MpnLoopFrontEmit.zeroLprog ())
  , ("mpn_norm_u32len_loop_owned", MpnLoopFrontEmit.normLprogFront ()) ]

/- Every seam kernel is inside the byte encoder's fragment: the front
compiled it (`isSome`) and every body instruction reaches the byte stream
(`encodableLcmd`), so the gated object encoder returns `some`. -/
#guard (objBytes (MpnLoopFrontEmit.addLprogFront ())).isSome
#guard (objBytes (MpnLoopFrontEmit.subLprogFront ())).isSome
#guard (objBytes (MpnLoopFrontEmit.andLprog ())).isSome
#guard (objBytes (MpnLoopFrontEmit.iorLprog ())).isSome
#guard (objBytes (MpnLoopFrontEmit.xorLprog ())).isSome
#guard (objBytes (MpnLoopFrontEmit.copyLprog ())).isSome
#guard (objBytes (MpnLoopFrontEmit.zeroLprog ())).isSome
#guard (objBytes (MpnLoopFrontEmit.normLprogFront ())).isSome

/- Each object exports exactly its own deployed symbol (one function per front
`Lprog`, named as the seam links it). -/
#guard (kernels ()).all (fun (n, p) =>
  (p.map (fun q => q.lp_funcs.map Prod.fst == [n])).getD false)

/-- Byte-list to `ByteArray`, for `IO.FS.writeBinFile`. -/
def toByteArray (bs : List (BitVec 8)) : ByteArray :=
  ⟨(bs.map (fun b => UInt8.ofNat b.toNat)).toArray⟩

/-- The five arithmetic/logical kernels the `catcrypt-mpn` crate links, keyed
    by the object name the crate's `build.rs` archives. -/
def crateKernels (_ : Unit) : List (String × Option Lprog) :=
  [ ("mpn_add_n_loop_owned", MpnLoopFrontEmit.addLprogFront ())
  , ("mpn_sub_n_loop_owned", MpnLoopFrontEmit.subLprogFront ())
  , ("mpn_and_n_loop_owned", MpnLoopFrontEmit.andLprog ())
  , ("mpn_ior_n_loop_owned", MpnLoopFrontEmit.iorLprog ())
  , ("mpn_xor_n_loop_owned", MpnLoopFrontEmit.xorLprog ()) ]

/-- Write the eight seam kernels' verified-encoder ELF objects into
    `bench/integration_owned/gen_bytes/`, and the five the crate links into
    `crates/catcrypt-mpn/obj/`, at elaboration so lake owns the dependency.
    Fails rather than writing a truncated object when a kernel is outside the
    encoder fragment. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/integration_owned/gen_bytes"
  for (name, p) in kernels () do
    match objBytes p with
    | some bs =>
        IO.FS.writeBinFile
          s!"bench/integration_owned/gen_bytes/{name}_bytes.o" (toByteArray bs)
    | none =>
        throw (IO.userError
          s!"{name}: front declined or body outside the byte-encoder fragment")
  -- The crate links the encoder objects directly, so write them into the
  -- crate's own obj/ from the same bytes: the artifact the crate ships is the
  -- encoder's output, drift-proof against a stale hand copy.
  IO.FS.createDirAll "crates/catcrypt-mpn/obj"
  for (name, p) in crateKernels () do
    match objBytes p with
    | some bs =>
        IO.FS.writeBinFile
          s!"crates/catcrypt-mpn/obj/{name}.o" (toByteArray bs)
    | none =>
        throw (IO.userError s!"{name}: outside the byte-encoder fragment")
  IO.println "wrote verified-encoder ELF objects for the 8 mpn seam kernels + the crate obj/"

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopBytesEmit
