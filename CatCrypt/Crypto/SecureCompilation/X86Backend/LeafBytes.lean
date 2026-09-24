/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject

/-!
# `emitLeafBytes` — one library entry point for a bytes-direct ABI-wrapped leaf

The eleven `bench/bytes_direct_*/` demos each COPY-PASTE the same scaffolding to
turn a verified straight-line `JInstr 64` block into a linkable `.o`:

* a trusted `pushq`-prologue / `popq …`-epilogue byte sequence (the encoder has no
  push/pop/ret arm; these are the documented trusted leaf-ABI framing);
* the verified-encoder bytes of the System-V argument-marshalling reg-reg `MOV`s
  (e.g. `movq %rdx, <yreg>` to free `%rdx` for `MULX`);
* `ScalarEncoder.encodeJBlock alloc block` for the `runBlock`-verified body
  (the result `storeMem` writes are part of the block, so there is no separate
  "result store" step);
* the ELF64 object stitching (`ElfObject.buildElfObjectMulti`).

This module factors the first three into ONE function, `emitLeafBytes`, that
returns the leaf's `.text` bytes as an `ElfObject.Leaf`. The object is then
`ElfObject.buildElfObjectMulti [leaf]` (the `gas -o foo.o` analogue with `gas`
removed) — re-using the already-proved multi-symbol stitcher rather than each
demo re-deriving the ELF assembly.

This mirrors `AsmPrinter.renderSysVLeafFn` (which renders the SAME ABI glue as
AT&T `.s` text), with one deliberate deviation: `renderSysVLeafFn` uses the leaf
**red-zone** save idiom (`movq %reg, -8*(i+1)(%rsp)`), which needs an `%rsp`-
relative store the verified `encMemMov` cannot encode (it would require a SIB
byte). The bytes path therefore uses explicit `pushq`/`popq` framing — exactly
what the demos already emit, and what `renderLeafFn` renders for the text-path
differential baseline. The push/pop framing is the trusted leaf scaffold; the
arg-marshal moves and the whole body are verified-encoder output.

## Trust tier

The encoder bytes are gas-pinned per `ScalarValidation` (`decode∘encode = id` on
the GP-ALU subset, plus the differential KAT against the gas-assembled `.s`).
The `pushq`/`popq`/`ret` framing bytes are the standard trusted leaf scaffold
(no encoder arm), the same trust tier the demos already carry. No open goals, no
custom axiom is introduced here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder

/-! ## 1. The trusted push/pop/ret framing bytes -/

/-- The `pushq %rN` bytes: an optional `REX.B` (`0x41`) when `N ≥ 8`, then the
    `0x50 + (N &&& 7)` single-byte `PUSH r64` opcode. `pushq %rbx` (N=3) → `0x53`;
    `pushq %r12` (N=12) → `0x41 0x54`. (The trusted leaf scaffold: the encoder has
    no `PUSH` arm.) -/
def encPushReg (r : String) : List (BitVec 8) :=
  let n := gpNum r
  let opc := 0x50 + (n &&& 7)
  (if bit n 3 = 1 then [0x41, opc] else [opc]).map (BitVec.ofNat 8)

/-- The `popq %rN` bytes: an optional `REX.B` (`0x41`) when `N ≥ 8`, then the
    `0x58 + (N &&& 7)` single-byte `POP r64` opcode. `popq %rbx` (N=3) → `0x5b`;
    `popq %r12` (N=12) → `0x41 0x5c`. -/
def encPopReg (r : String) : List (BitVec 8) :=
  let n := gpNum r
  let opc := 0x58 + (n &&& 7)
  (if bit n 3 = 1 then [0x41, opc] else [opc]).map (BitVec.ofNat 8)

/-- The single `ret` byte (`0xC3`). -/
def encRet : List (BitVec 8) := [BitVec.ofNat 8 0xC3]

/-- The prologue bytes: `pushq` each saved register in the given order. -/
def prologueBytes (savedRegs : List String) : List (BitVec 8) :=
  savedRegs.flatMap encPushReg

/-- The epilogue bytes: `popq` each saved register in **reverse** order (the LIFO
    mirror of the prologue), then `ret`. -/
def epilogueBytes (savedRegs : List String) : List (BitVec 8) :=
  savedRegs.reverse.flatMap encPopReg ++ encRet

/-! ## 2. The verified argument-marshalling bytes

This is the byte image of `AsmPrinter.argMarshalMoves`: for each `intPtr`
argument `i` whose allocation binds its name to a register **different** from its
System-V home register `intArgHome i`, emit `movq %home, %dst` — the verified
reg-reg `MOV` (`encAluRR 0x89`, `reg`=src=home, `rm`=dst). When a name is already
in its home register (the common pointer-argument case, e.g. `z`→`%rdi`) no move
is emitted, exactly matching `argMarshalMoves`'s `if dst == home then none`. -/

/-- The arg-marshalling bytes: the verified-encoder image of `argMarshalMoves`. -/
def argMarshalBytes (alloc : GpAlloc) (args : List AbiArg) : List (BitVec 8) :=
  (args.zipIdx.filterMap (fun (a, i) =>
    match a.cls, intArgHome i with
    | .intPtr, some home =>
        let dst := regOf alloc a.name
        if dst == home then none
        else some (encAluRR 0x89 (gpNum dst) (gpNum home))
    | _, none => none)).flatten

/-! ## 3. The library entry point -/

/-- Build a bytes-direct System-V AMD64 leaf as an `ElfObject.Leaf`:

    `.text = prologue (pushq savedRegs) ++ argMarshalBytes ++ encodeJBlock block
             ++ epilogue (popq savedRegs reversed ++ ret)`

    * `name`      — the global `STT_FUNC` symbol name;
    * `alloc`     — the register allocation the proved lowering uses (so the bytes
                    and the proof agree on placement);
    * `args`      — the System-V argument signature (drives the marshal moves);
    * `block`     — the `runBlock`-verified straight-line body, **including** its
                    result `storeMem` writes;
    * `savedRegs` — the callee-saved registers to `pushq`/`popq` frame (typically
                    `AsmPrinter.usedCalleeSaved alloc`).

    The single object is `ElfObject.buildElfObjectMulti [emitLeafBytes …]`. Mirrors
    `AsmPrinter.renderSysVLeafFn` (which renders the same glue as `.s` text) but
    emits BYTES and uses explicit `pushq`/`popq` framing (the encoder cannot emit
    the red-zone `%rsp`-relative save). -/
def emitLeafBytes (name : String) (alloc : GpAlloc) (args : List AbiArg)
    (block : List (JInstr 64)) (savedRegs : List String) : ElfObject.Leaf :=
  { name := name
  , text :=
      prologueBytes savedRegs
        ++ argMarshalBytes alloc args
        ++ encodeJBlock alloc block
        ++ epilogueBytes savedRegs }

/-- The complete single-leaf ELF64 `.o` bytes for a bytes-direct leaf: the
    `gas -o foo.o` analogue with `gas` removed. Re-uses the already-proved
    multi-symbol stitcher `ElfObject.buildElfObjectMulti`. -/
def emitLeafObject (name : String) (alloc : GpAlloc) (args : List AbiArg)
    (block : List (JInstr 64)) (savedRegs : List String) : List (BitVec 8) :=
  ElfObject.buildElfObjectMulti [emitLeafBytes name alloc args block savedRegs]

/-! ## 4. Structural sanity (the `.text` is exactly the four glued segments)

The leaf's `.text` is, definitionally, the prologue ++ marshal ++ body ++
epilogue — the same four-segment shape the demos hand-glue. This `rfl` pins that
the library introduces no reordering or padding between the segments. -/

@[simp] theorem emitLeafBytes_text (name : String) (alloc : GpAlloc)
    (args : List AbiArg) (block : List (JInstr 64)) (savedRegs : List String) :
    (emitLeafBytes name alloc args block savedRegs).text
      = prologueBytes savedRegs ++ argMarshalBytes alloc args
          ++ encodeJBlock alloc block ++ epilogueBytes savedRegs := rfl

/-- The single-leaf object is exactly the one-element multi-symbol stitch. -/
@[simp] theorem emitLeafObject_eq (name : String) (alloc : GpAlloc)
    (args : List AbiArg) (block : List (JInstr 64)) (savedRegs : List String) :
    emitLeafObject name alloc args block savedRegs
      = ElfObject.buildElfObjectMulti [emitLeafBytes name alloc args block savedRegs] :=
  rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes
