/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2LinkedData
import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2LinkedData
import CatCrypt.Crypto.SecureCompilation.HashTemplate.KeccakLinkedData
import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernel
import CatCrypt.Crypto.SecureCompilation.HashTemplate.LinkedKernelEmit
import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.Compiled
import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.CompiledOptAdd
import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.CompiledAndBool

set_option autoImplicit false
set_option compiler.extract_closed false

/-!
# `linked-kernel-emit`: the bytes of the region-compiled template kernels as ELF objects

The root of an executable, imported by no module. Each row evaluates `frameCompile` (the region
back half at the frame of the code) on one straight-line kernel under the layout of its linked
function, and writes the bytes it returns as an ELF64 relocatable object
(`ElfObject.buildElfObject`) with one global symbol (`LinkedKernelEmit.runRow`). By
`frameCompile_spec` these are the bytes that `compileRegion` returns at `redLayout σ F`, the
layout of the kernel's linked function at the frame `F` of its code.

| row | program | layout | object | symbol |
|---|---|---|---|---|
| `sha512_compress` | `sha2CompressBodyP sha512P` | `Sha2Linked.sha512Abi` | `bench/hash_linked_compare/gen/sha512_compress.o` | `catcrypt_sha512_compress` |
| `sha256_compress` | `sha2CompressBodyP sha256P` | `Sha2Linked.sha256Abi` | `bench/hash_linked_compare/gen/sha256_compress.o` | `catcrypt_sha256_compress` |
| `blake2b_compress` | `blake2CompressBodyP blake2bP` | `Blake2Linked.blake2bKAbi` | `bench/hash_linked_compare/gen/blake2b_compress.o` | `catcrypt_blake2b_compress` |
| `keccak_f1600` | `KeccakLinked.keccakFLayoutBody` | `KeccakLinked.keccakFAbi` | `bench/hash_linked_compare/gen/keccak_f1600.o` | `catcrypt_keccak_f1600` |
| `aeneas_incr_array` | `AeneasFront.Demo.incrArraySrc` | `AeneasFront.Demo.incrAbi` | `bench/aeneas_front/gen/incr_array.o` | `catcrypt_aeneas_incr_array` |
| `aeneas_opt_add` | `AeneasFront.Demo.optAddSrc` | `AeneasFront.Demo.optAddAbi` | `bench/aeneas_front/gen/opt_add_1_or_panic.o` | `catcrypt_aeneas_opt_add` |
| `aeneas_and_bool` | `AeneasFront.Demo.andBoolSrc` | `AeneasFront.Demo.andBoolAbi` | `bench/aeneas_front/gen/and_bool.o` | `catcrypt_aeneas_and_bool` |

The rows `aeneas_incr_array`, `aeneas_opt_add` and `aeneas_and_bool` are not kernels: they
evaluate the compiler of the Aeneas front, `NFEntry.compileR` at `aeneasEntry`, on the output of
`reifyAeneas%` for `arrays.incr_array`, `joins.opt_add_1_or_panic` and `bitwise.and_bool` of the
Aeneas tests; their bytes are those of `incrArray_compileR_correct` and `incrArray_compileR_ct`
(`AeneasFront/Demo/Compiled.lean`), of `optAdd_compileR_correct` and `optAdd_compileR_ct`
(`AeneasFront/Demo/CompiledOptAdd.lean`) and of `andBool_compileR_correct` and
`andBool_compileR_ct` (`AeneasFront/Demo/CompiledAndBool.lean`). They have no frame of their own
code and no read-only flag; the line prints `-` in both columns.

The row `sha256_compress` compiles a template over 32-bit words at the u64-slot layout: the back
half widens its words to 64-bit slots with zero high bits (`compileRegion`); it has no linked
function.

The linked functions are `Sha2Linked.sha512Kernel`, `Blake2Linked.blake2bKernel` and
`KeccakLinked.keccakFKernel`. The same bytes at the System V calling convention, with clobber
sets that hold no callee-saved register (the code saves and restores each one its body
writes), are the linked functions `Sha2Linked.sha512KernelAbi`, `Blake2Linked.blake2bKernelAbi`
and `KeccakLinked.keccakFKernelAbi` (module `LinkedAbi`), so a C caller calls the objects
directly.

The command line and the printed line of a row are those of `LinkedKernelEmit.runCli`.

## Main definitions

* `rows`: the three kernels, the SHA-256 compression at the u64-slot layout and the three
  compiler rows of the Aeneas front, each with its program, layout, output path and symbol.
* `frameProgs`: the programs of the frame rows.
* `main`: the command line `LinkedKernelEmit.runCli` over these rows.
-/

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.LinkedKernelEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2Linked (sha512Abi sha256Abi)
open CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2Linked (blake2bKAbi)
open CatCrypt.Crypto.SecureCompilation.HashTemplate.KeccakLinked (keccakFAbi keccakFLayoutBody)

/-- The rows of the executable. -/
def rows : List Row :=
  [ { name := "sha512_compress", sym := "catcrypt_sha512_compress"
      path := "bench/hash_linked_compare/gen/sha512_compress.o"
      call := fun _ => rowFrameCompile sha512Abi "sha512_compress"
        (NFProg.ofCom (sha2CompressBodyP sha512P)) },
    { name := "sha256_compress", sym := "catcrypt_sha256_compress"
      path := "bench/hash_linked_compare/gen/sha256_compress.o"
      call := fun _ => rowFrameCompile sha256Abi "sha256_compress"
        (NFProg.ofCom (sha2CompressBodyP sha256P)) },
    { name := "blake2b_compress", sym := "catcrypt_blake2b_compress"
      path := "bench/hash_linked_compare/gen/blake2b_compress.o"
      call := fun _ => rowFrameCompile blake2bKAbi "blake2b_compress"
        (NFProg.ofCom (blake2CompressBodyP blake2bP)) },
    { name := "keccak_f1600", sym := "catcrypt_keccak_f1600"
      path := "bench/hash_linked_compare/gen/keccak_f1600.o"
      call := fun _ => rowFrameCompile keccakFAbi "keccak_f" (NFProg.ofCom keccakFLayoutBody) },
    { name := "aeneas_incr_array", sym := "catcrypt_aeneas_incr_array"
      path := "bench/aeneas_front/gen/incr_array.o"
      call := fun _ => aeneasBytes AeneasFront.Demo.incrArraySrc AeneasFront.Demo.incrAbi
        "incr_array" },
    { name := "aeneas_opt_add", sym := "catcrypt_aeneas_opt_add"
      path := "bench/aeneas_front/gen/opt_add_1_or_panic.o"
      call := fun _ => aeneasBytes AeneasFront.Demo.optAddSrc AeneasFront.Demo.optAddAbi
        "opt_add_1_or_panic" },
    { name := "aeneas_and_bool", sym := "catcrypt_aeneas_and_bool"
      path := "bench/aeneas_front/gen/and_bool.o"
      call := fun _ => aeneasBytes AeneasFront.Demo.andBoolSrc AeneasFront.Demo.andBoolAbi
        "and_bool" } ]

/-- The programs of the frame rows. -/
def frameProgs : List (String × (Unit → Option FrameProg)) :=
  [ ("sha512_compress", fun _ => some ⟨_, _, NFProg.ofCom (sha2CompressBodyP sha512P)⟩),
    ("sha256_compress", fun _ => some ⟨_, _, NFProg.ofCom (sha2CompressBodyP sha256P)⟩),
    ("blake2b_compress", fun _ => some ⟨_, _, NFProg.ofCom (blake2CompressBodyP blake2bP)⟩),
    ("keccak_f1600", fun _ => some ⟨_, _, NFProg.ofCom keccakFLayoutBody⟩) ]

end CatCrypt.Crypto.SecureCompilation.HashTemplate.LinkedKernelEmit

open CatCrypt.Crypto.SecureCompilation.HashTemplate.LinkedKernelEmit in
/-- The command line of `linked-kernel-emit` (`LinkedKernelEmit.runCli`). -/
def main (args : List String) : IO UInt32 :=
  runCli "linked-kernel-emit" rows frameProgs args
