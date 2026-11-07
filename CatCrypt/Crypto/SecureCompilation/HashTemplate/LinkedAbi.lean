/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernelAbi
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2Linked
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2Linked
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.KeccakLinked

/-!
# The hash template kernels at the System V calling convention

The SHA-512 compression, the BLAKE2b compression and the Keccak-f[1600] permutation as
linked functions at the System V convention (`TemplateKernelData.abiKernel`): the bytes of
`Sha2Linked.sha512Kernel`, `Blake2Linked.blake2bKernel` and `KeccakLinked.keccakFKernel`,
the bytes the executable `linked-kernel-emit` writes to the objects of
`bench/hash_linked_compare/gen/`, at the clobber sets `abiClob sha512Clob`,
`abiClob blake2bKClob` and `abiClob keccakFClob`, which leave out the callee-saved registers
`%rbx`, `%rbp`, `%r12`-`%r15`. The code saves each callee-saved register its body writes in
its frame and restores it before the return, so a C caller calls the objects directly.

## Main definitions

* `Sha2Linked.sha512KernelAbi`, `Blake2Linked.blake2bKernelAbi`,
  `KeccakLinked.keccakFKernelAbi`: the linked functions at the System V convention.

## Main statements

* `Sha2Linked.sha512KernelAbi_clob`, `Blake2Linked.blake2bKernelAbi_clob`,
  `KeccakLinked.keccakFKernelAbi_clob`: no register of the clobber set is callee-saved.
* `Sha2Linked.sha512KernelAbi_meets`, `Blake2Linked.blake2bKernelAbi_meets`,
  `KeccakLinked.keccakFKernelAbi_meets`: the code meets the contract.
* `Sha2Linked.sha512KernelAbi_linked`, `Blake2Linked.blake2bKernelAbi_linked`,
  `KeccakLinked.keccakFKernelAbi_linked`: the linked functions are linked kernels of the out
  shape, with the destination at `%rdi`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.HashTemplate
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedKernel)
open CatCrypt.Crypto.Hax (LinkedFn)

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2Linked

/-- **The SHA-512 compression at the System V convention**: the code of `sha512Kernel` at the
    clobber set `abiClob sha512Clob`. -/
def sha512KernelAbi : LinkedFn := (sha512Data sha512Frame sha512Frame_fit).abiKernel sha512_check

/-- No register the SHA-512 compression may change at the System V convention is
    callee-saved. -/
theorem sha512KernelAbi_clob :
    ∀ x ∈ sha512KernelAbi.clob, x ∉ X86Backend.AsmPrinter.calleeSavedRegs :=
  TemplateKernelData.abiKernel_clob sha512_check

/-- **The code of the SHA-512 compression meets the contract at the System V convention.** -/
theorem sha512KernelAbi_meets : sha512KernelAbi.Meets :=
  TemplateKernelData.meets_abi sha512_check

/-- **The SHA-512 compression at the System V convention is a linked kernel** of the out
    shape, with the destination at `%rdi`. -/
theorem sha512KernelAbi_linked : LinkedKernel sha512KernelAbi :=
  TemplateKernelData.linked_abi (po := "RDI") sha512_check
    ((layoutIns_redLayout _ _).trans sha512_ins)
    ((congrArg (List.map _) (redLayout_args _ _)).trans sha512_args)
    (by simp [sha512Data]) (by decide) rfl

end CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2Linked

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2Linked

/-- **The BLAKE2b compression at the System V convention**: the code of `blake2bKernel` at
    the clobber set `abiClob blake2bKClob`. -/
def blake2bKernelAbi : LinkedFn :=
  (blake2bKData blake2bKFrame blake2bKFrame_fit).abiKernel blake2bK_check

/-- No register the BLAKE2b compression may change at the System V convention is
    callee-saved. -/
theorem blake2bKernelAbi_clob :
    ∀ x ∈ blake2bKernelAbi.clob, x ∉ X86Backend.AsmPrinter.calleeSavedRegs :=
  TemplateKernelData.abiKernel_clob blake2bK_check

/-- **The code of the BLAKE2b compression meets the contract at the System V convention.** -/
theorem blake2bKernelAbi_meets : blake2bKernelAbi.Meets :=
  TemplateKernelData.meets_abi blake2bK_check

/-- **The BLAKE2b compression at the System V convention is a linked kernel** of the out
    shape, with the destination at `%rdi`. -/
theorem blake2bKernelAbi_linked : LinkedKernel blake2bKernelAbi :=
  TemplateKernelData.linked_abi (po := "RDI") blake2bK_check
    ((layoutIns_redLayout _ _).trans blake2bK_ins)
    ((congrArg (List.map _) (redLayout_args _ _)).trans blake2bK_args)
    (by simp [blake2bKData]) (by decide) rfl

end CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2Linked

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.KeccakLinked

/-- **The Keccak-f[1600] permutation at the System V convention**: the code of
    `keccakFKernel` at the clobber set `abiClob keccakFClob`. -/
def keccakFKernelAbi : LinkedFn :=
  (keccakFData keccakFFrame keccakFFrame_fit).abiKernel keccakF_check

/-- No register the Keccak-f[1600] permutation may change at the System V convention is
    callee-saved. -/
theorem keccakFKernelAbi_clob :
    ∀ x ∈ keccakFKernelAbi.clob, x ∉ X86Backend.AsmPrinter.calleeSavedRegs :=
  TemplateKernelData.abiKernel_clob keccakF_check

/-- **The code of the Keccak-f[1600] permutation meets the contract at the System V
    convention.** -/
theorem keccakFKernelAbi_meets : keccakFKernelAbi.Meets :=
  TemplateKernelData.meets_abi keccakF_check

/-- **The Keccak-f[1600] permutation at the System V convention is a linked kernel** of the
    out shape, with the destination at `%rdi`. -/
theorem keccakFKernelAbi_linked : LinkedKernel keccakFKernelAbi :=
  TemplateKernelData.linked_abi (po := "RDI") keccakF_check
    ((layoutIns_redLayout _ _).trans keccakF_ins)
    ((congrArg (List.map _) (redLayout_args _ _)).trans keccakF_args)
    (by simp [keccakFData]) (by decide) rfl

end CatCrypt.Crypto.SecureCompilation.HashTemplate.KeccakLinked
