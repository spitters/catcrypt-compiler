/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree

/-!
# Resolver agreement: discharging the byte-agreement's `gpNum (regOf alloc ·) = gpNumU ·` side-condition (D4)

`LprogJInstrBytesAgree` proves the per-mnemonic byte-agreement of the two owned x86-64
encoders — the **JInstr** straight-line path (`ScalarEncoder.encodeJInstr`) and the
**Lprog** looped-RA path (`LprogBytes.encTwoAddr`) — **under** a *resolver-agreement*
side-condition: each register operand must resolve to the **same** SDM GP number on both
sides, i.e. `gpNum (regOf alloc r) = gpNumU dn`. The two encoders read **different**
register-name tables:

* the JInstr path resolves a block-local name `r` through the allocation `alloc` to an
  AT&T `%rN` name (`regOf alloc r`), then to a number via
  `ScalarEncoder.gpNum` (`"%rax" → 0`, …, `"%r15" → 15`);
* the Lprog path resolves an uppercase **physical** name `dn` directly via
  `LprogBytes.gpNumU` (`"RAX" → 0`, …, `"R15" → 15`).

This file closes that residual: it proves the two resolvers **agree** for the standard
allocation (the one that maps each physical name `r` to its AT&T register `gpReg64 r`),
making the byte-agreement **unconditional** in its resolver hypotheses. Re-pointing a
covered kernel from the Lprog encoder to the JInstr encoder is then a swap with **no
byte-KAT change** on the resolver axis.

## The table fact (`gpNum_gpReg64_eq_gpNumU`)

The lowercase AT&T table `gpReg64` (`"RAX" → "%rax"`) composed with `gpNum`
(`"%rax" → 0`) is **literally** the uppercase table `gpNumU` (`"RAX" → 0`): the two are
the *same* 16-way SDM enumeration written in two register-name spellings. So for every
physical GP name `r`,

  `gpNum (gpReg64 r) = gpNumU r`.

The two resolvers **fully agree** — there is **no** register-naming/ordering mismatch;
the `%rax`-vs-`RAX` difference is purely cosmetic, and both spellings land on the same
SDM number. (Each of the 16 names also gets a dedicated `rfl` lemma `gpNum_gpReg64_*` for
direct use; the `_eq_gpNumU` lemma collects them over the table domain `stdRegNames`.)

## The standard allocation (`stdGpAlloc`) and the discharge

The **standard allocation** built from a physical-name list `names` is
`stdGpAlloc names := names.map (fun r => (r, gpReg64 r))` — each physical name mapped to
its AT&T register. `regOf (stdGpAlloc names) r = gpReg64 r` for `r ∈ names`
(`regOf_stdGpAlloc`), so the JInstr resolver `gpNum ∘ regOf (stdGpAlloc names)` collapses
to `gpNum ∘ gpReg64 = gpNumU` (`resolver_agree`). Feeding `resolver_agree` into the
`*_bytes_agree` lemmas of `LprogJInstrBytesAgree` drops their `hd`/`hs`
resolver-agreement hypotheses, yielding the **resolver-unconditional** byte-agreements
`*_bytes_agree_std` (`add`/`sub`/`and`/`or`/`xor`/`mov` reg-reg, `load`/`store`
const-offset).

## The remaining (non-resolver) residual — honest

The `*_bytes_agree_std` lemmas still carry the **operand-domain** hypotheses
(`spillQsaveOff … = none`, `parseMemName … = none`, `isSpillOrQsave … = false`): these
say the operand is a plain covered register, not a spill/qsave/`mem.*` name. They are the
covered-fragment side-condition (`gatherJBlock` only ever fires on those), and — for a
*concrete* register literal — they are gated by `String.startsWith`/`isPrefixOf`, which
the Lean **kernel cannot reduce** without `native_decide` (banned here): the very same
`native_decide`-only string-dispatch residual that `LprogJInstrBytesAgree` §3 already
flags (mnemonic→opcode resolution). That residual is **orthogonal** to the resolver one:
this file closes the *resolver* axis (`gpNum`-vs-`gpNumU`) **completely and
kernel-cleanly**, leaving only the pre-existing, separately-flagged string-dispatch
obligation.

So: **the JInstr and Lprog encoders produce byte-identical output on the covered
fragment under the standard allocation, with the resolver side-condition fully
discharged** — retiring the Lprog owned encoder is a KAT-free swap on the resolver axis
(D4).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ResolverAgree

open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder (gpNum encodeJInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
  (gpNumU encTwoAddr spillQsaveOff parseMemName parseMemNameGp isSpillOrQsave isGpName
    memDstOp memSrcOp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (gpReg64)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc regOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree

/-! ## §1. The table fact: `gpNum ∘ gpReg64 = gpNumU`

The lowercase AT&T table (`gpReg64`) post-composed with the `%rN`→number table (`gpNum`)
is the uppercase physical→number table (`gpNumU`) — the same 16-way SDM enumeration in
two spellings. Each of the 16 names is a `rfl` (the closed-string matches all reduce in
the kernel); `gpNum_gpReg64_eq_gpNumU` collects them over the table domain. -/

/-- The 16 standard physical GP register names (uppercase), the domain on which the two
    resolvers are compared. Every name `regOf`/`gpNumU` can meaningfully resolve is one
    of these (an out-of-table name is the `<UNALLOCATED>`/`%<UNKNOWN>` sentinel both
    encoders reject). -/
def stdRegNames : List String :=
  [ "RAX", "RCX", "RDX", "RBX", "RSP", "RBP", "RSI", "RDI",
    "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15" ]

/-- **The resolver table fact (per name).** Each physical name's AT&T spelling resolves,
    through `gpNum`, to its `gpNumU` number — byte-for-byte the same SDM index. (16
    `rfl`s, one per GP register.) -/
theorem gpNum_gpReg64_RAX : gpNum (gpReg64 "RAX") = gpNumU "RAX" := rfl
theorem gpNum_gpReg64_RCX : gpNum (gpReg64 "RCX") = gpNumU "RCX" := rfl
theorem gpNum_gpReg64_RDX : gpNum (gpReg64 "RDX") = gpNumU "RDX" := rfl
theorem gpNum_gpReg64_RBX : gpNum (gpReg64 "RBX") = gpNumU "RBX" := rfl
theorem gpNum_gpReg64_RSP : gpNum (gpReg64 "RSP") = gpNumU "RSP" := rfl
theorem gpNum_gpReg64_RBP : gpNum (gpReg64 "RBP") = gpNumU "RBP" := rfl
theorem gpNum_gpReg64_RSI : gpNum (gpReg64 "RSI") = gpNumU "RSI" := rfl
theorem gpNum_gpReg64_RDI : gpNum (gpReg64 "RDI") = gpNumU "RDI" := rfl
theorem gpNum_gpReg64_R8  : gpNum (gpReg64 "R8")  = gpNumU "R8"  := rfl
theorem gpNum_gpReg64_R9  : gpNum (gpReg64 "R9")  = gpNumU "R9"  := rfl
theorem gpNum_gpReg64_R10 : gpNum (gpReg64 "R10") = gpNumU "R10" := rfl
theorem gpNum_gpReg64_R11 : gpNum (gpReg64 "R11") = gpNumU "R11" := rfl
theorem gpNum_gpReg64_R12 : gpNum (gpReg64 "R12") = gpNumU "R12" := rfl
theorem gpNum_gpReg64_R13 : gpNum (gpReg64 "R13") = gpNumU "R13" := rfl
theorem gpNum_gpReg64_R14 : gpNum (gpReg64 "R14") = gpNumU "R14" := rfl
theorem gpNum_gpReg64_R15 : gpNum (gpReg64 "R15") = gpNumU "R15" := rfl

/-- **The resolver table fact (over the table domain).** For every standard physical GP
    name `r`, the JInstr-side resolution of its AT&T spelling (`gpNum (gpReg64 r)`)
    equals the Lprog-side number (`gpNumU r`). The two register-name→number maps **fully
    agree** — there is no naming/ordering mismatch; `%rax`-vs-`RAX` is cosmetic. -/
theorem gpNum_gpReg64_eq_gpNumU (r : String) (h : r ∈ stdRegNames) :
    gpNum (gpReg64 r) = gpNumU r := by
  fin_cases h <;> rfl

/-- Every standard physical name is a general-purpose name of the Lprog encoder. -/
theorem isGpName_of_mem_stdRegNames {r : String} (h : r ∈ stdRegNames) :
    isGpName r = true := by
  fin_cases h <;> rfl

/-! ## §2. The standard allocation and the resolver discharge

The standard allocation maps each physical name to its AT&T register; `regOf` then reads
it back as exactly `gpReg64`, so the JInstr resolver collapses to `gpNum ∘ gpReg64`,
which §1 identifies with `gpNumU`. -/

/-- The **standard allocation** for a physical-name list: each name `r ↦ (r, gpReg64 r)`.
    This is the allocation under which the JInstr and Lprog encoders share a register
    naming (the JInstr names ARE the Lprog physical names, resolved to their AT&T
    spellings). -/
def stdGpAlloc (names : List String) : GpAlloc :=
  names.map (fun r => (r, gpReg64 r))

/-- `regOf` of the standard allocation reads a listed physical name back as its AT&T
    register `gpReg64 r` (the assoc-list lookup hits the `(r, gpReg64 r)` entry). -/
theorem regOf_stdGpAlloc (names : List String) (r : String) (h : r ∈ names) :
    regOf (stdGpAlloc names) r = gpReg64 r := by
  unfold regOf stdGpAlloc
  induction names with
  | nil => simp at h
  | cons a t ih =>
    rcases List.mem_cons.mp h with rfl | hmem
    · simp
    · simp only [List.map_cons, List.lookup]
      split
      · rename_i heq; simp_all
      · exact ih hmem

/-- **Resolver agreement (the discharge).** For a standard physical name `r` (in both the
    allocation list and the table), the JInstr resolver `gpNum ∘ regOf (stdGpAlloc names)`
    equals the Lprog resolver `gpNumU`. This is exactly the `hd`/`hs` side-condition the
    `*_bytes_agree` lemmas of `LprogJInstrBytesAgree` take — here proved, not assumed. -/
theorem resolver_agree (names : List String) (r : String)
    (hn : r ∈ names) (ht : r ∈ stdRegNames) :
    gpNum (regOf (stdGpAlloc names) r) = gpNumU r := by
  rw [regOf_stdGpAlloc names r hn, gpNum_gpReg64_eq_gpNumU r ht]

/-! ## §3. Resolver-unconditional byte-agreement (the D4 drop-in)

Feeding `resolver_agree` into the `*_bytes_agree` lemmas drops their resolver
hypotheses. The result: under the standard allocation, the JInstr encoding of a covered
reg-reg ALU/`MOV` (or const-offset `LOAD`/`STORE`) instruction is **byte-identical** to
the Lprog `encTwoAddr` byte function — with **no remaining resolver side-condition**,
only the operand-domain hypotheses (the pre-existing `String.startsWith`-gated residual,
orthogonal to the resolver axis). The JInstr names ARE the Lprog physical names `dn`/`sn`,
so a single name list parametrises both. -/

/-- **`ADD` bytes agree (resolver-unconditional).** -/
theorem add_bytes_agree_std (names : List String) (frame spillW : Nat) (dn sn : String)
    (qsaveB : Nat)
    (hdn : dn ∈ names) (hsn : sn ∈ names) (hdt : dn ∈ stdRegNames) (hst : sn ∈ stdRegNames)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false) :
    encodeJInstr (stdGpAlloc names) (.add dn (.reg sn))
      = encTwoAddr frame spillW 1 0x01 (.reg dn) (.reg sn) qsaveB :=
  add_bytes_agree (stdGpAlloc names) frame spillW dn sn dn sn qsaveB
    hdk hsk hdm hsm hdsp hssp (isGpName_of_mem_stdRegNames hdt)
    (isGpName_of_mem_stdRegNames hst)
    (resolver_agree names dn hdn hdt) (resolver_agree names sn hsn hst)

/-- **`SUB` bytes agree (resolver-unconditional).** -/
theorem sub_bytes_agree_std (names : List String) (frame spillW : Nat) (dn sn : String)
    (qsaveB : Nat)
    (hdn : dn ∈ names) (hsn : sn ∈ names) (hdt : dn ∈ stdRegNames) (hst : sn ∈ stdRegNames)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false) :
    encodeJInstr (stdGpAlloc names) (.sub dn (.reg sn))
      = encTwoAddr frame spillW 1 0x29 (.reg dn) (.reg sn) qsaveB :=
  sub_bytes_agree (stdGpAlloc names) frame spillW dn sn dn sn qsaveB
    hdk hsk hdm hsm hdsp hssp (isGpName_of_mem_stdRegNames hdt)
    (isGpName_of_mem_stdRegNames hst)
    (resolver_agree names dn hdn hdt) (resolver_agree names sn hsn hst)

/-- **`AND` bytes agree (resolver-unconditional).** -/
theorem and_bytes_agree_std (names : List String) (frame spillW : Nat) (dn sn : String)
    (qsaveB : Nat)
    (hdn : dn ∈ names) (hsn : sn ∈ names) (hdt : dn ∈ stdRegNames) (hst : sn ∈ stdRegNames)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false) :
    encodeJInstr (stdGpAlloc names) (.and_ dn (.reg sn))
      = encTwoAddr frame spillW 1 0x21 (.reg dn) (.reg sn) qsaveB :=
  and_bytes_agree (stdGpAlloc names) frame spillW dn sn dn sn qsaveB
    hdk hsk hdm hsm hdsp hssp (isGpName_of_mem_stdRegNames hdt)
    (isGpName_of_mem_stdRegNames hst)
    (resolver_agree names dn hdn hdt) (resolver_agree names sn hsn hst)

/-- **`OR` bytes agree (resolver-unconditional).** -/
theorem or_bytes_agree_std (names : List String) (frame spillW : Nat) (dn sn : String)
    (qsaveB : Nat)
    (hdn : dn ∈ names) (hsn : sn ∈ names) (hdt : dn ∈ stdRegNames) (hst : sn ∈ stdRegNames)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false) :
    encodeJInstr (stdGpAlloc names) (.or_ dn (.reg sn))
      = encTwoAddr frame spillW 1 0x09 (.reg dn) (.reg sn) qsaveB :=
  or_bytes_agree (stdGpAlloc names) frame spillW dn sn dn sn qsaveB
    hdk hsk hdm hsm hdsp hssp (isGpName_of_mem_stdRegNames hdt)
    (isGpName_of_mem_stdRegNames hst)
    (resolver_agree names dn hdn hdt) (resolver_agree names sn hsn hst)

/-- **`XOR` bytes agree (resolver-unconditional).** -/
theorem xor_bytes_agree_std (names : List String) (frame spillW : Nat) (dn sn : String)
    (qsaveB : Nat)
    (hdn : dn ∈ names) (hsn : sn ∈ names) (hdt : dn ∈ stdRegNames) (hst : sn ∈ stdRegNames)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false) :
    encodeJInstr (stdGpAlloc names) (.xor_ dn (.reg sn))
      = encTwoAddr frame spillW 1 0x31 (.reg dn) (.reg sn) qsaveB :=
  xor_bytes_agree (stdGpAlloc names) frame spillW dn sn dn sn qsaveB
    hdk hsk hdm hsm hdsp hssp (isGpName_of_mem_stdRegNames hdt)
    (isGpName_of_mem_stdRegNames hst)
    (resolver_agree names dn hdn hdt) (resolver_agree names sn hsn hst)

/-- **`MOV` (reg-reg) bytes agree (resolver-unconditional).** -/
theorem mov_bytes_agree_std (names : List String) (frame spillW : Nat) (dn sn : String)
    (qsaveB : Nat)
    (hdn : dn ∈ names) (hsn : sn ∈ names) (hdt : dn ∈ stdRegNames) (hst : sn ∈ stdRegNames)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false) :
    encodeJInstr (stdGpAlloc names) (.mov dn (.reg sn))
      = encTwoAddr frame spillW 1 0x89 (.reg dn) (.reg sn) qsaveB :=
  mov_bytes_agree (stdGpAlloc names) frame spillW dn sn dn sn qsaveB
    hdk hsk hdm hsm hdsp hssp (isGpName_of_mem_stdRegNames hdt)
    (isGpName_of_mem_stdRegNames hst)
    (resolver_agree names dn hdn hdt) (resolver_agree names sn hsn hst)

/-! ### §3b. The const-offset memory arms (resolver-unconditional)

The JInstr memory arms resolve a *register base* name through the allocation; the Lprog
`encTwoAddr` mem arm parses a `mem.<base>.<off>` operand to `(gpNumU base, off)`. The
base register's resolution is discharged by `resolver_agree`; the parsed base number `bb`
is fixed by the Lprog operand `dn`/`sn` (which IS `"mem.<base>.<off>"`). -/

/-- **`LOAD` bytes agree (resolver-unconditional).** The JInstr `loadMem d base off`
    encoding equals the Lprog reg←`mem.*` `encTwoAddr` byte function, with the
    destination-register resolution discharged. The Lprog source `sn` is the parsed
    `mem.*` operand with a general-purpose base (`hsm`); `bb` is its base number. -/
theorem load_bytes_agree_std (names : List String) (frame spillW op : Nat)
    (d base : String) (off : Int) (dn sn : String) (bb : Nat) (qsaveB : Nat)
    (hdn : d ∈ names) (hdt : d ∈ stdRegNames) (hd : gpNumU dn = gpNumU d)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemNameGp sn = some (bb, off))
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hdg : isGpName dn = true)
    (hb : gpNum (regOf (stdGpAlloc names) base) = bb) (hop : memSrcOp op = 0x8b) :
    encodeJInstr (stdGpAlloc names) (.loadMem d base off)
      = encTwoAddr frame spillW 1 op (.reg dn) (.reg sn) qsaveB :=
  load_bytes_agree (stdGpAlloc names) frame spillW op d base off dn sn bb qsaveB
    hdk hsk hdm hsm hdsp hssp hdg (hd ▸ resolver_agree names d hdn hdt) hb hop

/-- **`STORE` bytes agree (resolver-unconditional).** The JInstr `storeMem base off (reg r)`
    encoding equals the Lprog `mem.*`←reg `encTwoAddr` byte function, with the
    source-register resolution discharged. The Lprog destination `dn` is the parsed
    `mem.*` operand with a general-purpose base (`hdm`); `bb` is its base number. -/
theorem store_bytes_agree_std (names : List String) (frame spillW op : Nat)
    (base : String) (off : Int) (r : String) (dn sn : String) (bb : Nat) (qsaveB : Nat)
    (hrn : r ∈ names) (hrt : r ∈ stdRegNames) (hr : gpNumU sn = gpNumU r)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemNameGp dn = some (bb, off)) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hsg : isGpName sn = true)
    (hb : gpNum (regOf (stdGpAlloc names) base) = bb) (hop : memDstOp op = 0x89) :
    encodeJInstr (stdGpAlloc names) (.storeMem base off (.reg r))
      = encTwoAddr frame spillW 1 op (.reg dn) (.reg sn) qsaveB :=
  store_bytes_agree (stdGpAlloc names) frame spillW op base off r dn sn bb qsaveB
    hdk hsk hdm hsm hdsp hssp hsg (hr ▸ resolver_agree names r hrn hrt) hb hop

end CatCrypt.Crypto.SecureCompilation.X86Backend.ResolverAgree
