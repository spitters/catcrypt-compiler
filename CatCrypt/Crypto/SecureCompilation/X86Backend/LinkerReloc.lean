/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

/-!
# Linker soundness: the cross-object `call` displacement lands on its callee

The owned x86 backend stitches emitted leaf functions into a whole protocol object
through `LprogBytes.encodeLprogReloc` (the cross-function-call linker path). A
`call <sym>` between two functions in the same `Lprog` is resolved *at encode time*
to a PC-relative `rel32` displacement; a truly-external call becomes an
`R_X86_64_PLT32` `.rela.text` relocation the linker patches. This file proves the
**soundness of the intra-object resolution**: the displacement the encoder writes
into the `call` instruction's `rel32` field, interpreted with x86 PC-relative
semantics (`next-instruction-address + disp`), lands **exactly on the callee's
`.text` address**.

## What is proved (property #2 — relocation/displacement correctness)

The x86 `call rel32` (`E8 cd`) transfers control to `RIP_after_call + disp`, where
`RIP_after_call` is the address of the byte *following* the 5-byte instruction.
`encodeLcmdReloc` resolves an intra-object call to
`disp = symBase f - instrEnd`, where (per `encodeLprogReloc`'s `symBase` wiring)
`symBase f = calleeBase − bodyStart` is the callee's `.text` base relative to the
**start of the calling body's bytes**, and `instrEnd` is the call site's end
**relative to that same body start**. Writing `bodyStart` for the calling body's
absolute `.text` offset:

* `callSiteEndAbs = bodyStart + instrEnd`   (the absolute address after the call)
* `calleeBaseAbs  = bodyStart + symBase f`  (the callee's absolute `.text` address)

so the landed address is

```
callSiteEndAbs + disp
  = (bodyStart + instrEnd) + (symBase f − instrEnd)
  = bodyStart + symBase f
  = calleeBaseAbs.
```

The two facts this rests on, both already in `LprogBytes`:

1. **Encoding/decoding correctness of the `rel32` field** — `roundtrip_call32`:
   `decodeCall32 (encCall32 d) = some {opcode := 0xe8, disp := d}` for any in-range
   signed-32 displacement. So the bytes the encoder lays down really do carry the
   displacement the resolver computed (no off-by-one / endianness slip).
2. **The PC-relative algebra above** — `landed_eq_calleeBase`.

Composed: `linkedCall_lands_on_callee` says the displacement *recovered by decoding
the emitted call bytes*, applied PC-relative from the call site's absolute end,
equals the callee's absolute `.text` address — i.e. the linked call goes to the
right function.

A concrete 2-function `caller`/`callee` image (`demoProg`) is run end-to-end
through the real `encodeLprogReloc` pipeline (`native_decide` over the actual
emitted bytes) to witness that the abstract hypotheses hold on a real object the
backend produces: the call is intra-object (no relocation emitted), its decoded
displacement is `−23`, and `callSiteEndAbs + (−23) = 0 = calleeBase`.

## Scope (relative to a full verified linker)

This is a statement about the **relocation-patching / displacement-encoding**
layer, NOT a full operational call semantics:

* **No executed-call semantics.** There is no machine model in which `call` pushes
  a return address and jumps; the property is "the displacement field targets the
  callee's byte address", which is the relocation correctness, not "running the
  linked image computes `callee ∘ caller`". The property "linked run =
  composition" is out of scope — the owned backend has a decode round-trip for the
  control-flow bytes but no operational step relation for `call`/`ret` (the `ret`
  byte and the `push`/`pop` ABI scaffold are gas-pinned, per `LprogBytes` §"trust
  tally"). That property needs such an operational model.
* **Single object, intra-object only.** The proof covers a call to a function in
  the *same* `Lprog` (resolved directly). The truly-external / multi-object case
  (the `R_X86_64_PLT32` `.rela.text` relocation against an UNDEF symbol) is
  *structurally* well-formed here (`demoExternProg` witnesses one reloc, named for
  the right symbol, at the right `.text` offset) but its final displacement is the
  *linker's* to patch — we do not model `ld`'s GOT/PLT resolution or address-space
  layout.
* **`rel32` range side condition.** PC-relative `call` is limited to ±2GiB; the
  theorem carries `-2^31 ≤ disp < 2^31` as a hypothesis (always met for the small
  single-object images the backend emits, and discharged by `decide` in the demo).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LinkerReloc

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

/-! ## 1. The resolved intra-object displacement and its PC-relative target -/

/-- The signed `rel32` displacement `encodeLcmdReloc` writes for an **intra-object**
    `call`/`jmp` whose target symbol resolves (via `symBase`) to `delta` (the
    callee's `.text` base, relative to the start of THIS body's bytes), at a call
    site whose end offset within the body is `instrEnd`. This is the exact
    expression in `encodeLcmdReloc`'s `some delta` arm (`delta − Int.ofNat instrEnd`),
    isolated so the soundness statement is about *this number*. -/
def resolvedDisp (delta : Int) (instrEnd : Nat) : Int := delta - Int.ofNat instrEnd

/-- The absolute `.text` address `call rel32` transfers to: the address after the
    5-byte instruction (`callSiteEndAbs`) plus the encoded displacement. This is the
    x86 PC-relative semantics for `E8 cd`. -/
def landedAddr (callSiteEndAbs : Int) (disp : Int) : Int := callSiteEndAbs + disp

/-- **PC-relative algebra — the displacement lands on the callee.** With the
    `encodeLprogReloc` wiring `delta = calleeBase − bodyStart` (the `symBase`
    resolver) and the call site sitting at body-relative end `instrEnd` so its
    absolute end is `bodyStart + instrEnd`, the landed address of the resolved
    displacement is exactly the callee's absolute `.text` base. This is the core
    of linker soundness: the cross-function call goes to the right function. -/
theorem landed_eq_calleeBase (bodyStart calleeBase : Int) (instrEnd : Nat) :
    landedAddr (bodyStart + Int.ofNat instrEnd)
      (resolvedDisp (calleeBase - bodyStart) instrEnd) = calleeBase := by
  simp only [landedAddr, resolvedDisp]; ring

/-! ## 2. The emitted bytes carry the resolved displacement

`encodeLcmdReloc` writes the intra-object call via `encodeRemoteCF d i`, which for a
`Lcall` is `encCall32 d`. Decoding those 5 bytes recovers `d` exactly (the field is
the only thing a wrong jump would get wrong). -/

/-- Decoding the `call` bytes the reloc encoder emits for a resolved intra-object
    displacement recovers that displacement exactly. A direct corollary of
    `roundtrip_call32` specialised to the `encodeRemoteCF`/`Lcall` arm. -/
theorem decode_encodeRemoteCF_call (d : Int) (ra : Option String) (t : String × LLabel)
    (hlo : -(2^31) ≤ d) (hhi : d < 2^31) :
    decodeCall32 (encodeRemoteCF d (.Lcall ra t)) = some { opcode := 0xe8, disp := d } := by
  simp only [encodeRemoteCF]
  exact roundtrip_call32 d hlo hhi

/-! ## 3. The main theorem: the linked call's *decoded* displacement lands on the callee -/

/-- **Linker soundness (intra-object `call`).** The displacement *recovered by
    decoding the emitted `call` bytes*, applied with x86 PC-relative semantics from
    the call site's absolute end address, lands exactly on the callee's absolute
    `.text` base. This ties the encoded bytes (clause 2) to the address arithmetic
    (clause 1): a `call <callee>` resolved intra-object by `encodeLcmdReloc` /
    `encodeLprogReloc` transfers control to the callee.

    `bodyStart` is the calling function's `.text` base (`myBase + prologueLen`),
    `calleeBase` is the callee's `.text` base (`symValue` in the stitched object),
    and `instrEnd` is the call-site instruction's end offset within the calling
    body. The single side condition is the `rel32` range (`±2GiB`), met for every
    single-object image the backend emits. -/
theorem linkedCall_lands_on_callee
    (bodyStart calleeBase : Int) (instrEnd : Nat)
    (ra : Option String) (t : String × LLabel)
    (hlo : -(2^31) ≤ resolvedDisp (calleeBase - bodyStart) instrEnd)
    (hhi : resolvedDisp (calleeBase - bodyStart) instrEnd < 2^31) :
    -- decoding the emitted call bytes recovers the resolver's displacement …
    (decodeCall32 (encodeRemoteCF (resolvedDisp (calleeBase - bodyStart) instrEnd)
        (.Lcall ra t))).map (fun dc => landedAddr (bodyStart + Int.ofNat instrEnd) dc.disp)
      -- … and applying it PC-relative lands on the callee.
      = some calleeBase := by
  rw [decode_encodeRemoteCF_call _ ra t hlo hhi]
  simp only [Option.map_some]
  rw [landed_eq_calleeBase]

/-! ## 4. A concrete 2-function `caller`/`callee` image through the real pipeline

`demoProg` has `callee` (a trivial `MOV`) at `.text` base 0 and `caller` (a single
`call callee`) at `.text` base 13. Everything below is run through the ACTUAL
`encodeLprogReloc` / `funcBases` / `encodeLcmdReloc` pipeline the backend emits with
(`native_decide` over the real bytes), so the abstract hypotheses above are
witnessed on an object the backend really produces. -/

/-- `callee`: a trivial leaf (no spills, no calls). `.text` base 0 in `demoProg`. -/
def calleeBody : Lcmd := [⟨0, .Lopn [.reg "RAX"] "MOV" [.reg "RDI"]⟩]

/-- `caller`: a single intra-object `call callee`. `.text` base 13 in `demoProg`. -/
def callerBody : Lcmd := [⟨0, .Lcall none ("callee", 0)⟩]

/-- The 2-function image: `callee` then `caller`, both exported leaves. -/
def demoProg : Lprog :=
  { lp_funcs := [("callee", { lfd_body := calleeBody }),
                 ("caller", { lfd_body := callerBody })] }

/-- `callee` lands at `.text` base 0, `caller` at base 13 (5-byte prologue +
    3-byte `MOV` + 5-byte epilogue/ret = 13 for `callee`). -/
theorem demo_funcBases : funcBases demoProg = [("callee", 0), ("caller", 13)] := by
  native_decide

/-- The `call callee` is **intra-object** — no `.rela.text` relocation is emitted
    (the callee is in the object, resolved directly). -/
theorem demo_no_externs : externSyms demoProg = [] := by native_decide

/-- The `caller`'s `.text` base (`myBase + prologueLen`): `13 + 5 = 18`. -/
def demoCallerBodyStart : Int := 18

/-- The `callee`'s `.text` base. -/
def demoCalleeBase : Int := 0

/-- The call site's body-relative end offset (the single 5-byte call at body
    offset 0 ends at 5). -/
def demoInstrEnd : Nat := 5

/-- The `symBase` resolver `encodeLprogReloc` uses for `caller`: `callee`'s base
    minus `caller`'s `.text` base minus its prologue length =
    `0 − 13 − 5 = −18 = demoCalleeBase − demoCallerBodyStart`. -/
theorem demo_symBase :
    (Int.ofNat 0 - Int.ofNat 13 - Int.ofNat 5) = demoCalleeBase - demoCallerBodyStart := by
  decide

/-- The body bytes `encodeLcmdReloc` emits for `caller` under the real resolver: a
    single 5-byte `E8` call with the resolved displacement, **and no relocation**
    (intra-object). The 5 call bytes are `E8 E9FFFFFF` = `call rel32 = −23`. -/
theorem demo_encodeLcmdReloc :
    encodeLcmdReloc
        (fun f => if f = "callee" then some (demoCalleeBase - demoCallerBodyStart) else none)
        callerBody
      = ([0xe8, 0xe9, 0xff, 0xff, 0xff].map (BitVec.ofNat 8), []) := by
  native_decide

/-- Decoding the emitted `caller` call bytes recovers displacement `−23`, and
    applying it PC-relative from the call site's absolute end (`18 + 5 = 23`) lands
    on `0` = `callee`'s `.text` base. The concrete instance of
    `linkedCall_lands_on_callee` on the real emitted bytes. -/
theorem demo_call_lands_on_callee :
    (decodeCall32
        (encodeLcmdReloc
          (fun f => if f = "callee" then some (demoCalleeBase - demoCallerBodyStart) else none)
          callerBody).1).map (fun dc => landedAddr (demoCallerBodyStart + Int.ofNat demoInstrEnd) dc.disp)
      = some demoCalleeBase := by
  native_decide

/-- Abstract↔concrete tie: the general theorem `linkedCall_lands_on_callee`,
    instantiated at the demo's addresses, agrees with the byte-level demo — both
    say the linked `caller→callee` call lands on `callee`. -/
theorem demo_matches_general :
    (decodeCall32 (encodeRemoteCF
        (resolvedDisp (demoCalleeBase - demoCallerBodyStart) demoInstrEnd)
        (.Lcall none ("callee", 0)))).map
        (fun dc => landedAddr (demoCallerBodyStart + Int.ofNat demoInstrEnd) dc.disp)
      = some demoCalleeBase :=
  linkedCall_lands_on_callee demoCallerBodyStart demoCalleeBase demoInstrEnd none ("callee", 0)
    (by decide) (by decide)

/-! ## 5. External-call structural well-formedness (the relocation path)

When the callee is NOT in the object, `encodeLprogReloc` emits a `0`-placeholder
`rel32` and an `R_X86_64_PLT32` `.rela.text` relocation against an UNDEF symbol
named for the callee — the displacement is then the *linker's* to patch. We do not
model `ld`, but we witness that the relocation table the backend emits is
well-formed: one reloc, naming the right symbol, at the right rel32-field offset. -/

/-- `caller_ext` calls an external `libc_helper` (not in the object). -/
def callerExtBody : Lcmd := [⟨0, .Lcall none ("libc_helper", 0)⟩]

/-- A 1-function image whose only call is external. -/
def demoExternProg : Lprog :=
  { lp_funcs := [("caller_ext", { lfd_body := callerExtBody })] }

/-- The external symbol is collected (it is undefined in the object, so it becomes
    a `.rela.text` relocation target). -/
theorem demoExtern_externSyms : externSyms demoExternProg = ["libc_helper"] := by
  native_decide

/-- The reloc encoder emits exactly one relocation for the external call, naming
    `libc_helper`, at body offset `1` (the rel32 field, right after the `E8`
    opcode), with a `0`-placeholder displacement for the linker to patch. -/
theorem demoExtern_encodeLcmdReloc :
    encodeLcmdReloc (fun _ => none) callerExtBody
      = ([0xe8, 0x00, 0x00, 0x00, 0x00].map (BitVec.ofNat 8), [(1, "libc_helper")]) := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.LinkerReloc
