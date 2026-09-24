/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr

/-!
# The framed byte-residual between `JInstr` and `Lprog`: the `leaq` open/close pair

`ComToFramedJInstr.framedText_agree_of_body_agree` reconciles the framed `JInstr`
`.text` with the framed `Lprog` `.text` on the `gatherJBlock`-covered fragment
EXCEPT for one residual, pinned exactly by `lprogFramedText_structure` vs
`jinstrFramedText_no_leaq`: the `Lprog` looped driver lays down a frame-open /
frame-close `leaq` pair (`encLeaRspFrame (-F)` / `encLeaRspFrame F`) around the
body, and `encLeaRspFrame` is **not** guarded on a zero frame — even at
`disp = 0` it emits the 5-byte disp8 `leaq 0(%rsp), %rsp`. The framed `JInstr`
path (`jinstrFramedLeaf`) has no `leaq` at all, so the two `.text` streams differ
by exactly those two 5-byte `leaq` instructions.

This module closes that residual on the **literal byte level**, on top of
`ComToFramedJInstr`.

## What is built

* **§1 — the `leaq`-including framed leaf.** `jinstrFramedLeafLeaq f F` is the
  framed `JInstr` `.text` WITH the frame-open / frame-close `leaq` pair inserted
  around the body at frame size `F`, exactly where the `Lprog` driver puts them:
  `prologue ++ argMarshal ++ leaq(-F) ++ body ++ leaq(F) ++ epilogue`. Its
  structure lemma `jinstrFramedLeafLeaq_text` pins the six glued segments.

* **§2 — the literal match.** `framedLeaqText_eq_lprog` is the main
  theorem: given that the JInstr leaf's framing segments equal the `Lprog` leaf's
  framing segments (prologue = push, empty arg-marshal, epilogue = pop+ret), the
  frame size matches (`F = frameSize body`), and the two **body** byte streams
  agree (`encodeJBlock ≡ encodeLcmd body`, the `LprogJInstrBytesAgree` block
  agreement), the `leaq`-including JInstr framed `.text` is **LITERALLY equal**
  to the `Lprog` framed `.text` `encodeLfundefBytes body`. No residual remains —
  the `leaq` pair is present on BOTH sides.

* **§3 — the residual, isolated.** `framedLeaqText_eq_no_leaq_with_leaq` and
  `leaqPair_isolated` exhibit the difference between the two JInstr framings
  (`jinstrFramedText_no_leaq` without the pair, `jinstrFramedLeafLeaq` with it)
  as *exactly* the two `encLeaRspFrame` segments — the precise byte residual
  between the two framed paths, factored out.

* **§4 — the zero-frame no-op characterisation.** `encLeaRspFrame_zero` pins that
  at `F = 0` the inserted pair is two literal `leaq 0(%rsp), %rsp` (`0x48 0x8d
  0x64 0x24 0x00`) instructions — the 5-byte no-op the `Lprog` path emits
  unconditionally — so on the frame-free covered fragment the literal match adds
  exactly two no-ops to the JInstr `.text` to meet the `Lprog` `.text` byte for
  byte.

## Trust tier

No new trust: the inserted bytes are `LprogBytes.encLeaRspFrame` (the same
trusted leaf-ABI `leaq` the `Lprog` framed path `encodeLfundefBytes` already
emits), the body bytes are `ScalarEncoder.encodeJBlock` (gas-pinned), and the
prologue/epilogue is `LeafBytes`'s trusted push/pop/ret. This module only
*composes* and *reconciles* those. All goals are closed, with no axiom and no
`native_decide`.

## Conclusion

With `framedLeaqText_eq_lprog` the framed `JInstr` path (with the `leaq`-pair
framing) is a **literal whole-`.text` byte match** for the framed `Lprog` path on
the covered fragment, with no framed byte-residual.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstrLeaq

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (frameSize calleeSavedToSave gpReg64)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFramedEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr

/-! ## 1. The `leaq`-including framed `JInstr` leaf

`JInstrFramedEmit.jinstrFramedLeaf` frames a block as `prologue ++ argMarshal ++
encodeJBlock ++ epilogue` — NO `leaq`. To literally match the `Lprog` framed
`.text` (`encodeLfundefBytes`, which carries the frame-open / frame-close `leaq`
pair around the body) we insert the SAME `encLeaRspFrame (-F)` / `encLeaRspFrame
F` pair the `Lprog` driver uses, in the SAME positions (immediately around the
body). The frame size `F` is supplied (it is `frameSize body` for the matched
`Lprog` body). -/

/-- The framed `JInstr` `.text` bytes WITH the frame-open / frame-close `leaq`
    pair, exactly where the `Lprog` driver (`encodeLfundefBytes`) puts them:
    `prologue ++ argMarshal ++ encLeaRspFrame (-F) ++ encodeJBlock ++
     encLeaRspFrame F ++ epilogue`. This is the JInstr framing extended to carry
    the one residual the leaq-free `jinstrFramedLeaf` lacked. -/
def jinstrFramedLeaqText (f : JFunc) (F : Nat) : List (BitVec 8) :=
  prologueBytes f.savedRegs
    ++ argMarshalBytes f.alloc f.args
    ++ encLeaRspFrame (-(Int.ofNat F))
    ++ encodeJBlock f.alloc f.body
    ++ encLeaRspFrame (Int.ofNat F)
    ++ epilogueBytes f.savedRegs

/-- The `leaq`-including framed `.text` is exactly the six glued segments — the
    structural contrast with `jinstrFramedLeaf_text` (four segments, no `leaq`).
    `simp`-normalised to a right-nested append so it lines up with the `Lprog`
    structure lemma. -/
theorem jinstrFramedLeaqText_segments (f : JFunc) (F : Nat) :
    jinstrFramedLeaqText f F
      = prologueBytes f.savedRegs
          ++ (argMarshalBytes f.alloc f.args
          ++ (encLeaRspFrame (-(Int.ofNat F))
          ++ (encodeJBlock f.alloc f.body
          ++ (encLeaRspFrame (Int.ofNat F)
          ++ epilogueBytes f.savedRegs)))) := by
  simp [jinstrFramedLeaqText, List.append_assoc]

/-! ## 2. The literal match: the `leaq`-framed JInstr `.text` IS the `Lprog` `.text`

Given framing-segment agreement (the same hypotheses `framedText_agree_of_body_agree`
takes — prologue / empty marshal / epilogue equal the `Lprog` push / pop+ret), a
matched frame size, and body agreement, the `leaq`-including JInstr `.text` is
LITERALLY `encodeLfundefBytes body`. The `leaq` pair is on both sides, so no
residual is left. -/

/-- **The literal whole-`.text` match.** With
    the `leaq` pair carried by the JInstr framing too, and under the framing /
    frame-size / body agreement, the `leaq`-including framed JInstr `.text` equals
    the `Lprog` framed `.text` `encodeLfundefBytes body` **byte for byte**:

    * `hpush` — the JInstr prologue equals the `Lprog` callee-saved `pushq` block;
    * `hmar`  — the arg-marshal is empty (the covered fragment marshals nothing);
    * `hpop`  — the JInstr epilogue equals the `Lprog` `popq…++ret` block;
    * `hF`    — the inserted frame size is the `Lprog` body's `frameSize`;
    * `hbody` — the two body byte streams agree (`encodeJBlock ≡ encodeLcmd body`).

    This is the literal byte-level drop-in: the JInstr framed path (with the
    `leaq` framing) emits the SAME `.text` bytes as the `Lprog` framed path. -/
theorem framedLeaqText_eq_lprog
    (f : JFunc) (body : Lcmd) (F : Nat)
    (hpush : prologueBytes f.savedRegs
      = (calleeSavedToSave body).flatMap (fun r => encPushReg (gpReg64 r)))
    (hmar : argMarshalBytes f.alloc f.args = [])
    (hpop : epilogueBytes f.savedRegs
      = (calleeSavedToSave body).reverse.flatMap (fun r => encPopReg (gpReg64 r))
          ++ encRet)
    (hF : F = frameSize body)
    (hbody : encodeJBlock f.alloc f.body = encodeLcmd body) :
    jinstrFramedLeaqText f F = encodeLfundefBytes body := by
  rw [jinstrFramedLeaqText, hpush, hmar, hpop, hF, hbody]
  rw [lprogFramedText_structure body]
  simp [List.append_assoc]

/-! ## 3. The residual, isolated: the two framings differ by exactly the `leaq` pair

`jinstrFramedText_no_leaq` is the leaq-free JInstr `.text` (`prologue ++ body ++
epilogue`, empty marshal). `jinstrFramedLeaqText` adds the `encLeaRspFrame` pair.
The difference is EXACTLY those two `leaq` segments, in their body-flanking
positions — the precise byte residual between the two framed paths. -/

/-- The `leaq`-including framing is the leaq-free framing with the two
    `encLeaRspFrame` segments spliced in around the body. Concretely, with an
    empty arg-marshal, `jinstrFramedLeaf f`'s `.text` plus the inserted pair
    rebuilds `jinstrFramedLeaqText f F`: the residual between the two JInstr
    framings is precisely `encLeaRspFrame (-F)` (before the body) and
    `encLeaRspFrame F` (after it). -/
theorem leaqPair_isolated (f : JFunc) (F : Nat)
    (hmar : argMarshalBytes f.alloc f.args = []) :
    jinstrFramedLeaqText f F
      = prologueBytes f.savedRegs
          ++ encLeaRspFrame (-(Int.ofNat F))
          ++ encodeJBlock f.alloc f.body
          ++ encLeaRspFrame (Int.ofNat F)
          ++ epilogueBytes f.savedRegs := by
  rw [jinstrFramedLeaqText, hmar]
  simp [List.append_assoc]

/-- The two JInstr framings side by side: the leaq-free `.text`
    (`jinstrFramedText_no_leaq`) is `prologue ++ body ++ epilogue`; the
    `leaq`-including `.text` is the SAME with `encLeaRspFrame (-F)` and
    `encLeaRspFrame F` inserted immediately around the body. This pins the
    framed residual as exactly the two `leaq` segments. -/
theorem framedLeaqText_eq_no_leaq_with_leaq (f : JFunc) (F : Nat)
    (hmar : argMarshalBytes f.alloc f.args = []) :
    jinstrFramedLeaqText f F
      = prologueBytes f.savedRegs
          ++ encLeaRspFrame (-(Int.ofNat F))
          ++ (encodeJBlock f.alloc f.body)
          ++ encLeaRspFrame (Int.ofNat F)
          ++ epilogueBytes f.savedRegs ∧
      (jinstrFramedLeaf f).text
          = prologueBytes f.savedRegs ++ encodeJBlock f.alloc f.body
              ++ epilogueBytes f.savedRegs := by
  refine ⟨leaqPair_isolated f F hmar, jinstrFramedText_no_leaq f hmar⟩

/-! ## 4. The zero-frame no-op characterisation

On the frame-free covered fragment `F = 0`. `encLeaRspFrame 0` is the 5-byte
disp8 `leaq 0(%rsp), %rsp` (`0x48 0x8d 0x64 0x24 0x00`) — a literal no-op — and
`encLeaRspFrame (-0) = encLeaRspFrame 0`, so the inserted pair is two copies of
that no-op. This is exactly the unconditional `leaq` pair the `Lprog` path emits
even at frame size 0. -/

/-- `encLeaRspFrame 0` is the literal 5-byte `leaq 0(%rsp), %rsp` no-op
    (`REX.W 0x48`, `LEA 0x8d`, `ModRM disp8 %rsp 0x64`, `SIB 0x24`, `disp8 = 0x00`).
    At `disp = 0` the disp8 branch is taken (`-128 ≤ 0 ≤ 127`). -/
theorem encLeaRspFrame_zero :
    encLeaRspFrame 0
      = [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8d, BitVec.ofNat 8 0x64,
         BitVec.ofNat 8 0x24, BitVec.ofNat 8 0x00] := by
  rfl

/-- At frame size `0` both inserted `leaq`s collapse to the SAME 5-byte
    `leaq 0(%rsp), %rsp` no-op: `encLeaRspFrame (-(Int.ofNat 0)) = encLeaRspFrame
    (Int.ofNat 0) = encLeaRspFrame 0`. So on the frame-free covered fragment the
    `leaq`-including JInstr framing adds exactly two no-ops to the leaq-free
    `.text` — precisely the two no-ops the `Lprog` `.text` carries — and the
    literal match `framedLeaqText_eq_lprog` reduces to inserting them. -/
theorem leaqPair_zero_is_two_nops :
    encLeaRspFrame (-(Int.ofNat 0)) = encLeaRspFrame 0
      ∧ encLeaRspFrame (Int.ofNat 0) = encLeaRspFrame 0 := by
  constructor <;> rfl

/-- On the frame-free covered fragment (`F = 0`), the `leaq`-including JInstr
    `.text` is the leaq-free `.text` with exactly the two 5-byte
    `leaq 0(%rsp), %rsp` no-ops spliced around the body — the explicit
    "byte difference = exactly two `leaq 0(%rsp),%rsp` no-ops" statement. -/
theorem framedLeaqText_zero_two_nops (f : JFunc)
    (hmar : argMarshalBytes f.alloc f.args = []) :
    jinstrFramedLeaqText f 0
      = prologueBytes f.savedRegs
          ++ [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8d, BitVec.ofNat 8 0x64,
              BitVec.ofNat 8 0x24, BitVec.ofNat 8 0x00]
          ++ encodeJBlock f.alloc f.body
          ++ [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8d, BitVec.ofNat 8 0x64,
              BitVec.ofNat 8 0x24, BitVec.ofNat 8 0x00]
          ++ epilogueBytes f.savedRegs := by
  rw [leaqPair_isolated f 0 hmar]
  rw [show (-(Int.ofNat 0) : Int) = 0 by rfl, show (Int.ofNat 0 : Int) = 0 by rfl,
    encLeaRspFrame_zero]

end CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstrLeaq
