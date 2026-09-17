import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Framed

/-!
The imported s2n-bignum block inside the red-zone leaf frame, `s2nMontmulP384FramedBlock`,
encoded to x86-64 machine code by the owned scalar encoder `ScalarEncoder.encodeJBlock`
under the identity allocation `S2nMontmulP384.s2nAlloc`, and written as `.byte` directives.

The bytes are `encodeJBlock s2nAlloc s2nMontmulP384FramedBlock`, the byte string that
`Ascent.Demos.S2nMontmulP384.s2nMontmulP384FramedBytes_correct` is stated over: they decode
to 276 instructions that compute the Montgomery product modulo `p384` under `JasminModel`
and end with `%rsp`, `%rbx`, `%rbp`, `%r12`, `%r13`, `%r14`, `%r15` at their entry values.
The frame is part of those bytes: six `movq %r, -8·(k+1)(%rsp)` stores before the body and
six loads after it, with no `pushq`, `popq` or `%rsp` adjustment.

MEASUREMENT ARTIFACT for the entry marker and the return only. The literal lines are the
section and symbol directives, `endbr64` before the bytes, `retq` after them, and the
`.note.GNU-stack` section; no theorem describes `endbr64` or `retq`. The file is written for
the known-answer and timing harness next to `bignum_montmul_p384_encoded.s`.

The `#eval main` at the end writes `bench/s2n_import/gen/bignum_montmul_p384_framed.s`
when `lake lean` elaborates this file from the repository root. It fails, writing nothing,
if the encoder's gate `encodableJBlock` rejects the allocation.
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384

/-- The emitted symbol. -/
def framedSymbol : String := "bignum_montmul_p384_framed"

/-- A byte as `0xNN`. -/
def hexByte (b : BitVec 8) : String :=
  let d := Nat.toDigits 16 b.toNat
  "0x" ++ String.ofList (if d.length < 2 then '0' :: d else d)

/-- The byte string as `.byte` directives, sixteen bytes per line. -/
def byteLines : List (BitVec 8) → List String
  | [] => []
  | b :: bs =>
      ("\t.byte " ++ ", ".intercalate (((b :: bs).take 16).map hexByte))
        :: byteLines ((b :: bs).drop 16)
termination_by bs => bs.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- The encoded framed block. -/
def framedBytes : List (BitVec 8) := encodeJBlock s2nAlloc s2nMontmulP384FramedBlock

/-- The assembly text: `endbr64`, the encoded framed block, `retq`. -/
def framedAsm : String :=
  "\n".intercalate
    ([ "# bignum_montmul_p384_framed: encodeJBlock s2nAlloc s2nMontmulP384FramedBlock, "
          ++ toString framedBytes.length ++ " bytes, the subject of "
          ++ "S2nMontmulP384.s2nMontmulP384FramedBytes_correct.",
       "# The lines endbr64 and retq and the directives are literal text.",
       "\t.text",
       "\t.globl " ++ framedSymbol,
       "\t.type " ++ framedSymbol ++ ", @function",
       framedSymbol ++ ":",
       "\tendbr64" ]
    ++ byteLines framedBytes
    ++ [ "\tretq",
         "\t.section .note.GNU-stack,\"\",@progbits" ])
  ++ "\n"

def main : IO Unit := do
  unless encodableJBlock s2nAlloc s2nMontmulP384FramedBlock do
    throw <| IO.userError
      "encodableJBlock rejects s2nAlloc on s2nMontmulP384FramedBlock"
  let path := "bench/s2n_import/gen/bignum_montmul_p384_framed.s"
  IO.FS.createDirAll "bench/s2n_import/gen"
  IO.FS.writeFile path framedAsm
  IO.println s!"wrote {path} ({framedBytes.length} bytes)"

#eval main
