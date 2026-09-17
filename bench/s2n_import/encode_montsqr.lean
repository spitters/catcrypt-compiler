import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontsqrP384
import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder

/-!
The imported s2n-bignum block `s2nMontsqrP384Block`, encoded to x86-64 machine code by the
owned scalar encoder `ScalarEncoder.encodeJBlock` under the identity allocation on the
sixteen canonical register names, and written as `.byte` directives inside s2n-bignum's
frame.

The body bytes are `encodeJBlock idAlloc s2nMontsqrP384Block`, where `idAlloc` is
`gpNames.map fun r => (r, r)`, the same allocation as `S2nMontmulP384.s2nAlloc`. No
theorem is stated over these bytes.

MEASUREMENT ARTIFACT. The prologue (`endbr64`, `pushq` of `%rbx`, `%rbp`, `%r12`, `%r13`,
`%r14`, `%r15`) and the epilogue (the `popq` sequence in reverse, `retq`) are literal text;
no theorem describes them. The file is the known-answer and timing target
`s2n-sqr-encoded` of `bench/p384_ecdsa_rust/src/bin/fieldbench.rs`.

The `#eval main` at the end writes `bench/s2n_import/gen/bignum_montsqr_p384_encoded.s`
when `lake lean` elaborates this file from the repository root
(`make -C bench/s2n_import encode-montsqr`). It fails, writing nothing, if the encoder's
gate `encodableJBlock` rejects the allocation or an instruction of the block is outside
the encoder's faithful fragment `encodableJInstr`.

## Main definitions

* `encodedBody`: the encoder's bytes for `s2nMontsqrP384Block` under `idAlloc`.
* `main`: writes them as `.byte` directives inside s2n-bignum's frame.
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontsqrP384

/-- The emitted symbol. -/
def encodedSymbol : String := "bignum_montsqr_p384_encoded"

/-- The identity allocation on the sixteen canonical register names. -/
def idAlloc : GpAlloc := gpNames.map fun r => (r, r)

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

/-- The encoded body. -/
def encodedBody : List (BitVec 8) := encodeJBlock idAlloc s2nMontsqrP384Block

/-- The assembly text: s2n-bignum's frame around the encoded body. -/
def encodedAsm : String :=
  "\n".intercalate
    ([ "# bignum_montsqr_p384 body: encodeJBlock idAlloc s2nMontsqrP384Block, "
          ++ toString encodedBody.length ++ " bytes.",
       "# The frame lines (endbr64, pushq, popq, retq) are literal text.",
       "\t.text",
       "\t.globl " ++ encodedSymbol,
       "\t.type " ++ encodedSymbol ++ ", @function",
       encodedSymbol ++ ":",
       "\tendbr64", "\tpushq %rbx", "\tpushq %rbp", "\tpushq %r12", "\tpushq %r13",
       "\tpushq %r14", "\tpushq %r15" ]
    ++ byteLines encodedBody
    ++ [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbp",
         "\tpopq %rbx", "\tretq",
         "\t.section .note.GNU-stack,\"\",@progbits" ])
  ++ "\n"

def main : IO Unit := do
  unless encodableJBlock idAlloc s2nMontsqrP384Block do
    throw <| IO.userError "encodableJBlock rejects idAlloc on s2nMontsqrP384Block"
  if let some i := firstUnencodable s2nMontsqrP384Block then
    throw <| IO.userError s!"instruction outside the encodable fragment: {repr i}"
  let path := "bench/s2n_import/gen/bignum_montsqr_p384_encoded.s"
  IO.FS.createDirAll "bench/s2n_import/gen"
  IO.FS.writeFile path encodedAsm
  IO.println s!"wrote {path} ({encodedBody.length} body bytes)"

#eval main
