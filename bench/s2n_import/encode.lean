import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Bytes

/-!
The imported s2n-bignum block `s2nMontmulP384Block`, encoded to x86-64 machine code by the
owned scalar encoder `ScalarEncoder.encodeJBlock` under the identity allocation
`S2nMontmulP384.s2nAlloc`, and written as `.byte` directives inside s2n-bignum's frame.

The body bytes are `encodeJBlock s2nAlloc s2nMontmulP384Block`, the byte string that
`Ascent.Demos.S2nMontmulP384.s2nMontmulP384Bytes_correct` is stated over: they decode to
264 instructions that compute the Montgomery product modulo `p384` under `JasminModel`.

MEASUREMENT ARTIFACT for the frame only. The prologue (`endbr64`, `pushq` of `%rbx`,
`%rbp`, `%r12`, `%r13`, `%r14`, `%r15`) and the epilogue (the `popq` sequence in reverse,
`retq`) are literal text; no theorem describes them. The file is the known-answer and
timing target `s2n-encoded` of `bench/p384_ecdsa_rust/src/bin/fieldbench.rs`.

The `#eval main` at the end writes `bench/s2n_import/gen/bignum_montmul_p384_encoded.s`
when `lake lean` elaborates this file from the repository root
(`make -C bench/s2n_import encode`). It fails, writing nothing, if the encoder's gate
`encodableJBlock` rejects the allocation.
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384

/-- The emitted symbol. -/
def encodedSymbol : String := "bignum_montmul_p384_encoded"

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
def encodedBody : List (BitVec 8) := encodeJBlock s2nAlloc s2nMontmulP384Block

/-- The assembly text: s2n-bignum's frame around the encoded body. -/
def encodedAsm : String :=
  "\n".intercalate
    ([ "# bignum_montmul_p384 body: encodeJBlock s2nAlloc s2nMontmulP384Block, "
          ++ toString encodedBody.length ++ " bytes, the subject of "
          ++ "S2nMontmulP384.s2nMontmulP384Bytes_correct.",
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
  unless encodableJBlock s2nAlloc s2nMontmulP384Block do
    throw <| IO.userError "encodableJBlock rejects s2nAlloc on s2nMontmulP384Block"
  let path := "bench/s2n_import/gen/bignum_montmul_p384_encoded.s"
  IO.FS.createDirAll "bench/s2n_import/gen"
  IO.FS.writeFile path encodedAsm
  IO.println s!"wrote {path} ({encodedBody.length} body bytes)"

#eval main
