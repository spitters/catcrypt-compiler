import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes

/-!
The four Curve25519 field kernels inside the red-zone leaf frame, `feMulFramed`,
`feSqrFramed`, `feAddFramed` and `feSubFramed` of
`Ascent.Demos.Fe25519KernelsBytes`, encoded to x86-64 machine code by the owned scalar
encoder `ScalarEncoder.encodeJBlock` under the identity allocation
`S2nMontmulP384.s2nAlloc`, and written as `.byte` directives, one `.s` file per kernel.

The bytes of each file are `encodeJBlock s2nAlloc KFramed`, the byte string that
`Fe25519KernelsBytes.KFramedBytes_correct` is stated over: they decode to instructions that
compute the field operation modulo `2^255 - 19` under `JasminModel` and end with `%rsp`,
`%rbx`, `%rbp`, `%r12`, `%r13`, `%r14`, `%r15` at their entry values;
`Fe25519KernelsBytes.KFramedBytes_constant_time` states that their leakage trace does not
depend on the state. The symbols and the argument registers are those of the files in
`crates/catcrypt-ed25519/asm/` of the SSProve-lean tree: `z = %rdi`, `x = %rsi`,
`y = %rdx`.

MEASUREMENT ARTIFACT for the entry marker and the return only. The literal lines are the
section and symbol directives, `endbr64` before the bytes, `retq` after them, and the
`.note.GNU-stack` section; no theorem describes `endbr64` or `retq`.

The `#eval main` at the end writes `bench/s2n_import/gen/fe25519_{mul,sqr,add,sub}_x86_from_lean.s`
when `lake lean` elaborates this file from the repository root. It fails, writing nothing,
if the encoder's gate `encodableJBlock` rejects the allocation on any of the four blocks.

## Main definitions

* `hexByte`, `byteLines`: a byte as a `0x..` literal, and bytes as `.byte` directive lines.
* `kernels`: the four framed kernels with their symbols and the theorem each file cites.
* `kernelAsm`: the assembly file of one kernel.
* `main`: writes the four files.
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384 (s2nAlloc)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes

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

/-- The kernels: symbol, framed block, and the theorem the bytes are the subject of. -/
def kernels : List (String × List (JInstr 64) × String) :=
  [ ("fe25519_mul_x86_from_lean", feMulFramed, "feMulFramedBytes_correct"),
    ("fe25519_sqr_x86_from_lean", feSqrFramed, "feSqrFramedBytes_correct"),
    ("fe25519_add_x86_from_lean", feAddFramed, "feAddFramedBytes_correct"),
    ("fe25519_sub_x86_from_lean", feSubFramed, "feSubFramedBytes_correct") ]

/-- The assembly text of one kernel: `endbr64`, the encoded framed block, `retq`. -/
def kernelAsm (sym : String) (block : List (JInstr 64)) (thm : String) : String :=
  let bytes := encodeJBlock s2nAlloc block
  "\n".intercalate
    ([ "# " ++ sym ++ ": encodeJBlock s2nAlloc, " ++ toString block.length
          ++ " instructions, " ++ toString bytes.length ++ " bytes, the subject of "
          ++ "Fe25519KernelsBytes." ++ thm ++ ".",
       "# The lines endbr64 and retq and the directives are literal text.",
       "\t.text",
       "\t.globl " ++ sym,
       "\t.type " ++ sym ++ ", @function",
       sym ++ ":",
       "\tendbr64" ]
    ++ byteLines bytes
    ++ [ "\tretq",
         "\t.size " ++ sym ++ ", .-" ++ sym,
         "\t.section .note.GNU-stack,\"\",@progbits" ])
  ++ "\n"

def main : IO Unit := do
  for (sym, block, _) in kernels do
    unless encodableJBlock s2nAlloc block do
      throw <| IO.userError s!"encodableJBlock rejects s2nAlloc on the block of {sym}"
  IO.FS.createDirAll "bench/s2n_import/gen"
  for (sym, block, thm) in kernels do
    let path := s!"bench/s2n_import/gen/{sym}.s"
    IO.FS.writeFile path (kernelAsm sym block thm)
    IO.println s!"wrote {path} ({(encodeJBlock s2nAlloc block).length} bytes)"

#eval main
