import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.CombSelectBytes

/-!
The three comb table selects `combSelectPhys`, `combSelect5Phys` and `combSelect6Phys` of
`Ascent.Demos.CombSelectBytes` (16, 32 and 64 entries), encoded to x86-64 machine code by
the owned scalar encoder `ScalarEncoder.encodeJBlock` under the identity allocation
`S2nMontmulP384.s2nAlloc`, and written as `.byte` directives, one `.s` file per kernel.

The bytes of each file are `encodeJBlock s2nAlloc KPhys`, the byte string that
`CombSelectBytes.KBytes_correct` is stated over: for an index in `%rsi` below the number of
entries they decode to instructions that store at `%rdx` the four words of that entry of
the table at `%rdi` under `JasminModel`, leave the table unchanged, and end with `%rsp`,
`%rbx`, `%rbp`, `%r12`, `%r13`, `%r14`, `%r15` at their entry values;
`CombSelectBytes.KBytes_constant_time` states that their leakage trace does not depend on
the state. The symbols and the argument registers are those of
`crates/catcrypt-ed25519/asm/ed25519_comb_select_x86_from_lean.s` and of
`bench/ed25519_comb_compare/gen_com/` in the SSProve-lean tree: `tbl = %rdi`, `d = %rsi`,
`z = %rdx`. The blocks write no callee-saved register, so the files carry no frame.

MEASUREMENT ARTIFACT for the entry marker and the return only. The literal lines are the
section and symbol directives, `endbr64` before the bytes, `retq` after them, and the
`.note.GNU-stack` section; no theorem describes `endbr64` or `retq`.

The `#eval main` at the end writes
`bench/s2n_import/gen/ed25519_comb{,5,6}_select_x86_from_lean.s` when `lake lean`
elaborates this file from the repository root. It fails, writing nothing, if the encoder's
gate `encodableJBlock` rejects the allocation on any of the three blocks.

## Main definitions

* `hexByte`, `byteLines`: a byte as a `0x..` literal, and bytes as `.byte` directive lines.
* `kernels`: the three kernels with their symbols and the theorem each file cites.
* `kernelAsm`: the assembly file of one kernel.
* `main`: writes the three files.
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384 (s2nAlloc)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.CombSelectBytes

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

/-- The kernels: symbol, physical block, and the theorem the bytes are the subject of. -/
def kernels : List (String × List (JInstr 64) × String) :=
  [ ("ed25519_comb_select_x86_from_lean", combSelectPhys, "combSelectBytes_correct"),
    ("ed25519_comb5_select_x86_from_lean", combSelect5Phys, "combSelect5Bytes_correct"),
    ("ed25519_comb6_select_x86_from_lean", combSelect6Phys, "combSelect6Bytes_correct") ]

/-- The assembly text of one kernel: `endbr64`, the encoded block, `retq`. -/
def kernelAsm (sym : String) (block : List (JInstr 64)) (thm : String) : String :=
  let bytes := encodeJBlock s2nAlloc block
  "\n".intercalate
    ([ "# " ++ sym ++ ": encodeJBlock s2nAlloc, " ++ toString block.length
          ++ " instructions, " ++ toString bytes.length ++ " bytes, the subject of "
          ++ "CombSelectBytes." ++ thm ++ ".",
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
