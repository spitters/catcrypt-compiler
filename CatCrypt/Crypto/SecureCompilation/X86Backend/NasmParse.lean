/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# A parser from NASM Intel-syntax assembly into `JInstr 64` blocks

`parseNasm` reads assembly text in the NASM Intel syntax CryptOpt writes (for
instance `bench/cryptopt/fiat_curve25519_carry_mul.asm`) into the straight-line
instruction list that `runBlock : JState 64 → List (JInstr 64) → JState 64`
executes. `printNasm` prints such a list back to the canonical text form. The
parser maps each instruction to the one `JInstr` constructor whose `evalInstr`
arm is that instruction's semantics; an instruction with no such constructor is
an error naming the source line, never a different instruction.

## Accepted text

* Comments from `;` to the end of the line, blank lines, `SECTION` and `GLOBAL`
  directives, and label lines `name:`. Directives and labels produce no
  instruction.
* Operands: the sixteen 64-bit general-purpose registers; the 8-, 16- and
  32-bit low subregisters (`al`, `r10b`, `ax`, `r10w`, `eax`, `r10d`) in the
  forms that take them; immediates in decimal or `0x` hexadecimal, with an
  optional `-` sign; and memory operands `[ base ± disp ]`, `[ base + idx ]`,
  `[ base + idx*scale ]` with an optional `qword` size. Mnemonics and register
  names are case-insensitive.
* A subregister names the low bits of its 64-bit register: the produced
  `JInstr` names the 64-bit register, and the width is carried by the
  instruction (`setcc` writes a byte, `testN sz` tests `sz` bits, `movzx`/`movsx`
  carry their source width, a shift count `cl` reads the low six bits of `rcx`).
  The high-byte registers `ah`, `ch`, `dh`, `bh` have no such reading and are
  rejected.
* Register names in the produced `JInstr` carry the AT&T `%` prefix (`%rax`),
  the spelling `AsmPrinter.regOf` and the ascent modules use.
* `ret` with no operand is accepted as the last instruction of the text only:
  `parseNasm` returns the instructions before it, and any instruction after a
  `ret` is an error. A straight-line `JInstr` block has no return instruction.

`JState.mem` is keyed by the base register's name and a byte offset, so a
parsed memory operand `[ rax + 0x20 ]` denotes cell `("%rax", 32)`. That cell
equals the machine cell at address `rax + 32` for every access through
`%rax` exactly when the value of `%rax` is fixed across those accesses and the
banks of registers holding equal pointers are equal in the initial state.

## Canonical text

One instruction per line, lower case, `mnemonic op1, op2, op3`; immediates and
displacements in lower-case `0x` hexadecimal; a memory operand without index is
printed `[ base + 0xd ]` or `[ base - 0xd ]` (a zero displacement is printed),
an indexed one `[ base + idx ]` or `[ base + idx*scale ]` followed by a
displacement only when it is nonzero. Two lexical identifications hold in the
canonical form: a condition code is spelled by one name per condition
(`setc` and `setnae` are `setb`, `cmovz` is `cmove`, `cmovnle` is `cmovg`; the
names are `condName`), and an immediate in `[2^64 - 2^31, 2^64)` is spelled as
the negative number congruent to it modulo `2^64` (`0xfffffffffffffffd` is
`-0x3`), the value a sign-extended 32-bit immediate denotes. A final `ret` is
not part of the canonical text. `canonicalNasm` produces this form from the
source text at the lexical level, without the `JInstr` mapping, and
`NasmParseKat` checks `printNasm ∘ parseNasm` against it.

## Coverage of `fiat_curve25519_carry_mul.asm`

The file has 167 instructions before its final `ret`. The table lists, for each
mnemonic and operand form of the file, the `JInstr` constructor and the flags
its `evalInstr` arm reads and writes, or the gap.

| Mnemonic, form (count) | `JInstr` | Flags read / written |
|---|---|---|
| `mov r, r` / `mov r, imm` | `mov` | none / none |
| `mov r, [b + d]` | `loadMem` | none / none |
| `mov [b + d], r` | `storeMem` | none / none |
| `mulx hi, lo, r` | `mulx hi lo (.reg "%rdx") (.reg r)` | none / none |
| `mulx hi, lo, [b + d]` | `mulxMem hi lo (.reg "%rdx") b d` | none / none |
| `adcx r, r` (13 of 17) | `adcx` | CF / CF only |
| `adcx r, [b + d]` (4) | `adcxMem` | CF / CF only |
| `adox r, r` (12 of 16) | `adox` | OF / OF only |
| `adox r, [b + d]` (4) | `adoxMem` | OF / OF only |
| `add r, r` / `add r, imm` (10 of 12) | `add` | none / OF CF SF PF ZF |
| `add r, [b + d]` (2) | `addMem` | none / OF CF SF PF ZF |
| `adc r, imm` (4) | `adc` | CF / OF CF SF PF ZF |
| `xor r, r` (5) | `xor_` | none / OF = CF = 0, SF PF ZF |
| `sub r, imm` (1) | `sub` | none / OF CF SF PF ZF |
| `shr r, imm` (2) | `shr` | none / `x86_SHR` flags |
| `lea r, [b + i]` (3) | `lea r b i 1 0` | none / none |
| `imul r, r', imm` (1) | `imulri` | none / OF CF, SF PF ZF undefined |
| `imul r, [b + d], imm` (4) | `imulriMem` | none / OF CF, SF PF ZF undefined |
| `bzhi r, r', r''` (7) | `bzhi` | none / OF = 0, CF, SF ZF, PF undefined |
| `shrd r, r', imm` (5) | `shrd` | none / `x86_SHRD` flags |
| `xchg r, r'` (1) | `xchg` | none / none |
| `test al, al` (1) | `testN 8` | none / OF = CF = 0, SF PF ZF |

Every instruction of the file has a `JInstr` constructor. The `OF` that `bzhi`
clears is read by the `adox` on lines 98 and 136 of the file. The parser also maps
`add [b + d], r`, `add qword [b + d], imm` (`addToMem`) and `imul r, [b + d]`
(`imulMem`), which the file does not use.

## Coverage of `fiat_curve25519_solinas_square.asm`

The file has 99 instructions before its final `ret`, and every one has a `JInstr`
constructor: beyond the forms of the table above it uses `inc r` (`inc`),
`clc` (`clc`), `setc r8` (`setcc .b`), `movzx r, r8` (`movzx r 8 r'`),
`cmovo r, r'` (`cmovcc .o`), `test al, al` (`testN 8`) and `mov r, -imm`
(`mov r (.imm (2^64 - imm))`).

## Main definitions

* `Operand`, `MemRef`, `Line`: the lexical form of an operand and of a line.
* `lexLine`: one source line to its lexical form.
* `toJInstr`: a lexical instruction to its `JInstr 64`, or an error naming it.
* `toSyntax`: a `JInstr 64` to its lexical instruction, the inverse of `toJInstr`
  on the parser's image.
* `parseNasm`, `printNasm`, `canonicalNasm`: whole-text parse, print and
  canonicalisation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParse

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. Lexical layer -/

/-- The sixteen 64-bit general-purpose register names, in Intel spelling. -/
def gpr64Names : List String :=
  ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
   "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]

/-- The low subregisters of the sixteen 64-bit registers, as
    `(name, 64-bit register, width)`, in Intel spelling. -/
def lowSubRegs : List (String × String × Nat) :=
  [("al", "rax", 8), ("cl", "rcx", 8), ("dl", "rdx", 8), ("bl", "rbx", 8),
   ("spl", "rsp", 8), ("bpl", "rbp", 8), ("sil", "rsi", 8), ("dil", "rdi", 8),
   ("ax", "rax", 16), ("cx", "rcx", 16), ("dx", "rdx", 16), ("bx", "rbx", 16),
   ("sp", "rsp", 16), ("bp", "rbp", 16), ("si", "rsi", 16), ("di", "rdi", 16),
   ("eax", "rax", 32), ("ecx", "rcx", 32), ("edx", "rdx", 32), ("ebx", "rbx", 32),
   ("esp", "rsp", 32), ("ebp", "rbp", 32), ("esi", "rsi", 32), ("edi", "rdi", 32)] ++
  (List.range 8).flatMap (fun i =>
    let n := s!"r{i + 8}"
    [(n ++ "b", n, 8), (n ++ "w", n, 16), (n ++ "d", n, 32)])

/-- The 8-, 16- and 32-bit general-purpose register names, in Intel spelling:
    the low subregisters and the four high-byte registers. -/
def subRegNames : List String :=
  lowSubRegs.map (·.1) ++ ["ah", "ch", "dh", "bh"]

/-- The 64-bit register and the width of a low subregister name. -/
def subRegParent? (r : String) : Option (String × Nat) :=
  (lowSubRegs.find? (·.1 == r)).map (·.2)

/-- The low subregister name of width `sz` of a 64-bit register name. -/
def subRegName? (parent : String) (sz : Nat) : Option String :=
  (lowSubRegs.find? (fun e => e.2.1 == parent && e.2.2 == sz)).map (·.1)

/-- The canonical condition-code name of a Jasmin condition, as it follows `set`
    and `cmov`: `nb` is `ae`, `nbe` is `a`, `nl` is `ge` and `nle` is `g`; the
    other twelve keep their `Condt` name. -/
def condName : Condt → String
  | .o => "o"  | .no => "no" | .b => "b"   | .nb => "ae"
  | .e => "e"  | .ne => "ne" | .be => "be" | .nbe => "a"
  | .s => "s"  | .ns => "ns" | .p => "p"   | .np => "np"
  | .l => "l"  | .nl => "ge" | .le => "le" | .nle => "g"

/-- The condition a NASM condition-code suffix names, with every alias the
    Intel SDM lists (`c`, `nae` for `b`; `z` for `e`; `pe` for `p`; …). -/
def condOfSuffix? : String → Option Condt
  | "o" => some .o | "no" => some .no
  | "b" | "c" | "nae" => some .b
  | "ae" | "nc" | "nb" => some .nb
  | "e" | "z" => some .e
  | "ne" | "nz" => some .ne
  | "be" | "na" => some .be
  | "a" | "nbe" => some .nbe
  | "s" => some .s | "ns" => some .ns
  | "p" | "pe" => some .p
  | "np" | "po" => some .np
  | "l" | "nge" => some .l
  | "ge" | "nl" => some .nl
  | "le" | "ng" => some .le
  | "g" | "nle" => some .nle
  | _ => none

/-- A mnemonic with its condition code, if it has one, spelled by `condName`. -/
def canonMnemonic (word : List Char) : List Char :=
  match word with
  | 'c' :: 'm' :: 'o' :: 'v' :: cc =>
      match condOfSuffix? (String.ofList cc) with
      | some c => "cmov".toList ++ (condName c).toList
      | none => word
  | 's' :: 'e' :: 't' :: cc =>
      match condOfSuffix? (String.ofList cc) with
      | some c => "set".toList ++ (condName c).toList
      | none => word
  | _ => word

/-- A memory operand `size [ base + idx*scale ± disp ]` as written. The base and
    index are Intel register names without prefix. -/
structure MemRef where
  size : Option String
  base : String
  idx : Option (String × Nat)
  disp : Int

/-- An operand as written: a 64-bit register, a narrower register, a
    non-negative immediate, a negative immediate `-v` with `0 < v ≤ 2^31`, or a
    memory operand. -/
inductive Operand where
  | reg (r : String)
  | subreg (r : String)
  | imm (v : Nat)
  | negImm (v : Nat)
  | mem (m : MemRef)

/-- A source line as written: blank or comment-only, a `SECTION`/`GLOBAL`
    directive, a label, or an instruction with its operands. -/
inductive Line where
  | blank
  | directive (text : String)
  | label (name : String)
  | instr (mnemonic : String) (ops : List Operand)

/-- A character list without leading and trailing whitespace. -/
def trimChars (cs : List Char) : List Char :=
  ((cs.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- The value of a hexadecimal digit, lower case. -/
def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The value of a non-empty digit string in base `b` (10 or 16). -/
def digitsVal (b : Nat) : List Char → Option Nat
  | [] => none
  | c :: cs => (c :: cs).foldlM (fun acc d =>
      (hexDigit? d).bind fun v => if v < b then some (acc * b + v) else none) 0

/-- A non-negative number in decimal or `0x` hexadecimal. -/
def parseNum? : List Char → Option Nat
  | '0' :: 'x' :: rest => digitsVal 16 rest
  | cs => digitsVal 10 cs

/-- The lexical immediate of a 64-bit value `v`: the negative spelling
    `-(2^64 - v)` for `v` in `[2^64 - 2^31, 2^64)`, the value itself otherwise. -/
def immOperand (v : Nat) : Operand :=
  if 2 ^ 64 - 2 ^ 31 ≤ v ∧ v < 2 ^ 64 then .negImm (2 ^ 64 - v) else .imm v

/-- Split a whitespace-free memory expression at top-level `+` and `-` into
    signed terms; `true` marks a positive term. -/
def splitTerms (cs : List Char) : List (Bool × List Char) :=
  go true [] cs
where
  /-- The splitting loop with the current sign and the reversed current term. -/
  go (pos : Bool) (cur : List Char) : List Char → List (Bool × List Char)
    | [] => [(pos, cur.reverse)]
    | '+' :: rest => (pos, cur.reverse) :: go true [] rest
    | '-' :: rest => (pos, cur.reverse) :: go false [] rest
    | c :: rest => go pos (c :: cur) rest

/-- One term of a memory expression: a register with a scale, or a number. -/
inductive MemTerm where
  | reg (r : String) (scale : Nat) (scaled : Bool)
  | num (v : Nat)

/-- Classify one term: `reg`, `reg*n`, `n*reg`, or a number. -/
def memTerm (t : List Char) : Except String MemTerm :=
  let s := String.ofList t
  match t.splitOn '*' with
  | [a, b] =>
      let sa := String.ofList a
      let sb := String.ofList b
      if gpr64Names.contains sa then
        match parseNum? b with
        | some n => pure (.reg sa n true)
        | none => throw s!"bad scale in memory term {s}"
      else if gpr64Names.contains sb then
        match parseNum? a with
        | some n => pure (.reg sb n true)
        | none => throw s!"bad scale in memory term {s}"
      else throw s!"no 64-bit register in memory term {s}"
  | [_] =>
      if gpr64Names.contains s then pure (.reg s 1 false)
      else match parseNum? t with
        | some n => pure (.num n)
        | none => throw s!"unrecognised memory term {s}"
  | _ => throw s!"unrecognised memory term {s}"

/-- Parse the inside of `[ ... ]` given the optional size keyword. -/
def parseMem (size : Option String) (inner : List Char) : Except String Operand := do
  let terms := splitTerms (inner.filter (fun c => !c.isWhitespace))
  let mut base : Option String := none
  let mut idx : Option (String × Nat) := none
  let mut disp : Int := 0
  for (pos, t) in terms do
    if t.isEmpty then throw "empty term in memory operand"
    match ← memTerm t with
    | .num v => disp := if pos then disp + v else disp - v
    | .reg r sc scaled =>
        if !pos then throw s!"negated register {r} in memory operand"
        if base.isNone && !scaled then base := some r
        else if idx.isNone then idx := some (r, sc)
        else throw "more than two registers in memory operand"
  match base with
  | none => throw "memory operand without a base register"
  | some b => pure (.mem { size, base := b, idx, disp })

/-- Parse one operand text (already lower case). -/
def parseOperand (cs : List Char) : Except String Operand := do
  let cs := trimChars cs
  let s := String.ofList cs
  if cs.contains '[' then
    let pre := trimChars (cs.takeWhile (· ≠ '['))
    let rest := (cs.dropWhile (· ≠ '[')).drop 1
    let inner := rest.takeWhile (· ≠ ']')
    let after := trimChars ((rest.dropWhile (· ≠ ']')).drop 1)
    unless rest.contains ']' && after.isEmpty do
      throw s!"malformed memory operand {s}"
    let size ← match String.ofList pre with
      | "" => pure none
      | "byte" => pure (some "byte")
      | "word" => pure (some "word")
      | "dword" => pure (some "dword")
      | "qword" => pure (some "qword")
      | k => throw s!"unrecognised size keyword {k}"
    parseMem size inner
  else if gpr64Names.contains s then pure (.reg s)
  else if subRegNames.contains s then pure (.subreg s)
  else match cs with
    | '-' :: rest =>
        match parseNum? rest with
        | some 0 => pure (.imm 0)
        | some v =>
            if v ≤ 2 ^ 31 then pure (.negImm v)
            else throw s!"negative immediate {s} is below -2^31"
        | none => throw s!"unrecognised operand {s}"
    | _ =>
        match parseNum? cs with
        | some v => pure (immOperand v)
        | none => throw s!"unrecognised operand {s}"

/-- Split an operand list at commas outside brackets. -/
def splitOperands (cs : List Char) : List (List Char) :=
  go 0 [] cs
where
  /-- The splitting loop with the bracket depth and the reversed current field. -/
  go (depth : Nat) (cur : List Char) : List Char → List (List Char)
    | [] => [cur.reverse]
    | ',' :: rest =>
        if depth = 0 then cur.reverse :: go depth [] rest
        else go depth (',' :: cur) rest
    | '[' :: rest => go (depth + 1) ('[' :: cur) rest
    | ']' :: rest => go (depth - 1) (']' :: cur) rest
    | c :: rest => go depth (c :: cur) rest

/-- Lex one source line. Comments run from `;` to the end of the line. A
    condition-code mnemonic is spelled by `canonMnemonic`. -/
def lexLine (ln : String) : Except String Line := do
  let cs := trimChars (ln.toList.takeWhile (· ≠ ';'))
  if cs.isEmpty then return .blank
  let lower := cs.map Char.toLower
  let word := lower.takeWhile (fun c => !c.isWhitespace)
  let rest := trimChars (lower.dropWhile (fun c => !c.isWhitespace))
  match String.ofList word with
  | "section" | "global" => return .directive (String.ofList cs)
  | _ => pure ()
  if rest.isEmpty && word.getLast? == some ':' then
    let nm := word.dropLast
    if !nm.isEmpty && nm.all (fun c => c.isAlphanum || c == '_' || c == '.') then
      return .label (String.ofList (cs.dropLast))
    throw s!"malformed label {String.ofList cs}"
  unless word.all Char.isAlphanum do
    throw s!"malformed mnemonic {String.ofList word}"
  let ops ← if rest.isEmpty then pure [] else (splitOperands rest).mapM parseOperand
  return .instr (String.ofList (canonMnemonic word)) ops

/-! ## 2. Canonical printing of the lexical form -/

/-- A natural number in lower-case `0x` hexadecimal. -/
def hex (v : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 v)

/-- The canonical text of a memory operand. -/
def printMem (m : MemRef) : String :=
  let sz := match m.size with
    | some k => k ++ " "
    | none => ""
  let dispTxt :=
    if m.disp < 0 then s!" - {hex m.disp.natAbs}" else s!" + {hex m.disp.natAbs}"
  let body := match m.idx with
    | none => m.base ++ dispTxt
    | some (i, sc) =>
        let it := if sc = 1 then i else s!"{i}*{sc}"
        m.base ++ " + " ++ it ++ (if m.disp = 0 then "" else dispTxt)
  sz ++ "[ " ++ body ++ " ]"

/-- The canonical text of an operand. -/
def printOperand : Operand → String
  | .reg r => r
  | .subreg r => r
  | .imm v => hex v
  | .negImm v => "-" ++ hex v
  | .mem m => printMem m

/-- The canonical text of an instruction. -/
def printInstrSyntax (mn : String) (ops : List Operand) : String :=
  if ops.isEmpty then mn else mn ++ " " ++ ", ".intercalate (ops.map printOperand)

/-- A `ret` with no operand, the terminator `parseNasm` accepts as the last
    instruction. -/
def isRet (mn : String) (ops : List Operand) : Bool :=
  mn == "ret" && ops.isEmpty

/-! ## 3. Mapping to `JInstr 64` -/

/-- The `JInstr` register name of an Intel 64-bit register name. -/
def jreg (r : String) : String := "%" ++ r

/-- The Intel name of a `JInstr` register name, when it is a 64-bit GPR. -/
def intelReg (r : String) : Except String String :=
  match r.toList with
  | '%' :: n =>
      let s := String.ofList n
      if gpr64Names.contains s then pure s
      else throw s!"register {r} is not a 64-bit general-purpose register"
  | _ => throw s!"register {r} has no AT&T prefix"

/-- The Intel low subregister name of width `sz` of a `JInstr` register name. -/
def intelSubReg (r : String) (sz : Nat) : Except String String := do
  let p ← intelReg r
  match subRegName? p sz with
  | some n => pure n
  | none => throw s!"register {r} has no {sz}-bit subregister name"

/-- The `JInstr` register and the width of a lexical low subregister. -/
def subRegOf (r : String) : Except String (String × Nat) :=
  match subRegParent? r with
  | some (p, sz) => pure (jreg p, sz)
  | none => throw s!"{r} is a high-byte register: no JInstr register holds it"

/-- The 64-bit value of a sign-extended 32-bit immediate operand. -/
def simm32? : Operand → Option Nat
  | .imm v => if v < 2 ^ 31 then some v else none
  | .negImm v => some (2 ^ 64 - v)
  | _ => none

/-- A shift or rotate count operand: an immediate below 256, or `cl`, which is
    the register `%rcx` (the count is masked to its low six bits, which `cl`
    holds). -/
def countOf? : Operand → Option JOperand
  | .imm v => if v < 256 then some (.imm v) else none
  | .subreg "cl" => some (.reg "%rcx")
  | _ => none

/-- The two-operand flag-setting ALU mnemonics with a `JInstr` constructor of
    shape `dst src`. -/
def aluOf? : String → Option (String → JOperand → JInstr 64)
  | "add" => some .add
  | "sub" => some .sub
  | "adc" => some .adc
  | "sbb" => some .sbb
  | "and" => some .and_
  | "or" => some .or_
  | "xor" => some .xor_
  | "cmp" => some .cmp
  | "test" => some .test
  | _ => none

/-- The shift and rotate mnemonics taking an immediate or `cl` count. -/
def shiftOf? : String → Option (String → JOperand → JInstr 64)
  | "shl" => some .shl
  | "shr" => some .shr
  | "sar" => some .sar
  | "rol" => some .rol
  | "ror" => some .ror
  | "rcl" => some .rcl
  | "rcr" => some .rcr
  | _ => none

/-- The double-precision shifts. -/
def dshiftOf? : String → Option (String → String → JOperand → JInstr 64)
  | "shld" => some .shld
  | "shrd" => some .shrd
  | _ => none

/-- The bit-test mnemonics. -/
def btOf? : String → Option (String → JOperand → JInstr 64)
  | "bt" => some .bt
  | "btr" => some .btr
  | "bts" => some .bts
  | _ => none

/-- The condition of a `cmov<cc>` mnemonic. -/
def cmovCond? (mn : String) : Option Condt :=
  match mn.toList with
  | 'c' :: 'm' :: 'o' :: 'v' :: cc => condOfSuffix? (String.ofList cc)
  | _ => none

/-- The condition of a `set<cc>` mnemonic. -/
def setCond? (mn : String) : Option Condt :=
  match mn.toList with
  | 's' :: 'e' :: 't' :: cc => condOfSuffix? (String.ofList cc)
  | _ => none

/-- The mnemonics whose forms take a subregister operand. -/
def takesSubReg (mn : String) : Bool :=
  mn == "test" || mn == "movzx" || mn == "movsx" || mn == "movsxd" ||
    (setCond? mn).isSome || (shiftOf? mn).isSome || (dshiftOf? mn).isSome

/-- A memory operand without index and with no size or `qword` size, as the
    `(base, displacement)` pair of `loadMem`/`storeMem`/`mulxMem`. -/
def plainMem (m : MemRef) : Except String (String × Int) := do
  unless m.size.isNone || m.size == some "qword" do
    throw s!"{m.size.getD ""} memory operand: JMem is word-granular"
  match m.idx with
  | none => pure (m.base, m.disp)
  | some _ => throw "indexed memory operand in a form with no indexed JInstr constructor"

/-- A valid SIB scale. -/
def validScale (sc : Nat) : Bool := sc == 1 || sc == 2 || sc == 4 || sc == 8

/-- A lexical instruction to its `JInstr 64`. The error names the missing
    constructor or operand form. -/
def toJInstr (mn : String) (ops : List Operand) : Except String (JInstr 64) := do
  unless takesSubReg mn do
    for o in ops do
      if let .subreg r := o then
        throw s!"{mn} on the sub-64-bit register {r}: JInstr registers are 64-bit"
  if mn == "test" then
    match ops with
    | [.subreg a, .subreg b] =>
        let (ra, sa) ← subRegOf a
        let (rb, sb) ← subRegOf b
        unless sa = sb do throw s!"test of registers of widths {sa} and {sb}"
        return .testN sa ra (.reg rb)
    | [.subreg a, .imm v] =>
        let (ra, sa) ← subRegOf a
        if v < 2 ^ sa then return .testN sa ra (.imm v)
        else throw s!"test immediate {hex v} does not fit {sa} bits"
    | [.subreg _, _] | [_, .subreg _] =>
        throw "test of a subregister with an operand of another width"
    | _ => pure ()
  if let some f := aluOf? mn then
    match ops with
    | [.reg d, .reg s] => return f (jreg d) (.reg (jreg s))
    | [.reg d, o@(.imm _)] | [.reg d, o@(.negImm _)] =>
        match simm32? o with
        | some v => return f (jreg d) (.imm v)
        | none => throw s!"{mn} immediate {printOperand o} is not a sign-extended imm32"
    | [.reg d, .mem m] =>
        if mn == "add" then
          let (b, off) ← plainMem m
          return .addMem (jreg d) (jreg b) off
        else throw s!"{mn} with a memory source operand: no JInstr constructor"
    | [.mem m, .reg s] =>
        if mn == "add" then
          let (b, off) ← plainMem m
          return .addToMem (jreg b) off (.reg (jreg s))
        else throw s!"{mn} with a memory destination operand: no JInstr constructor"
    | [.mem m, o] =>
        if mn == "add" then
          unless m.size == some "qword" do
            throw "add of an immediate to memory needs the qword size"
          let some v := simm32? o
            | throw s!"add immediate {printOperand o} is not a sign-extended imm32"
          let (b, off) ← plainMem m
          return .addToMem (jreg b) off (.imm v)
        else throw s!"{mn} with a memory destination operand: no JInstr constructor"
    | _ => throw s!"{mn}: unsupported operand form"
  if let some f := shiftOf? mn then
    match ops with
    | [.reg d, c] =>
        match countOf? c with
        | some a => return f (jreg d) a
        | none => throw s!"{mn} count {printOperand c} is neither an imm8 nor cl"
    | _ => throw s!"{mn}: only the register, count form has a JInstr constructor"
  if let some f := dshiftOf? mn then
    match ops with
    | [.reg d, .reg s, c] =>
        match countOf? c with
        | some a => return f (jreg d) (jreg s) a
        | none => throw s!"{mn} count {printOperand c} is neither an imm8 nor cl"
    | _ => throw s!"{mn}: only the register, register, count form has a JInstr constructor"
  if let some f := btOf? mn then
    match ops with
    | [.reg d, .reg s] => return f (jreg d) (.reg (jreg s))
    | [.reg d, .imm v] =>
        if v < 256 then return f (jreg d) (.imm v)
        else throw s!"{mn} bit offset {hex v} is not an imm8"
    | _ => throw s!"{mn}: only the register, register or imm8 form has a JInstr constructor"
  if let some c := cmovCond? mn then
    match ops with
    | [.reg d, .reg s] => return .cmovcc c (jreg d) (.reg (jreg s))
    | _ => throw s!"{mn}: only the register, register form has a JInstr constructor"
  if let some c := setCond? mn then
    match ops with
    | [.subreg r] =>
        let (p, sz) ← subRegOf r
        if sz = 8 then return .setcc c p
        else throw s!"{mn} on the {sz}-bit register {r}: SETcc writes a byte"
    | _ => throw s!"{mn}: only the byte-register form has a JInstr constructor"
  match mn, ops with
  | "mov", [.reg d, .reg s] => return .mov (jreg d) (.reg (jreg s))
  | "mov", [.reg d, .imm v] =>
      if v < 2 ^ 64 then return .mov (jreg d) (.imm v)
      else throw s!"mov immediate {hex v} exceeds 64 bits"
  | "mov", [.reg d, .negImm v] => return .mov (jreg d) (.imm (2 ^ 64 - v))
  | "mov", [.reg d, .mem m] =>
      match m.idx, m.disp with
      | some (i, sc), 0 =>
          unless m.size.isNone || m.size == some "qword" do
            throw "sub-word indexed load: JMem is word-granular"
          unless validScale sc do throw s!"invalid scale {sc}"
          return .loadMemIdx (jreg d) (jreg m.base) (jreg i) sc
      | _, _ =>
          let (b, off) ← plainMem m
          return .loadMem (jreg d) (jreg b) off
  | "mov", [.mem m, .reg s] =>
      match m.idx, m.disp with
      | some (i, sc), 0 =>
          unless m.size.isNone || m.size == some "qword" do
            throw "sub-word indexed store: JMem is word-granular"
          unless validScale sc do throw s!"invalid scale {sc}"
          return .storeMemIdx (jreg m.base) (jreg i) sc (.reg (jreg s))
      | _, _ =>
          let (b, off) ← plainMem m
          return .storeMem (jreg b) off (.reg (jreg s))
  | "mov", [.mem m, o] =>
      unless m.size == some "qword" do
        throw "mov of an immediate to memory needs the qword size"
      let some v := simm32? o
        | throw s!"mov immediate {printOperand o} is not a sign-extended imm32"
      let (b, off) ← plainMem m
      return .storeMem (jreg b) off (.imm v)
  | "movzx", [.reg d, .subreg s] =>
      let (p, sz) ← subRegOf s
      if sz = 8 ∨ sz = 16 then return .movzx (jreg d) sz p
      else throw s!"movzx from the {sz}-bit register {s} has no NASM form"
  | "movsx", [.reg d, .subreg s] =>
      let (p, sz) ← subRegOf s
      if sz = 8 ∨ sz = 16 then return .movsx (jreg d) sz p
      else throw s!"movsx from the {sz}-bit register {s}: NASM spells it movsxd"
  | "movsxd", [.reg d, .subreg s] =>
      let (p, sz) ← subRegOf s
      if sz = 32 then return .movsx (jreg d) 32 p
      else throw s!"movsxd from the {sz}-bit register {s}"
  | "imul", [.reg d, .reg s] => return .imul (jreg d) (.reg (jreg s))
  | "imul", [.reg d, .reg s, o] =>
      let some v := simm32? o
        | throw s!"imul immediate {printOperand o} is not a sign-extended imm32"
      if s = d then return .imul (jreg d) (.imm v)
      else return .imulri (jreg d) (jreg s) v
  | "imul", [.reg d, .mem m, o] =>
      let some v := simm32? o
        | throw s!"imul immediate {printOperand o} is not a sign-extended imm32"
      let (b, off) ← plainMem m
      return .imulriMem (jreg d) (jreg b) off v
  | "imul", [.reg d, .mem m] =>
      let (b, off) ← plainMem m
      return .imulMem (jreg d) (jreg b) off
  | "imul", [.reg s] => return .imulWide "%rdx" "%rax" (jreg s)
  | "mul", [.reg s] => return .mul "%rdx" "%rax" (jreg s)
  | "neg", [.reg d] => return .neg (jreg d)
  | "not", [.reg d] => return .not_ (jreg d)
  | "inc", [.reg d] => return .inc (jreg d)
  | "dec", [.reg d] => return .dec (jreg d)
  | "clc", [] => return .clc
  | "stc", [] => return .stc
  | "xchg", [.reg a, .reg b] => return .xchg (jreg a) (jreg b)
  | "andn", [.reg d, .reg a, .reg b] => return .andn (jreg d) (jreg a) (jreg b)
  | "shlx", [.reg d, .reg a, .reg c] => return .shlx (jreg d) (jreg a) (jreg c)
  | "shrx", [.reg d, .reg a, .reg c] => return .shrx (jreg d) (jreg a) (jreg c)
  | "sarx", [.reg d, .reg a, .reg c] => return .sarx (jreg d) (jreg a) (jreg c)
  | "rorx", [.reg d, .reg a, .imm v] =>
      if v < 256 then return .rorx (jreg d) (jreg a) (.imm v)
      else throw s!"rorx count {hex v} is not an imm8"
  | "lea", [.reg d, .mem m] =>
      unless m.size.isNone do throw "lea with a size keyword"
      match m.idx with
      | none => return .lea (jreg d) (jreg m.base) (jreg m.base) 0 m.disp
      | some (i, sc) =>
          unless validScale sc do throw s!"invalid scale {sc}"
          return .lea (jreg d) (jreg m.base) (jreg i) sc m.disp
  | "mulx", [.reg hi, .reg lo, .reg s] =>
      return .mulx (jreg hi) (jreg lo) (.reg "%rdx") (.reg (jreg s))
  | "mulx", [.reg hi, .reg lo, .mem m] =>
      let (b, off) ← plainMem m
      return .mulxMem (jreg hi) (jreg lo) (.reg "%rdx") (jreg b) off
  | "adcx", [.reg d, .reg s] => return .adcx (jreg d) (.reg (jreg s))
  | "adox", [.reg d, .reg s] => return .adox (jreg d) (.reg (jreg s))
  | "adcx", [.reg d, .mem m] =>
      let (b, off) ← plainMem m
      return .adcxMem (jreg d) (jreg b) off
  | "adox", [.reg d, .mem m] =>
      let (b, off) ← plainMem m
      return .adoxMem (jreg d) (jreg b) off
  | "bzhi", [.reg d, .reg s, .reg i] => return .bzhi (jreg d) (jreg s) (jreg i)
  | "ret", _ => throw "ret: a straight-line JInstr block has no return; parseNasm \
      accepts it as the last instruction"
  | _, _ => throw s!"{mn} with {ops.length} operands: no JInstr constructor"

/-- A memory operand without size keyword. -/
def memOp (base : String) (idx : Option (String × Nat)) (disp : Int) : Operand :=
  .mem { size := none, base := base, idx := idx, disp := disp }

/-- The lexical form of a two-operand ALU instruction. -/
def aluSyntax (mn d : String) (s : JOperand) : Except String (String × List Operand) := do
  let d ← intelReg d
  match s with
  | .reg r => return (mn, [.reg d, .reg (← intelReg r)])
  | .imm v => return (mn, [.reg d, immOperand v])

/-- The lexical form of a shift or rotate count: an immediate, or `cl` for
    `%rcx`. -/
def countSyntax (mn : String) : JOperand → Except String Operand
  | .imm v => pure (.imm v)
  | .reg "%rcx" => pure (.subreg "cl")
  | .reg r => throw s!"{mn} by the register {r} has no NASM form (the count register is cl)"

/-- The lexical form of a shift or rotate. -/
def shiftSyntax (mn d : String) (a : JOperand) : Except String (String × List Operand) := do
  let d ← intelReg d
  return (mn, [.reg d, ← countSyntax mn a])

/-- The lexical form of a double-precision shift. -/
def dshiftSyntax (mn d s : String) (a : JOperand) :
    Except String (String × List Operand) := do
  let d ← intelReg d
  let s ← intelReg s
  return (mn, [.reg d, .reg s, ← countSyntax mn a])

/-- The lexical form of a conditional move from a register. -/
def cmovSyntax (mn d : String) (s : JOperand) : Except String (String × List Operand) := do
  let d ← intelReg d
  match s with
  | .reg r => return (mn, [.reg d, .reg (← intelReg r)])
  | .imm _ => throw s!"{mn} from an immediate has no NASM form"

/-- The lexical form of a bit test. -/
def btSyntax (mn d : String) (b : JOperand) : Except String (String × List Operand) := do
  let d ← intelReg d
  match b with
  | .reg r => return (mn, [.reg d, .reg (← intelReg r)])
  | .imm v => return (mn, [.reg d, .imm v])

/-- The lexical instruction of a `JInstr 64`: the inverse of `toJInstr` on its
    image. Constructors and operand forms outside that image are errors. -/
def toSyntax : JInstr 64 → Except String (String × List Operand)
  | .mov d src => do
      let d ← intelReg d
      match src with
      | .reg s => return ("mov", [.reg d, .reg (← intelReg s)])
      | .imm v => return ("mov", [.reg d, immOperand v])
  | .add d s => aluSyntax "add" d s
  | .sub d s => aluSyntax "sub" d s
  | .adc d s => aluSyntax "adc" d s
  | .sbb d s => aluSyntax "sbb" d s
  | .and_ d s => aluSyntax "and" d s
  | .or_ d s => aluSyntax "or" d s
  | .xor_ d s => aluSyntax "xor" d s
  | .cmp d s => aluSyntax "cmp" d s
  | .test d s => aluSyntax "test" d s
  | .imul d (.reg s) => do return ("imul", [.reg (← intelReg d), .reg (← intelReg s)])
  | .imul d (.imm v) => do
      let d ← intelReg d
      return ("imul", [.reg d, .reg d, immOperand v])
  | .neg d => do return ("neg", [.reg (← intelReg d)])
  | .not_ d => do return ("not", [.reg (← intelReg d)])
  | .andn d a b => do
      return ("andn", [.reg (← intelReg d), .reg (← intelReg a), .reg (← intelReg b)])
  | .shlx d a c => do
      return ("shlx", [.reg (← intelReg d), .reg (← intelReg a), .reg (← intelReg c)])
  | .shrx d a c => do
      return ("shrx", [.reg (← intelReg d), .reg (← intelReg a), .reg (← intelReg c)])
  | .sarx d a c => do
      return ("sarx", [.reg (← intelReg d), .reg (← intelReg a), .reg (← intelReg c)])
  | .rorx d a (.imm v) => do return ("rorx", [.reg (← intelReg d), .reg (← intelReg a), .imm v])
  | .rorx _ _ (.reg _) => throw "rorx with a register count has no NASM form"
  | .shl d a => shiftSyntax "shl" d a
  | .shr d a => shiftSyntax "shr" d a
  | .sar d a => shiftSyntax "sar" d a
  | .rol d a => shiftSyntax "rol" d a
  | .ror d a => shiftSyntax "ror" d a
  | .rcl d a => shiftSyntax "rcl" d a
  | .rcr d a => shiftSyntax "rcr" d a
  | .shld d s a => dshiftSyntax "shld" d s a
  | .shrd d s a => dshiftSyntax "shrd" d s a
  | .cmove d s => cmovSyntax "cmove" d s
  | .cmovne d s => cmovSyntax "cmovne" d s
  | .cmovb d s => cmovSyntax "cmovb" d s
  | .cmovcc c d s => cmovSyntax ("cmov" ++ condName c) d s
  | .setcc c d => do return ("set" ++ condName c, [.subreg (← intelSubReg d 8)])
  | .testN sz a b => do
      if sz = 64 then aluSyntax "test" a b
      else if sz = 8 ∨ sz = 16 ∨ sz = 32 then
        let an ← intelSubReg a sz
        match b with
        | .reg r => return ("test", [.subreg an, .subreg (← intelSubReg r sz)])
        | .imm v => return ("test", [.subreg an, .imm v])
      else throw s!"test at width {sz} has no NASM form"
  | .bt a b => btSyntax "bt" a b
  | .btr d b => btSyntax "btr" d b
  | .bts d b => btSyntax "bts" d b
  | .inc d => do return ("inc", [.reg (← intelReg d)])
  | .dec d => do return ("dec", [.reg (← intelReg d)])
  | .clc => return ("clc", [])
  | .stc => return ("stc", [])
  | .xchg a b => do return ("xchg", [.reg (← intelReg a), .reg (← intelReg b)])
  | .imulri d s imm => do
      return ("imul", [.reg (← intelReg d), .reg (← intelReg s), immOperand imm])
  | .mul hi lo s => do
      unless hi = "%rdx" ∧ lo = "%rax" do
        throw "mul with destinations other than rdx:rax has no NASM form"
      return ("mul", [.reg (← intelReg s)])
  | .imulWide hi lo s => do
      unless hi = "%rdx" ∧ lo = "%rax" do
        throw "one-operand imul with destinations other than rdx:rax has no NASM form"
      return ("imul", [.reg (← intelReg s)])
  | .lea d b i sc off => do
      let d ← intelReg d
      let bn ← intelReg b
      if sc = 0 then
        if i = b then return ("lea", [.reg d, memOp bn none off])
        else throw "lea with scale 0 and an index register has no NASM form"
      else
        let iN ← intelReg i
        return ("lea", [.reg d, memOp bn (some (iN, sc)) off])
  | .mulx hi lo a b => do
      unless a matches .reg "%rdx" do throw "mulx with an implicit source other than rdx"
      let hN ← intelReg hi
      let lN ← intelReg lo
      match b with
      | .reg s => return ("mulx", [.reg hN, .reg lN, .reg (← intelReg s)])
      | .imm _ => throw "mulx with an immediate source has no NASM form"
  | .mulxMem hi lo a b off => do
      unless a matches .reg "%rdx" do throw "mulx with an implicit source other than rdx"
      let hN ← intelReg hi
      let lN ← intelReg lo
      let bN ← intelReg b
      return ("mulx", [.reg hN, .reg lN, memOp bN none off])
  | .adcx d (.reg s) => do return ("adcx", [.reg (← intelReg d), .reg (← intelReg s)])
  | .adox d (.reg s) => do return ("adox", [.reg (← intelReg d), .reg (← intelReg s)])
  | .adcx _ (.imm _) => throw "adcx with an immediate source has no NASM form"
  | .adox _ (.imm _) => throw "adox with an immediate source has no NASM form"
  | .loadMem d b off => do
      let dN ← intelReg d
      let bN ← intelReg b
      return ("mov", [.reg dN, memOp bN none off])
  | .storeMem b off (.reg s) => do
      let bN ← intelReg b
      let sN ← intelReg s
      return ("mov", [memOp bN none off, .reg sN])
  | .storeMem b off (.imm v) => do
      let bN ← intelReg b
      return ("mov", [.mem { size := some "qword", base := bN, idx := none, disp := off },
        immOperand v])
  | .loadMemIdx d b i sc => do
      let dN ← intelReg d
      let bN ← intelReg b
      let iN ← intelReg i
      return ("mov", [.reg dN, memOp bN (some (iN, sc)) 0])
  | .storeMemIdx b i sc (.reg s) => do
      let bN ← intelReg b
      let iN ← intelReg i
      let sN ← intelReg s
      return ("mov", [memOp bN (some (iN, sc)) 0, .reg sN])
  | .storeMemIdx _ _ _ (.imm _) => throw "indexed store of an immediate is outside the parser image"
  | .setc _ => throw "setc (SETB then MOVZX) is two NASM instructions"
  | .movzx d sw s => do
      if sw = 8 ∨ sw = 16 then
        return ("movzx", [.reg (← intelReg d), .subreg (← intelSubReg s sw)])
      else throw s!"movzx from width {sw} has no NASM form"
  | .movsx d sw s => do
      if sw = 8 ∨ sw = 16 then
        return ("movsx", [.reg (← intelReg d), .subreg (← intelSubReg s sw)])
      else if sw = 32 then
        return ("movsxd", [.reg (← intelReg d), .subreg (← intelSubReg s 32)])
      else throw s!"movsx from width {sw} has no NASM form"
  | .loadSym _ _ => throw "RIP-relative symbol load is outside the parser image"
  | .addMem d b off => do
      let dN ← intelReg d
      let bN ← intelReg b
      return ("add", [.reg dN, memOp bN none off])
  | .addToMem b off (.reg s) => do
      let bN ← intelReg b
      let sN ← intelReg s
      return ("add", [memOp bN none off, .reg sN])
  | .addToMem b off (.imm v) => do
      let bN ← intelReg b
      return ("add", [.mem { size := some "qword", base := bN, idx := none, disp := off },
        immOperand v])
  | .adcxMem d b off => do
      let dN ← intelReg d
      let bN ← intelReg b
      return ("adcx", [.reg dN, memOp bN none off])
  | .adoxMem d b off => do
      let dN ← intelReg d
      let bN ← intelReg b
      return ("adox", [.reg dN, memOp bN none off])
  | .imulMem d b off => do
      let dN ← intelReg d
      let bN ← intelReg b
      return ("imul", [.reg dN, memOp bN none off])
  | .imulriMem d b off imm => do
      let dN ← intelReg d
      let bN ← intelReg b
      return ("imul", [.reg dN, memOp bN none off, immOperand imm])
  | .bzhi d s i => do
      return ("bzhi", [.reg (← intelReg d), .reg (← intelReg s), .reg (← intelReg i)])

/-! ## 4. Whole-text parse, print and canonicalisation -/

/-- One source line to its instruction, if it has one. -/
def parseLine (ln : String) : Except String (Option (JInstr 64)) := do
  match ← lexLine ln with
  | .instr mn ops => some <$> toJInstr mn ops
  | _ => pure none

/-- The source lines of a text, numbered from 1, with carriage returns removed. -/
def numberedLines (src : String) : List (Nat × String) :=
  let ls := (src.splitOn "\n").map (fun l => String.ofList (l.toList.filter (· ≠ '\r')))
  (List.range ls.length).zip ls |>.map (fun (i, l) => (i + 1, l))

/-- Parse NASM text into a `JInstr 64` block. A `ret` with no operand is
    accepted as the last instruction and ends the block; the error names the
    first line that does not lex, whose instruction has no `JInstr`
    constructor, or that follows a `ret`. -/
def parseNasm (src : String) : Except String (List (JInstr 64)) := do
  let mut out : Array (JInstr 64) := #[]
  let mut retLine : Option Nat := none
  for (n, ln) in numberedLines src do
    match lexLine ln with
    | .error e => throw s!"line {n}: {e}"
    | .ok (.instr mn ops) =>
        if let some r := retLine then
          throw s!"line {n}: {printInstrSyntax mn ops}: instruction after the ret on line {r}"
        if isRet mn ops then retLine := some n
        else
          match toJInstr mn ops with
          | .ok i => out := out.push i
          | .error e => throw s!"line {n}: {printInstrSyntax mn ops}: {e}"
    | .ok _ => pure ()
  return out.toList

/-- Join canonical lines, one per line with a final newline. -/
def joinLines (ls : List String) : String :=
  String.join (ls.map (· ++ "\n"))

/-- The canonical text of a `JInstr 64`. -/
def printInstr (i : JInstr 64) : Except String String := do
  let (mn, ops) ← toSyntax i
  return printInstrSyntax mn ops

/-- Print a `JInstr 64` block as canonical NASM text. -/
def printNasm (is : List (JInstr 64)) : Except String String := do
  return joinLines (← is.mapM printInstr)

/-- The canonical text of NASM source at the lexical level: instruction lines
    only, without the `JInstr` mapping, and without the final `ret`, under the
    rule of `parseNasm` (an instruction after a `ret` is an error). -/
def canonicalNasm (src : String) : Except String String := do
  let mut out : Array String := #[]
  let mut retLine : Option Nat := none
  for (n, ln) in numberedLines src do
    match lexLine ln with
    | .error e => throw s!"line {n}: {e}"
    | .ok (.instr mn ops) =>
        if let some r := retLine then
          throw s!"line {n}: {printInstrSyntax mn ops}: instruction after the ret on line {r}"
        if isRet mn ops then retLine := some n
        else out := out.push (printInstrSyntax mn ops)
    | .ok _ => pure ()
  return joinLines out.toList

end CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParse
