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
* Operands: the sixteen 64-bit general-purpose registers, non-negative
  immediates in decimal or `0x` hexadecimal, and memory operands
  `[ base ± disp ]`, `[ base + idx ]`, `[ base + idx*scale ]` with an optional
  `qword` size. Mnemonics and register names are case-insensitive.
* Register names in the produced `JInstr` carry the AT&T `%` prefix (`%rax`),
  the spelling `AsmPrinter.regOf` and the ascent modules use.

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
displacement only when it is nonzero. `canonicalNasm` produces this form from
the source text at the lexical level, without the `JInstr` mapping, and
`NasmParseKat` checks `printNasm ∘ parseNasm` against it.

## Coverage of `fiat_curve25519_carry_mul.asm`

The file has 168 instructions. The table lists, for each mnemonic and operand
form of the file, the `JInstr` constructor and the flags its `evalInstr` arm
reads and writes, or the gap.

| Mnemonic, form (count) | `JInstr` | Flags read / written |
|---|---|---|
| `mov r, r` / `mov r, imm` | `mov` | none / none |
| `mov r, [b + d]` | `loadMem` | none / none |
| `mov [b + d], r` | `storeMem` | none / none |
| `mulx hi, lo, r` | `mulx hi lo (.reg "%rdx") (.reg r)` | none / none |
| `mulx hi, lo, [b + d]` | `mulxMem hi lo (.reg "%rdx") b d` | none / none |
| `adcx r, r` (13 of 17) | `adcx` | CF / CF only |
| `adcx r, [b + d]` (4) | gap | |
| `adox r, r` (12 of 16) | `adox` | OF / OF only |
| `adox r, [b + d]` (4) | gap | |
| `add r, r` / `add r, imm` (10 of 12) | `add` | none / OF CF SF PF ZF |
| `add r, [b + d]` (2) | gap | |
| `adc r, imm` (4) | `adc` | CF / OF CF SF PF ZF |
| `xor r, r` (5) | `xor_` | none / OF = CF = 0, SF PF ZF |
| `sub r, imm` (1) | `sub` | none / OF CF SF PF ZF |
| `shr r, imm` (2) | `shr` | none / `x86_SHR` flags |
| `lea r, [b + i]` (3) | `lea r b i 1 0` | none / none |
| `imul r, r', imm` (1) and `imul r, [b + d], imm` (4) | gap | |
| `bzhi` (7) | gap | |
| `shrd r, r', imm` (5) | gap | |
| `xchg r, r'` (1) | gap | |
| `test al, al` (1) | gap | |
| `ret` (1) | gap | |

The constructors and `evalInstr` arms that close the gaps:

* `imul r, src, imm`: `imulri (dst src : String) (imm : Int)` with
  `s.writeB5W dst (x86_IMULt (s.get src) (BitVec.ofInt 64 imm))`
  (`Ox86_IMULri_instr`), and a memory-source form
  `imulriMem (dst base : String) (off imm : Int)` reading `s.load base off`.
  `JInstr.imul d (.imm v)` is the case `src = dst` and is what the parser
  produces for `imul d, d, imm`.
* `adcx`, `adox`, `add` with a memory source: `adcxMem`, `adoxMem`, `addMem`
  `(dst base : String) (off : Int)`, each the register arm with `src.eval s`
  replaced by `s.load base off`; alternatively a memory case of `JOperand`.
* `bzhi dst, src, idx`: `bzhi (dst src idx : String)` with
  `n := (s.get idx).toNat % 256`, word `if n < 64 then src &&& (2^n - 1) else
  src`, `ZF`/`SF` from the word, `CF := decide (63 < n)`, `OF := false`, `PF`
  undefined, written with `writeB5W`. The cleared `OF` is read by the `adox` on
  lines 98 and 136 of the file.
* `shrd dst, src, imm`: `shrd (dst src : String) (cnt : JOperand)` with
  `x86_SHRD` shaped as `x86_SHR`: count `i` masked to six bits, `rflags_None`
  for `i = 0`, otherwise word `(dst >>> i) ||| (src <<< (64 - i))`,
  `CF := lsb (dst >>> (i - 1))`, `OF` defined only for `i = 1`
  (`msb word ≠ msb dst`), `SF`/`PF`/`ZF` from the word (`Ox86_SHRD_instr`).
* `xchg a, b`: `xchg (a b : String)` writing `a := s.get b` and `b := s.get a`
  and no flag.
* `test al, al`: a byte-width test `test8 (a b : String)` writing the five
  flags of `x86_TEST` on the low bytes (`OF = CF = false`, `SF` from bit 7, `ZF`
  and `PF` from the byte). The cleared `CF` and `OF` are read by the `adox` and
  `adcx` on lines 53 to 56.
* `ret`: no constructor of a straight-line block expresses a return. The
  choices are a parser that accepts `ret` only as the last instruction and
  returns the body, or a control-flow terminator in the block type.

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

/-- The 8-, 16- and 32-bit general-purpose register names, in Intel spelling. -/
def subRegNames : List String :=
  ["al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil", "ah", "ch", "dh", "bh",
   "ax", "cx", "dx", "bx", "sp", "bp", "si", "di",
   "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi"] ++
  (List.range 8).flatMap (fun i =>
    let n := s!"r{i + 8}"
    [n ++ "b", n ++ "w", n ++ "d"])

/-- A memory operand `size [ base + idx*scale ± disp ]` as written. The base and
    index are Intel register names without prefix. -/
structure MemRef where
  size : Option String
  base : String
  idx : Option (String × Nat)
  disp : Int

/-- An operand as written: a 64-bit register, a narrower register, a
    non-negative immediate, or a memory operand. -/
inductive Operand where
  | reg (r : String)
  | subreg (r : String)
  | imm (v : Nat)
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
  else if cs.head? == some '-' then throw s!"negative immediate {s}"
  else match parseNum? cs with
    | some v => pure (.imm v)
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

/-- Lex one source line. Comments run from `;` to the end of the line. -/
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
  return .instr (String.ofList word) ops

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
  | .mem m => printMem m

/-- The canonical text of an instruction. -/
def printInstrSyntax (mn : String) (ops : List Operand) : String :=
  if ops.isEmpty then mn else mn ++ " " ++ ", ".intercalate (ops.map printOperand)

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

/-- The shift and rotate mnemonics taking an immediate count. -/
def shiftOf? : String → Option (String → JOperand → JInstr 64)
  | "shl" => some .shl
  | "shr" => some .shr
  | "sar" => some .sar
  | "rol" => some .rol
  | "ror" => some .ror
  | _ => none

/-- The conditional moves with a `JInstr` constructor. -/
def cmovOf? : String → Option (String → JOperand → JInstr 64)
  | "cmove" => some .cmove
  | "cmovne" => some .cmovne
  | "cmovb" => some .cmovb
  | _ => none

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
  for o in ops do
    if let .subreg r := o then
      throw s!"{mn} on the sub-64-bit register {r}: JInstr registers are 64-bit"
  if let some f := aluOf? mn then
    match ops with
    | [.reg d, .reg s] => return f (jreg d) (.reg (jreg s))
    | [.reg d, .imm v] =>
        if v < 2 ^ 31 then return f (jreg d) (.imm v)
        else throw s!"{mn} immediate {hex v} is not a sign-extended imm32"
    | [.reg _, .mem _] => throw s!"{mn} with a memory source operand: no JInstr constructor"
    | [.mem _, _] => throw s!"{mn} with a memory destination operand: no JInstr constructor"
    | _ => throw s!"{mn}: unsupported operand form"
  if let some f := shiftOf? mn then
    match ops with
    | [.reg d, .imm v] =>
        if v < 256 then return f (jreg d) (.imm v)
        else throw s!"{mn} count {hex v} is not an imm8"
    | _ => throw s!"{mn}: only the register, imm8 form has a JInstr constructor"
  if let some f := cmovOf? mn then
    match ops with
    | [.reg d, .reg s] => return f (jreg d) (.reg (jreg s))
    | _ => throw s!"{mn}: only the register, register form has a JInstr constructor"
  match mn, ops with
  | "mov", [.reg d, .reg s] => return .mov (jreg d) (.reg (jreg s))
  | "mov", [.reg d, .imm v] =>
      if v < 2 ^ 64 then return .mov (jreg d) (.imm v)
      else throw s!"mov immediate {hex v} exceeds 64 bits"
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
  | "mov", [.mem m, .imm v] =>
      unless m.size == some "qword" do
        throw "mov of an immediate to memory needs the qword size"
      unless v < 2 ^ 31 do throw s!"mov immediate {hex v} is not a sign-extended imm32"
      let (b, off) ← plainMem m
      return .storeMem (jreg b) off (.imm v)
  | "imul", [.reg d, .reg s] => return .imul (jreg d) (.reg (jreg s))
  | "imul", [.reg d, .reg s, .imm v] =>
      if s ≠ d then
        throw "imul with three operands and source register different from the \
          destination: no JInstr constructor (JInstr.imul is dst := dst * src)"
      else if v < 2 ^ 31 then return .imul (jreg d) (.imm v)
      else throw s!"imul immediate {hex v} is not a sign-extended imm32"
  | "imul", [.reg _, .mem _, .imm _] =>
      throw "imul with three operands and a memory source: no JInstr constructor"
  | "neg", [.reg d] => return .neg (jreg d)
  | "not", [.reg d] => return .not_ (jreg d)
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
  | "adcx", [.reg _, .mem _] =>
      throw "adcx with a memory source operand: no JInstr constructor"
  | "adox", [.reg _, .mem _] =>
      throw "adox with a memory source operand: no JInstr constructor"
  | "bzhi", _ => throw "bzhi: no JInstr constructor"
  | "shrd", _ => throw "shrd: no JInstr constructor"
  | "shld", _ => throw "shld: no JInstr constructor"
  | "xchg", _ => throw "xchg: no JInstr constructor"
  | "ret", _ => throw "ret: a straight-line JInstr block has no return"
  | _, _ => throw s!"{mn} with {ops.length} operands: no JInstr constructor"

/-- A memory operand without size keyword. -/
def memOp (base : String) (idx : Option (String × Nat)) (disp : Int) : Operand :=
  .mem { size := none, base := base, idx := idx, disp := disp }

/-- The lexical form of a two-operand ALU instruction. -/
def aluSyntax (mn d : String) (s : JOperand) : Except String (String × List Operand) := do
  let d ← intelReg d
  match s with
  | .reg r => return (mn, [.reg d, .reg (← intelReg r)])
  | .imm v => return (mn, [.reg d, .imm v])

/-- The lexical form of a shift or rotate by an immediate. -/
def shiftSyntax (mn d : String) (a : JOperand) : Except String (String × List Operand) := do
  let d ← intelReg d
  match a with
  | .imm v => return (mn, [.reg d, .imm v])
  | .reg _ => throw s!"{mn} by a 64-bit register has no NASM form"

/-- The lexical form of a conditional move from a register. -/
def cmovSyntax (mn d : String) (s : JOperand) : Except String (String × List Operand) := do
  let d ← intelReg d
  match s with
  | .reg r => return (mn, [.reg d, .reg (← intelReg r)])
  | .imm _ => throw s!"{mn} from an immediate has no NASM form"

/-- The lexical instruction of a `JInstr 64`: the inverse of `toJInstr` on its
    image. Constructors and operand forms outside that image are errors. -/
def toSyntax : JInstr 64 → Except String (String × List Operand)
  | .mov d src => do
      let d ← intelReg d
      match src with
      | .reg s => return ("mov", [.reg d, .reg (← intelReg s)])
      | .imm v => return ("mov", [.reg d, .imm v])
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
      return ("imul", [.reg d, .reg d, .imm v])
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
  | .cmove d s => cmovSyntax "cmove" d s
  | .cmovne d s => cmovSyntax "cmovne" d s
  | .cmovb d s => cmovSyntax "cmovb" d s
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
        .imm v])
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
  | .movzx _ _ _ => throw "movzx reads a sub-64-bit register"
  | .movsx _ _ _ => throw "movsx reads a sub-64-bit register"
  | .loadSym _ _ => throw "RIP-relative symbol load is outside the parser image"

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

/-- Parse NASM text into a `JInstr 64` block. The error names the first line
    that does not lex or whose instruction has no `JInstr` constructor. -/
def parseNasm (src : String) : Except String (List (JInstr 64)) := do
  let mut out : Array (JInstr 64) := #[]
  for (n, ln) in numberedLines src do
    match lexLine ln with
    | .error e => throw s!"line {n}: {e}"
    | .ok (.instr mn ops) =>
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
    only, without the `JInstr` mapping. -/
def canonicalNasm (src : String) : Except String String := do
  let mut out : Array String := #[]
  for (n, ln) in numberedLines src do
    match lexLine ln with
    | .error e => throw s!"line {n}: {e}"
    | .ok (.instr mn ops) => out := out.push (printInstrSyntax mn ops)
    | .ok _ => pure ()
  return joinLines out.toList

end CatCrypt.Crypto.SecureCompilation.X86Backend.NasmParse
