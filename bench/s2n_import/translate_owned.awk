# Translate one function of an x86-64 AT&T file printed by CatCrypt's owned
# backend (`AsmPrinter.renderLeafFn` / `renderSysVLeafFn`,
# `LprogAsmPrinter`) into the elements of a Lean `List (JInstr 64)`, or, when
# the function contains `call`, a `List CallSeg`.
#
# Input: the `.s` file itself (no preprocessor).
# Variables (set with -v):
#   sym      the function label
#   summary  a path; a summary of the translation is written there
#   prefix   the name prefix of the segment definitions
#   block    the name of the block definition
#   partprefix  the name prefix of the part definitions
#   maxseg   the largest segment, in instructions (default 32)
#
# Output on stdout: the segment definitions and the block definition.
#
# Any statement outside the accepted shapes stops the translation: the program
# prints `file:line: message` on stderr and exits 1.  The accepted shapes are
# listed in README.md (section "Importing the owned backend's output").

BEGIN {
    phase = "pre"          # pre -> entry -> body -> exit -> post
    cur_line = 0
    n_out = 0
    n_push = 0
    n_pop = 0
    n_call = 0
    endbr = 0
    failed = 0
    frame_n = ""           # the size of the dropped %rsp adjustment
    saverun = 1            # still inside the entry run of stores to %rsp
    n_save = 0
    pend = 0               # a `setc` waiting for its `movzbq`
    ofundef = 0            # OF/SF/PF undefined (after `btq`), per the SDM
    TWO31 = "2147483648"
    TWO32 = "4294967296"
    TWO64 = "18446744073709551616"
    split("rax rbx rcx rdx rsi rdi rbp r8 r9 r10 r11 r12 r13 r14 r15", r64list, " ")
    for (i in r64list) R64["%" r64list[i]] = 1
    R32["%eax"] = "%rax"; R32["%ebx"] = "%rbx"; R32["%ecx"] = "%rcx"
    R32["%edx"] = "%rdx"; R32["%esi"] = "%rsi"; R32["%edi"] = "%rdi"
    R32["%ebp"] = "%rbp"
    for (i = 8; i <= 15; i++) R32["%r" i "d"] = "%r" i
    R8["%al"] = "%rax"; R8["%bl"] = "%rbx"; R8["%cl"] = "%rcx"; R8["%dl"] = "%rdx"
    R8["%sil"] = "%rsi"; R8["%dil"] = "%rdi"; R8["%bpl"] = "%rbp"
    for (i = 8; i <= 15; i++) R8["%r" i "b"] = "%r" i
    CALLEE["%rbx"] = 1; CALLEE["%rbp"] = 1; CALLEE["%r12"] = 1
    CALLEE["%r13"] = 1; CALLEE["%r14"] = 1; CALLEE["%r15"] = 1
    SCALE["1"] = 1; SCALE["2"] = 1; SCALE["4"] = 1; SCALE["8"] = 1
}

function fail(msg) {
    printf("%s:%d: %s\n", FILENAME, cur_line, msg) > "/dev/stderr"
    failed = 1
    exit 1
}

function trim(s) {
    sub(/^[ \t]+/, "", s)
    sub(/[ \t]+$/, "", s)
    return s
}

# ---- decimal-string arithmetic (awk numbers are doubles) -------------------

function strip0(s) {
    sub(/^0+/, "", s)
    return (s == "") ? "0" : s
}

function dec_muladd(a, m, c,    i, x, r) {
    r = ""
    for (i = length(a); i >= 1; i--) {
        x = substr(a, i, 1) * m + c
        r = (x % 10) r
        c = int(x / 10)
    }
    while (c > 0) {
        r = (c % 10) r
        c = int(c / 10)
    }
    return strip0(r)
}

function hex2dec(h,    i, d, r) {
    r = "0"
    h = tolower(h)
    for (i = 1; i <= length(h); i++) {
        d = index("0123456789abcdef", substr(h, i, 1)) - 1
        if (d < 0) fail("not a hexadecimal digit in `" h "`")
        r = dec_muladd(r, 16, d)
    }
    return r
}

function declt(a, b) {
    if (length(a) != length(b)) return length(a) < length(b)
    return a < b
}

# ---- operands --------------------------------------------------------------

# A 64-bit general register other than %rsp, or "".
function reg64(t) {
    return (t in R64) ? t : ""
}

function reg32(t) {
    return (t in R32) ? R32[t] : ""
}

function reg8(t) {
    return (t in R8) ? R8[t] : ""
}

function literal(t) {
    if (t ~ /^0[xX][0-9a-fA-F]+$/) return hex2dec(substr(t, 3))
    if (t ~ /^[0-9]+$/) return strip0(t)
    return ""
}

function imm(t,    v) {
    if (substr(t, 1, 1) != "$") return ""
    v = literal(substr(t, 2))
    if (v == "") fail("immediate `" t "` is not an unsigned decimal or hexadecimal literal")
    if (!declt(v, TWO64)) fail("immediate `" t "` does not fit in 64 bits")
    return v
}

# A memory operand `disp(%base)` or `disp(%base, %index, scale)`.  Sets
# MKIND (1 = base only, 2 = base and index), MBASE, MIDX, MSCALE, MOFF (a Lean
# `Int` literal) and MOFFZ (1 when the displacement is 0), and returns MKIND,
# or 0 when `t` is not a memory operand.  The base may be %rsp; the index may
# not.
function mem(t,    p, d, inner, parts, n, b, neg, v) {
    if (t !~ /\)$/) return 0
    p = index(t, "(")
    if (p == 0) return 0
    d = substr(t, 1, p - 1)
    inner = substr(t, p + 1, length(t) - p - 1)
    n = split(inner, parts, ",")
    b = trim(parts[1])
    if (reg64(b) == "" && b != "%rsp") fail("memory operand `" t "` has a base that is not a 64-bit general register")
    MBASE = b
    if (n == 1) MKIND = 1
    else if (n == 3) {
        MIDX = trim(parts[2]); MSCALE = trim(parts[3])
        if (reg64(MIDX) == "") fail("memory operand `" t "` has an index that is not a 64-bit general register other than %rsp")
        if (!(MSCALE in SCALE)) fail("memory operand `" t "` has a scale other than 1, 2, 4, 8")
        MKIND = 2
    } else fail("memory operand `" t "` has a shape other than `disp(%b)` or `disp(%b, %i, s)`")
    neg = 0
    if (substr(d, 1, 1) == "-") { neg = 1; d = substr(d, 2) }
    if (d == "") v = "0"
    else {
        v = literal(d)
        if (v == "") fail("memory operand `" t "` has a displacement that is not a literal")
    }
    if (!declt(v, TWO31)) fail("memory operand `" t "` has a displacement outside the signed 32-bit range")
    MOFFZ = (v == "0")
    MOFF = (neg && v != "0") ? "(-" v ")" : v
    MOFFNUM = (neg ? -1 : 1) * (v + 0)
    return MKIND
}

function q(s) {
    return "\"" s "\""
}

function split_operands(s,    i, c, depth, cur, n) {
    delete OPS
    n = 0
    depth = 0
    cur = ""
    s = trim(s)
    if (s == "") return 0
    for (i = 1; i <= length(s); i++) {
        c = substr(s, i, 1)
        if (c == "(") depth++
        if (c == ")") depth--
        if (c == "," && depth == 0) {
            OPS[++n] = trim(cur)
            cur = ""
        } else cur = cur c
    }
    OPS[++n] = trim(cur)
    return n
}

# ---- output ----------------------------------------------------------------

# Record one translated instruction.  `writes` lists the registers it writes,
# `bases` the memory base registers it reads or writes through, `kind` marks
# frame stores/loads for the segmenting.
function emit(lean, writes, bases, kind, text, line,    arr, n, i, b) {
    n_out++
    OUT[n_out] = lean
    SRC[n_out] = text
    LOC[n_out] = line
    KIND[n_out] = kind
    CUTAFTER[n_out] = 0
    n = split(bases, arr, " ")
    for (i = 1; i <= n; i++) {
        b = arr[i]
        if (b == "") continue
        if (REWRITTEN[b]) REBASED[b] = 1
        if (b in LEAFROM) ALIASED[b] = LEAFROM[b]
        MEMUSED[b] = 1
    }
    n = split(writes, arr, " ")
    for (i = 1; i <= n; i++) {
        if (arr[i] == "") continue
        if (MEMUSED[arr[i]]) REWRITTEN[arr[i]] = 1
        delete LEAFROM[arr[i]]
    }
    if (kind != "save") saverun = 0
}

function count(mn) {
    MNCOUNT[mn]++
}

# OF/SF/PF are undefined after `btq` (Intel SDM, BT); the model keeps their old
# values.  Refuse any accepted instruction that reads them in that state.
function reads_of(mn) {
    if (ofundef) fail("`" mn "` reads OF, which is undefined after the preceding `btq`")
}

function flush_setc() {
    if (!pend) return
    emit(".setcc .b " q(PEND_R), PEND_R, "", "", PEND_TEXT, PEND_LINE)
    SETCC++
    pend = 0
}

function translate(mn, rest, text,    n, s, d, v, lo, hi, r, k) {
    n = split_operands(rest)

    # `setc %r8; movzbq %r8, %r64` on one register is the model's `setc` arm
    # (`evalInstr_setc_eq_setcc_movzx`).
    if (pend) {
        if (mn == "movzbq" && n == 2 && OPS[1] == PEND_8 && OPS[2] == PEND_R) {
            emit(".setc " q(PEND_R), PEND_R, "", "", PEND_TEXT "; " text, PEND_LINE)
            SETC_FUSED++
            pend = 0
            return
        }
        flush_setc()
    }

    if (mn == "setc" || mn == "setb") {
        if (n != 1 || (r = reg8(OPS[1])) == "") fail("`" mn "` accepted only on a low-byte register: " text)
        pend = 1; PEND_R = r; PEND_8 = OPS[1]; PEND_TEXT = text; PEND_LINE = cur_line
        return
    }

    if (mn == "movzbq") {
        if (n != 2 || (s = reg8(OPS[1])) == "" || (d = reg64(OPS[2])) == "")
            fail("`movzbq` accepted only from a low-byte register to a 64-bit register: " text)
        emit(".movzx " q(d) " 8 " q(s), d, "", "", text, cur_line); return
    }

    if (mn == "movq") {
        if (n != 2) fail("`movq` with " n " operands")
        d = reg64(OPS[2])
        if (d != "") {
            if ((s = reg64(OPS[1])) != "") { emit(".mov " q(d) " (.reg " q(s) ")", d, "", "", text, cur_line); return }
            if ((v = imm(OPS[1])) != "")   { emit(".mov " q(d) " (.imm " v ")", d, "", "", text, cur_line); return }
            k = mem(OPS[1])
            if (k == 1) {
                emit(".loadMem " q(d) " " q(MBASE) " " MOFF, d, MBASE, (MBASE == "%rsp") ? "rspload" : "", text, cur_line)
                LOADOFF[n_out] = MOFFNUM
                LOADREG[n_out] = d
                return
            }
            if (k == 2) {
                if (!MOFFZ) fail("indexed load with a nonzero displacement: " text)
                emit(".loadMemIdx " q(d) " " q(MBASE) " " q(MIDX) " " MSCALE, d, MBASE, "", text, cur_line); return
            }
        }
        k = mem(OPS[2])
        if (k && (s = reg64(OPS[1])) != "") {
            if (k == 1) {
                if (saverun && MBASE == "%rsp") {
                    n_save++
                    SAVEOFF[s] = MOFFNUM
                    emit(".storeMem " q(MBASE) " " MOFF " (.reg " q(s) ")", "", MBASE, "save", text, cur_line)
                } else
                    emit(".storeMem " q(MBASE) " " MOFF " (.reg " q(s) ")", "", MBASE, "", text, cur_line)
                return
            }
            if (!MOFFZ) fail("indexed store with a nonzero displacement: " text)
            emit(".storeMemIdx " q(MBASE) " " q(MIDX) " " MSCALE " (.reg " q(s) ")", "", MBASE, "", text, cur_line); return
        }
        fail("`movq` operand shape not accepted: " text)
    }

    if (mn == "movl") {
        # `movl $imm, %r32` writes the zero-extended immediate to the whole
        # register and no flag: a 64-bit move of the same value.
        if (n != 2) fail("`movl` with " n " operands")
        v = imm(OPS[1])
        if (v != "" && mem(OPS[2]))
            fail("`movl` into memory writes the low 4 bytes of a cell; JasminModel's memory is word-granular and has no 32-bit store: " text)
        d = reg32(OPS[2])
        if (d == "" || v == "") fail("`movl` accepted only as an immediate into a 32-bit register: " text)
        if (!declt(v, TWO32)) fail("`movl` immediate does not fit in 32 bits: " text)
        emit(".mov " q(d) " (.imm " v ")", d, "", "", text, cur_line)
        MOVL32++
        return
    }

    if (mn == "leaq") {
        if (n != 2) fail("`leaq` with " n " operands")
        d = reg64(OPS[2])
        k = mem(OPS[1])
        if (d == "" || !k) fail("`leaq` accepted only from an address to a 64-bit register other than %rsp: " text)
        # `lea d b b 0 off` computes b + b * 0 + off = b + off (`evalInstr`).
        if (k == 1) emit(".lea " q(d) " " q(MBASE) " " q(MBASE) " 0 " MOFF, d, "", "", text, cur_line)
        else emit(".lea " q(d) " " q(MBASE) " " q(MIDX) " " MSCALE " " MOFF, d, "", "", text, cur_line)
        LEA++
        LEAFROM[d] = MBASE
        return
    }

    if (mn == "addq" || mn == "subq" || mn == "adcq" || mn == "sbbq" || mn == "xorq" || mn == "andq" || mn == "orq") {
        if (n != 2) fail("`" mn "` with " n " operands")
        r = substr(mn, 1, length(mn) - 1)
        if (r == "xor" || r == "and" || r == "or") r = r "_"
        d = reg64(OPS[2])
        if (d == "") fail("`" mn "` destination is not a 64-bit general register other than %rsp: " text)
        ofundef = 0
        if ((s = reg64(OPS[1])) != "") { emit("." r " " q(d) " (.reg " q(s) ")", d, "", "", text, cur_line); return }
        if ((v = imm(OPS[1])) != "") {
            if (!declt(v, TWO31)) fail("`" mn "` immediate is outside the sign-extended 32-bit range: " text)
            emit("." r " " q(d) " (.imm " v ")", d, "", "", text, cur_line); return
        }
        if (mn == "addq" && mem(OPS[1]) == 1) { emit(".addMem " q(d) " " q(MBASE) " " MOFF, d, MBASE, "", text, cur_line); return }
        fail("`" mn "` operand shape not accepted: " text)
    }

    if (mn == "shlq" || mn == "shrq" || mn == "sarq") {
        if (n != 2) fail("`" mn "` with " n " operands")
        d = reg64(OPS[2])
        v = imm(OPS[1])
        if (d == "" || v == "") fail("`" mn "` needs an immediate count and a 64-bit register: " text)
        # A zero count leaves the flags unchanged on the processor, while
        # `x86_SHL`/`x86_SHR`/`x86_SAR` make them undefined.
        if (v == "0") fail("`" mn "` with count 0: " text)
        if (!declt(v, "64")) fail("`" mn "` count is 64 or more: " text)
        ofundef = 0
        emit("." substr(mn, 1, 3) " " q(d) " (.imm " v ")", d, "", "", text, cur_line); return
    }

    if (mn == "negq") {
        if (n != 1 || (d = reg64(OPS[1])) == "") fail("`negq` accepted only on a 64-bit register: " text)
        ofundef = 0
        emit(".neg " q(d), d, "", "", text, cur_line); return
    }

    if (mn == "imulq") {
        if (n == 2) {
            d = reg64(OPS[2]); s = reg64(OPS[1])
            if (d == "" || s == "") fail("two-operand `imulq` accepted only on 64-bit registers: " text)
            ofundef = 0
            emit(".imul " q(d) " (.reg " q(s) ")", d, "", "", text, cur_line); return
        }
        if (n == 3) {
            v = imm(OPS[1]); s = reg64(OPS[2]); d = reg64(OPS[3])
            if (v == "" || s == "" || d == "") fail("three-operand `imulq` accepted only as `imulq $imm, %src, %dst`: " text)
            if (!declt(v, TWO31)) fail("`imulq` immediate is outside the sign-extended 32-bit range: " text)
            ofundef = 0
            emit(".imulri " q(d) " " q(s) " " v, d, "", "", text, cur_line); return
        }
        fail("`imulq` with " n " operands")
    }

    if (mn == "adcx" || mn == "adcxq" || mn == "adox" || mn == "adoxq") {
        if (n != 2) fail("`" mn "` with " n " operands")
        r = substr(mn, 1, 4)
        if (r == "adox") { reads_of(mn); ofundef = 0 }
        d = reg64(OPS[2])
        if (d == "") fail("`" mn "` destination is not a 64-bit general register: " text)
        if ((s = reg64(OPS[1])) != "") { emit("." r " " q(d) " (.reg " q(s) ")", d, "", "", text, cur_line); return }
        if (mem(OPS[1]) == 1) { emit("." r "Mem " q(d) " " q(MBASE) " " MOFF, d, MBASE, "", text, cur_line); return }
        fail("`" mn "` operand shape not accepted: " text)
    }

    if (mn == "mulx" || mn == "mulxq") {
        # AT&T `mulx src2, lo, hi`; the first source is %rdx.
        if (n != 3) fail("`" mn "` with " n " operands")
        lo = reg64(OPS[2]); hi = reg64(OPS[3])
        if (lo == "" || hi == "") fail("`" mn "` destinations are not 64-bit general registers: " text)
        if (lo == hi) fail("`" mn "` with equal destinations: " text)
        if ((s = reg64(OPS[1])) != "") {
            emit(".mulx " q(hi) " " q(lo) " (.reg \"%rdx\") (.reg " q(s) ")", hi " " lo, "", "", text, cur_line); return
        }
        if (mem(OPS[1]) == 1) {
            emit(".mulxMem " q(hi) " " q(lo) " (.reg \"%rdx\") " q(MBASE) " " MOFF, hi " " lo, MBASE, "", text, cur_line); return
        }
        fail("`" mn "` source shape not accepted: " text)
    }

    if (mn == "btq") {
        if (n != 2) fail("`btq` with " n " operands")
        d = reg64(OPS[2]); v = imm(OPS[1])
        if (d == "" || v == "") fail("`btq` accepted only as `btq $k, %r64`: " text)
        if (!declt(v, "64")) fail("`btq` bit index is 64 or more: " text)
        ofundef = 1
        emit(".bt " q(d) " (.imm " v ")", "", "", "", text, cur_line); return
    }

    if (mn == "testq") {
        if (n != 2) fail("`testq` with " n " operands")
        d = reg64(OPS[2]); s = reg64(OPS[1])
        if (d == "" || s == "") fail("`testq` accepted only on two 64-bit registers: " text)
        ofundef = 0
        emit(".test " q(d) " (.reg " q(s) ")", "", "", "", text, cur_line); return
    }

    if (mn == "cmovnzq" || mn == "cmovneq" || mn == "cmovzq" || mn == "cmoveq" || mn == "cmovbq" || mn == "cmovcq") {
        if (n != 2) fail("`" mn "` with " n " operands")
        d = reg64(OPS[2]); s = reg64(OPS[1])
        if (d == "" || s == "") fail("`" mn "` operands are not 64-bit general registers: " text)
        r = (mn == "cmovnzq" || mn == "cmovneq") ? "cmovne" : ((mn == "cmovzq" || mn == "cmoveq") ? "cmove" : "cmovb")
        emit("." r " " q(d) " (.reg " q(s) ")", d, "", "", text, cur_line); return
    }

    fail("mnemonic or operand shape not accepted: " text)
}

# ---- driver ----------------------------------------------------------------

# Record a call after instruction n_out (0: before the first instruction).
# Several calls may follow one instruction; each after the first gets a
# segment with an empty body.
function end_run(callee, text,    k) {
    k = ++CALLN[n_out]
    CALLSYM[n_out, k] = callee
    CALLTXT[n_out, k] = text
    CALLLN[n_out, k] = cur_line
    if (n_out > 0) CUTAFTER[n_out] = 1
    saverun = 0
}

# One segment definition with an empty body, ended by call k after
# instruction j.
function print_empty_call(o, j, k) {
    printf("/-- Segment %d of the body: `call %s` with no instruction before it. -/\n", o, CALLSYM[j, k])
    printf("def %s : List CallSeg :=\n", segname(o))
    printf("  [ { body := []\n      callee := some %s } ]  -- l.%d `%s`\n\n", q(CALLSYM[j, k]), CALLLN[j, k], CALLTXT[j, k])
}

function statement(st,    mn, rest, p, v) {
    st = trim(st)
    if (st == "") return
    if (phase == "pre") {
        if (st == sym ":") phase = "entry"
        return
    }
    if (phase == "post") return

    if (substr(st, 1, 1) == ".") fail("directive inside the function: " st)
    if (st ~ /^[A-Za-z0-9_.$]+:/) fail("label inside the function: " st)

    p = match(st, /[ \t]/)
    if (p) { mn = substr(st, 1, p - 1); rest = trim(substr(st, p + 1)) }
    else { mn = st; rest = "" }
    split_operands(rest)

    if (phase == "entry") {
        if (mn == "endbr64" && rest == "") {
            if (n_push > 0 || endbr || frame_n != "") fail("CET landing pad after the first frame instruction")
            endbr = 1
            return
        }
        if (mn == "pushq") {
            if (frame_n != "") fail("`pushq` after the frame allocation")
            if (split_operands(rest) != 1 || !(OPS[1] in CALLEE)) fail("`pushq` of a register that is not callee-saved: " st)
            if (PUSHED[OPS[1]]) fail("`pushq` of " OPS[1] " twice")
            PUSHED[OPS[1]] = 1
            PUSH[++n_push] = OPS[1]
            return
        }
        if ((mn == "leaq" && OPS[2] == "%rsp" && OPS[1] ~ /^-[0-9]+\(%rsp\)$/) ||
            (mn == "subq" && OPS[2] == "%rsp" && OPS[1] ~ /^\$[0-9]+$/)) {
            v = (mn == "leaq") ? substr(OPS[1], 2, index(OPS[1], "(") - 2) : substr(OPS[1], 2)
            if (v + 0 <= 0) fail("frame allocation of size 0: " st)
            frame_n = v + 0
            FRAME_TEXT = mn " " rest
            return
        }
        phase = "body"
    }

    if (phase == "body") {
        if ((mn == "leaq" && OPS[2] == "%rsp" && OPS[1] ~ /^[0-9]+\(%rsp\)$/) ||
            (mn == "addq" && OPS[2] == "%rsp" && OPS[1] ~ /^\$[0-9]+$/)) {
            flush_setc()
            v = (mn == "leaq") ? substr(OPS[1], 1, index(OPS[1], "(") - 1) : substr(OPS[1], 2)
            if (frame_n == "" || v + 0 != frame_n) fail("frame release `" st "` does not match the allocation (" frame_n ")")
            FRAME_REL_TEXT = mn " " rest
            phase = "exit"
            return
        }
        if (mn == "popq" || mn == "ret" || mn == "retq") {
            flush_setc()
            if (frame_n != "") fail("`" mn "` before the frame release")
            phase = "exit"
        } else if (mn == "call" || mn == "callq") {
            flush_setc()
            if (split_operands(rest) != 1 || rest !~ /^[A-Za-z_][A-Za-z0-9_.$]*$/)
                fail("`call` accepted only to a symbol: " st)
            n_call++
            CALLEES[rest]++
            count("call")
            end_run(rest, "call " rest)
            ofundef = 0
            return
        } else {
            if ((OPS[1] == "%rsp" || OPS[2] == "%rsp" || OPS[3] == "%rsp") && mn != "leaq")
                fail("%rsp as a register operand inside the body: " st)
            if (mn == "leaq" && OPS[2] == "%rsp") fail("`leaq` into %rsp inside the body: " st)
            count(mn)
            translate(mn, rest, mn " " rest)
            return
        }
    }

    if (phase == "exit") {
        if (mn == "popq") {
            if (split_operands(rest) != 1) fail("`popq` shape not accepted: " st)
            n_pop++
            if (n_pop > n_push || OPS[1] != PUSH[n_push - n_pop + 1])
                fail("`popq " OPS[1] "` does not restore the frame in reverse push order")
            return
        }
        if ((mn == "retq" || mn == "ret") && rest == "") {
            if (n_pop != n_push) fail("return with " n_push - n_pop " saved registers not restored")
            RET_TEXT = mn
            phase = "post"
            return
        }
        fail("instruction after the frame release: " st)
    }
}

{
    cur_line = FNR
    line = $0
    p = index(line, "#")
    if (p) line = substr(line, 1, p - 1)
    statement(line)
}

function segname(s) {
    return sprintf("%s%0" segw "d", prefix, s)
}

END {
    if (failed) exit 1
    if (phase != "post") {
        printf("%s: the function `%s` was not found or does not end in a return (phase %s)\n", FILENAME, sym, phase) > "/dev/stderr"
        exit 1
    }
    if (n_out == 0 && n_call == 0) {
        printf("%s: the function `%s` has an empty body\n", FILENAME, sym) > "/dev/stderr"
        exit 1
    }
    if (maxseg == "") maxseg = 32
    callmode = (n_call > 0)

    # The trailing run of loads of callee-saved registers from %rsp, each from
    # the slot the entry run saved it to, is the frame restore.
    n_rest = 0
    for (i = n_out; i >= 1; i--) {
        if (KIND[i] != "rspload" || CUTAFTER[i]) break
        r = LOADREG[i]
        if (!(r in CALLEE) || !(r in SAVEOFF) || SAVEOFF[r] != LOADOFF[i] || SEENREST[r]) break
        SEENREST[r] = 1
        n_rest++
    }
    if (n_save > 0 && n_save < n_out) CUTAFTER[n_save] = 1
    if (n_rest > 0 && n_out - n_rest >= 1) CUTAFTER[n_out - n_rest] = 1

    # Segments: cut after a call, after the frame stores, before the frame
    # loads, and every `maxseg` instructions.  A call with no instruction
    # before it in its segment gets an empty segment.
    n_seg = 0
    used = 0
    SEGSTART[1] = 1
    for (i = 1; i <= n_out; i++) {
        if (used == 0) { n_seg++; SEGSTART[n_seg] = i }
        SEG[i] = n_seg
        used++
        if (CUTAFTER[i] || used >= maxseg) { SEGEND[n_seg] = i; used = 0 }
    }
    if (used > 0) SEGEND[n_seg] = n_out

    n_total = n_seg
    if (callmode) {
        n_total += CALLN[0]
        for (j = 1; j <= n_out; j++) if (CALLN[j] > 1) n_total += CALLN[j] - 1
    }
    segw = (n_total >= 100) ? 3 : 2

    # Segment definitions.  SEGN[o] and SEGC[o] count the instructions and
    # calls of output segment o.
    ty = callmode ? "List CallSeg" : "List (JInstr 64)"
    o = 0
    if (callmode) for (k = 1; k <= CALLN[0]; k++) { print_empty_call(++o, 0, k); SEGN[o] = 0; SEGC[o] = 1 }
    for (s = 1; s <= n_seg; s++) {
        i = SEGSTART[s]; j = SEGEND[s]
        c = (callmode && CALLN[j] > 0) ? CALLSYM[j, 1] : ""
        range = (LOC[i] == LOC[j]) ? "line " LOC[i] : "lines " LOC[i] "–" LOC[j]
        o++
        SEGN[o] = j - i + 1; SEGC[o] = (c != "")
        printf("/-- Segment %d of the body: the %d instruction%s from source %s%s. -/\n", o, j - i + 1, (j > i) ? "s" : "", range, (c != "") ? ",\n    then `call " c "`" : "")
        printf("def %s : %s :=\n", segname(o), ty)
        if (!callmode) {
            for (k = i; k <= j; k++)
                printf("  %s %s%s  -- l.%d `%s`\n", (k == i) ? "[" : " ", OUT[k], (k < j) ? "," : " ]", LOC[k], SRC[k])
            printf("\n")
        } else {
            printf("  [ { body :=\n")
            for (k = i; k <= j; k++)
                printf("        %s %s%s  -- l.%d `%s`\n", (k == i) ? "[" : " ", OUT[k], (k < j) ? "," : " ]", LOC[k], SRC[k])
            if (c != "") printf("      callee := some %s } ]  -- l.%d `%s`\n\n", q(c), CALLLN[j, 1], CALLTXT[j, 1])
            else printf("      callee := none } ]\n\n")
            for (k = 2; k <= CALLN[j]; k++) { print_empty_call(++o, j, k); SEGN[o] = 0; SEGC[o] = 1 }
        }
    }
    n_def = o

    # More than `partmax` segments are grouped into parts of at most
    # `partmax` segments, each with its own count lemmas; the block is the
    # concatenation of the parts.  A single sum over all segments exceeds the
    # default recursion depth of `rfl`.
    partmax = 16
    if (n_def > partmax) {
        n_part = int((n_def + partmax - 1) / partmax)
        pw = (n_part >= 100) ? 3 : 2
        for (p = 1; p <= n_part; p++) {
            a = (p - 1) * partmax + 1; b = p * partmax; if (b > n_def) b = n_def
            pn = 0; pc = 0
            for (s = a; s <= b; s++) { pn += SEGN[s]; pc += SEGC[s] }
            PNAME[p] = sprintf("%s%0" pw "d", partprefix, p)
            printf("/-- Part %d of the body: segments %d–%d. -/\n", p, a, b)
            printf("def %s : %s :=\n", PNAME[p], ty)
            line = " "
            for (s = a; s <= b; s++) {
                piece = sprintf(" %s%s", segname(s), (s < b) ? " ++" : "")
                if (length(line piece) > 90) { print line; line = " " }
                line = line piece
            }
            print line
            printf("\n")
            if (!callmode) {
                printf("/-- Part %d has %d instruction%s. -/\n", p, pn, (pn == 1) ? "" : "s")
                printf("theorem %s_length :\n    %s.length = %d := by\n", PNAME[p], PNAME[p], pn)
                printf("  unfold %s\n%s  rfl\n\n", PNAME[p], (a < b) ? "  simp only [List.length_append]\n" : "")
            } else {
                printf("/-- Part %d has %d instruction%s. -/\n", p, pn, (pn == 1) ? "" : "s")
                printf("theorem %s_instrs :\n    (CallSeg.instrs %s).length = %d := by\n", PNAME[p], PNAME[p], pn)
                printf("  unfold %s\n%s  rfl\n\n", PNAME[p], (a < b) ? "  simp only [CallSeg.instrs_append, List.length_append]\n" : "")
                printf("/-- Part %d makes %d call%s. -/\n", p, pc, (pc == 1) ? "" : "s")
                printf("theorem %s_calls :\n    (CallSeg.callees %s).length = %d := by\n", PNAME[p], PNAME[p], pc)
                printf("  unfold %s\n%s  rfl\n\n", PNAME[p], (a < b) ? "  simp only [CallSeg.callees_append, List.length_append]\n" : "")
            }
        }
    } else n_part = 0

    printf("/-- The body of `%s`, translated instruction by instruction by\n", sym)
    if (n_part > 0)
        printf("    `bench/s2n_import/import_owned.sh`: the concatenation of its %d segments,\n    grouped in %d parts", n_def, n_part)
    else
        if (n_def == 1) printf("    `bench/s2n_import/import_owned.sh`: its one segment")
        else printf("    `bench/s2n_import/import_owned.sh`: the concatenation of its %d segments", n_def)
    if (callmode) printf(".\n    Each segment is a run of instructions followed by the `call` that ends it, if any. -/\n")
    else printf(". -/\n")
    printf("def %s : %s :=\n", block, ty)
    line = " "
    top = (n_part > 0) ? n_part : n_def
    for (s = 1; s <= top; s++) {
        piece = sprintf(" %s%s", (n_part > 0) ? PNAME[s] : segname(s), (s < top) ? " ++" : "")
        if (length(line piece) > 90) { print line; line = " " }
        line = line piece
    }
    print line

    frame = ""
    for (i = 1; i <= n_push; i++) frame = frame (i > 1 ? " " : "") PUSH[i]
    printf("instructions %d\n", n_out) > summary
    printf("segments %d\n", n_def) > summary
    printf("parts %d\n", n_part) > summary
    for (p = 1; p <= n_part; p++) printf("part %s\n", PNAME[p]) > summary
    printf("calls %d\n", n_call) > summary
    printf("maxseg %d\n", maxseg) > summary
    printf("push %s\n", frame) > summary
    printf("npush %d\n", n_push) > summary
    printf("framealloc %s\n", FRAME_TEXT) > summary
    printf("framerelease %s\n", FRAME_REL_TEXT) > summary
    printf("ret %s\n", RET_TEXT) > summary
    printf("endbr %d\n", endbr) > summary
    printf("saves %d\n", n_save) > summary
    printf("restores %d\n", n_rest) > summary
    printf("movl %d\nsetcfused %d\nsetcc %d\nlea %d\n", MOVL32 + 0, SETC_FUSED + 0, SETCC + 0, LEA + 0) > summary
    for (m in REBASED) printf("rebased %s\n", m) > summary
    for (m in ALIASED) printf("aliased %s %s\n", m, ALIASED[m]) > summary
    for (m in CALLEES) printf("callee %s %d\n", m, CALLEES[m]) > summary
    for (m in MNCOUNT) printf("mnemonic %s %d\n", m, MNCOUNT[m]) > summary
    close(summary)
}
