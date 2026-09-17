# Translate the C-preprocessed text of one s2n-bignum x86 AT&T function into
# the elements of a Lean `List (JInstr 64)`.
#
# Input: `cpp` output with line markers (`# N "file"`).
# Variables (set with -v):
#   sym      the function label, e.g. bignum_montmul_p384
#   summary  a path; a summary of the translation is written there
#   prefix   the name prefix of the segment definitions
#   block    the name of the block definition
#   maxseg   the largest segment, in instructions (default 22)
#
# Segments follow the paragraphs of the source.  A paragraph longer than
# `maxseg` is cut into ceil(n / maxseg) near-equal parts at preprocessed-line
# boundaries, so a macro expansion is never divided; a single line longer than
# `maxseg` is a segment of its own.
#
# Output on stdout: one Lean list element per body instruction, each followed
# by a comment giving the source file line and the instruction text.
#
# Any statement outside the accepted shapes stops the translation: the program
# prints `file:line: message` on stderr and exits 1.  The accepted shapes are
# listed in README.md; nothing is inferred beyond them.

BEGIN {
    phase = "pre"          # pre -> entry -> body -> exit -> post
    cur_file = "?"
    cur_line = 0
    n_out = 0
    n_push = 0
    n_pop = 0
    endbr = 0
    failed = 0
    TWO31 = "2147483648"
    TWO32 = "4294967296"
    TWO64 = "18446744073709551616"
    split("rax rbx rcx rdx rsi rdi rbp r8 r9 r10 r11 r12 r13 r14 r15", r64list, " ")
    for (i in r64list) R64["%" r64list[i]] = 1
    R32["%eax"] = "%rax"; R32["%ebx"] = "%rbx"; R32["%ecx"] = "%rcx"
    R32["%edx"] = "%rdx"; R32["%esi"] = "%rsi"; R32["%edi"] = "%rdi"
    R32["%ebp"] = "%rbp"
    for (i = 8; i <= 15; i++) R32["%r" i "d"] = "%r" i
    CALLEE["%rbx"] = 1; CALLEE["%rbp"] = 1; CALLEE["%r12"] = 1
    CALLEE["%r13"] = 1; CALLEE["%r14"] = 1; CALLEE["%r15"] = 1
}

function fail(msg) {
    printf("%s:%d: %s\n", cur_file, cur_line, msg) > "/dev/stderr"
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

# a * m + c for a decimal string a and small integers m, c.
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

# a < b for decimal strings without leading zeros.
function declt(a, b) {
    if (length(a) != length(b)) return length(a) < length(b)
    return a < b
}

# ---- operands --------------------------------------------------------------

# The 64-bit register an operand names, or "".
function reg64(t) {
    return (t in R64) ? t : ""
}

# The 64-bit parent of a 32-bit register operand, or "".
function reg32(t) {
    return (t in R32) ? R32[t] : ""
}

# A literal (decimal or 0x hexadecimal, no sign) as a decimal string, or "".
function literal(t) {
    if (t ~ /^0[xX][0-9a-fA-F]+$/) return hex2dec(substr(t, 3))
    if (t ~ /^[0-9]+$/) return strip0(t)
    return ""
}

# The value of an immediate operand `$lit` as a decimal string, or "".
function imm(t,    v) {
    if (substr(t, 1, 1) != "$") return ""
    v = literal(substr(t, 2))
    if (v == "") fail("immediate `" t "` is not an unsigned decimal or hexadecimal literal")
    if (!declt(v, TWO64)) fail("immediate `" t "` does not fit in 64 bits")
    return v
}

# A memory operand `disp(%base)` or `(%base)`.  Sets MBASE and MOFF (a Lean
# `Int` literal) and returns 1, or returns 0 when `t` is not of that shape.
function mem(t,    p, d, b, neg, v) {
    if (t !~ /\)$/) return 0
    p = index(t, "(")
    if (p == 0) return 0
    d = substr(t, 1, p - 1)
    b = substr(t, p + 1, length(t) - p - 1)
    if (reg64(b) == "") fail("memory operand `" t "` has a base that is not a 64-bit general register, or has an index")
    neg = 0
    if (substr(d, 1, 1) == "-") { neg = 1; d = substr(d, 2) }
    if (d == "") v = "0"
    else {
        v = literal(d)
        if (v == "") fail("memory operand `" t "` has a displacement that is not a literal")
    }
    if (!declt(v, TWO31)) fail("memory operand `" t "` has a displacement outside the signed 32-bit range")
    MBASE = b
    MOFF = (neg && v != "0") ? "(-" v ")" : v
    return 1
}

function q(s) {
    return "\"" s "\""
}

# ---- statement splitting ---------------------------------------------------

# Split the operand text on commas outside parentheses into OPS[1..n].
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

# Record one translated instruction.  `touched` is a space-separated list of
# the 64-bit registers the instruction reads or writes, implicit ones included;
# `kind` marks the instruction for the positional checks.
function emit(lean, touched, kind, text,    arr, n, i) {
    n_out++
    OUT[n_out] = lean
    SRC[n_out] = text
    LOC[n_out] = cur_line
    # A new paragraph starts where the preprocessed text has a blank line (a
    # blank or comment-only line of the source) since the previous instruction.
    if (n_out == 1 || NR > PREV_NR + 1) n_para++
    PARA[n_out] = n_para
    PLINE[n_out] = NR
    PREV_NR = NR
    n = split(touched, arr, " ")
    for (i = 1; i <= n; i++) {
        LAST_KIND[arr[i]] = kind
        LAST_INSTANCE[arr[i]] = NR
    }
}

function count(mn) {
    MNCOUNT[mn]++
}

# ---- instruction translation ----------------------------------------------

function translate(mn, rest, text,    n, s, d, v, lo, hi, r) {
    n = split_operands(rest)

    if (mn == "movq") {
        if (n != 2) fail("`movq` with " n " operands")
        d = reg64(OPS[2])
        if (d != "") {
            if ((s = reg64(OPS[1])) != "") { emit(".mov " q(d) " (.reg " q(s) ")", d " " s, "", text); return }
            if ((v = imm(OPS[1])) != "")   { emit(".mov " q(d) " (.imm " v ")", d, "", text); return }
            if (mem(OPS[1]))               { emit(".loadMem " q(d) " " q(MBASE) " " MOFF, d " " MBASE, "", text); return }
        }
        if (mem(OPS[2]) && (s = reg64(OPS[1])) != "") {
            emit(".storeMem " q(MBASE) " " MOFF " (.reg " q(s) ")", MBASE " " s, "", text); return
        }
        fail("`movq` operand shape not accepted: " text)
    }

    if (mn == "addq" || mn == "subq" || mn == "adcq" || mn == "sbbq" || mn == "xorq" || mn == "andq" || mn == "orq") {
        if (n != 2) fail("`" mn "` with " n " operands")
        r = substr(mn, 1, length(mn) - 1)
        if (r == "xor" || r == "and" || r == "or") r = r "_"
        d = reg64(OPS[2])
        if (d == "") fail("`" mn "` destination is not a 64-bit general register: " text)
        if ((s = reg64(OPS[1])) != "") { emit("." r " " q(d) " (.reg " q(s) ")", d " " s, "", text); return }
        if ((v = imm(OPS[1])) != "") {
            if (!declt(v, TWO31)) fail("`" mn "` immediate is outside the sign-extended 32-bit range: " text)
            emit("." r " " q(d) " (.imm " v ")", d, "", text); return
        }
        if (mn == "addq" && mem(OPS[1])) { emit(".addMem " q(d) " " q(MBASE) " " MOFF, d " " MBASE, "", text); return }
        fail("`" mn "` operand shape not accepted: " text)
    }

    if (mn == "shlq" || mn == "shrq" || mn == "sarq") {
        if (n != 2) fail("`" mn "` with " n " operands")
        d = reg64(OPS[2])
        v = imm(OPS[1])
        if (d == "" || v == "") fail("`" mn "` needs an immediate count and a 64-bit register: " text)
        if (!declt(v, "64")) fail("`" mn "` count is 64 or more: " text)
        emit("." substr(mn, 1, 3) " " q(d) " (.imm " v ")", d, "", text); return
    }

    if (mn == "adcxq" || mn == "adoxq") {
        if (n != 2) fail("`" mn "` with " n " operands")
        r = substr(mn, 1, 4)
        d = reg64(OPS[2])
        if (d == "") fail("`" mn "` destination is not a 64-bit general register: " text)
        if ((s = reg64(OPS[1])) != "") { emit("." r " " q(d) " (.reg " q(s) ")", d " " s, "", text); return }
        if (mem(OPS[1])) { emit("." r "Mem " q(d) " " q(MBASE) " " MOFF, d " " MBASE, "", text); return }
        fail("`" mn "` operand shape not accepted: " text)
    }

    if (mn == "mulxq") {
        # AT&T `mulxq src2, lo, hi`; the first source is %rdx.
        if (n != 3) fail("`mulxq` with " n " operands")
        lo = reg64(OPS[2]); hi = reg64(OPS[3])
        if (lo == "" || hi == "") fail("`mulxq` destinations are not 64-bit general registers: " text)
        if (lo == hi) fail("`mulxq` with equal destinations: " text)
        if ((s = reg64(OPS[1])) != "") {
            emit(".mulx " q(hi) " " q(lo) " (.reg \"%rdx\") (.reg " q(s) ")", hi " " lo " %rdx " s, "", text); return
        }
        if (mem(OPS[1])) {
            emit(".mulxMem " q(hi) " " q(lo) " (.reg \"%rdx\") " q(MBASE) " " MOFF, hi " " lo " %rdx " MBASE, "", text); return
        }
        fail("`mulxq` source shape not accepted: " text)
    }

    if (mn == "cmovnzq" || mn == "cmovneq" || mn == "cmovzq" || mn == "cmoveq" || mn == "cmovbq" || mn == "cmovcq") {
        if (n != 2) fail("`" mn "` with " n " operands")
        d = reg64(OPS[2]); s = reg64(OPS[1])
        if (d == "" || s == "") fail("`" mn "` operands are not 64-bit general registers: " text)
        r = (mn == "cmovnzq" || mn == "cmovneq") ? "cmovne" : ((mn == "cmovzq" || mn == "cmoveq") ? "cmove" : "cmovb")
        emit("." r " " q(d) " (.reg " q(s) ")", d " " s, "", text); return
    }

    # ---- 32-bit forms: three accepted shapes, each checked here --------------

    if (mn == "xorl") {
        # `xorl %r32, %r32` writes 0 to the full register and sets CF = OF = 0,
        # ZF = PF = 1, SF = 0, exactly as `xorq %r64, %r64`.
        if (n != 2) fail("`xorl` with " n " operands")
        s = reg32(OPS[1]); d = reg32(OPS[2])
        if (s == "" || d == "" || OPS[1] != OPS[2])
            fail("`xorl` accepted only as the zeroing idiom on one 32-bit register: " text)
        emit(".xor_ " q(d) " (.reg " q(d) ")", d, "xorl-zero", text)
        ZEROED32++
        return
    }

    if (mn == "movl") {
        # `movl $imm, %r32` writes the zero-extended immediate to the full
        # register and no flag, exactly as a 64-bit move of the same value.
        if (n != 2) fail("`movl` with " n " operands")
        d = reg32(OPS[2]); v = imm(OPS[1])
        if (d == "" || v == "") fail("`movl` accepted only as an immediate into a 32-bit register: " text)
        if (!declt(v, TWO32)) fail("`movl` immediate does not fit in 32 bits: " text)
        emit(".mov " q(d) " (.imm " v ")", d, "", text)
        MOVL32++
        return
    }

    if (mn == "adcl") {
        # `adcl %r32, %r32` on a register whose upper and lower halves are 0
        # computes 0 + 0 + CF.  At 32 and at 64 bits the result is CF, the
        # carry-out, overflow and sign flags are 0, and ZF and PF agree, so it
        # is value- and flag-equal to `adcq %r64, %r64`.  The zero is
        # established only by the check below: the previous instruction that
        # touches the register is `xorl` zeroing it, in the same macro
        # instance (the same line of preprocessed text).
        if (n != 2) fail("`adcl` with " n " operands")
        s = reg32(OPS[1]); d = reg32(OPS[2])
        if (s == "" || d == "" || OPS[1] != OPS[2])
            fail("`adcl` accepted only on one 32-bit register as both operands: " text)
        if (LAST_KIND[d] != "xorl-zero" || LAST_INSTANCE[d] != NR)
            fail("`adcl` on " OPS[1] " is not preceded, within its macro instance, by `xorl` zeroing " OPS[1] " as the last instruction touching " d ": " text)
        emit(".adc " q(d) " (.reg " q(d) ")", d, "", text)
        ADCL32++
        ADCLREG[OPS[1]] = 1
        return
    }

    fail("mnemonic or operand size not accepted: " text)
}

# ---- driver ----------------------------------------------------------------

function statement(st,    mn, rest, p) {
    st = trim(st)
    if (st == "") return

    if (substr(st, 1, 1) == ".") {
        if (phase == "pre" || phase == "post") return
        if (st ~ /^\.cfi_/) return
        if (phase == "entry" && st ~ /^\.byte[ \t]+0xf3[ \t]*,[ \t]*0x0f[ \t]*,[ \t]*0x1e[ \t]*,[ \t]*0xfa$/) {
            if (n_push > 0 || endbr) fail("CET landing pad after the first frame instruction")
            endbr = 1
            return
        }
        fail("directive inside the function: " st)
    }

    if (st ~ /^[A-Za-z0-9_.$]+:$/) {
        if (phase == "pre") {
            if (substr(st, 1, length(st) - 1) == sym) phase = "entry"
            return
        }
        fail("label inside or after the function: " st)
    }
    if (st ~ /^[A-Za-z0-9_.$]+:/) fail("label followed by a statement: " st)

    p = match(st, /[ \t]/)
    if (p) { mn = substr(st, 1, p - 1); rest = substr(st, p + 1) }
    else { mn = st; rest = "" }

    if (phase == "pre") fail("instruction before the label `" sym "`: " st)
    if (phase == "post") fail("instruction after the return: " st)

    if (phase == "entry") {
        if (mn == "endbr64" && rest == "") {
            if (n_push > 0 || endbr) fail("CET landing pad after the first frame instruction")
            endbr = 1
            return
        }
        if (mn == "pushq") {
            if (split_operands(rest) != 1 || !(OPS[1] in CALLEE)) fail("`pushq` of a register that is not callee-saved: " st)
            PUSH[++n_push] = OPS[1]
            return
        }
        phase = "body"
    }

    if (phase == "body") {
        if (mn == "popq" || mn == "retq" || mn == "ret") phase = "exit"
        else {
            count(mn)
            translate(mn, rest, mn " " trim(rest))
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
            phase = "post"
            return
        }
        fail("instruction after the first `popq`: " st)
    }
}

/^#[ \t]*[0-9]+[ \t]+"/ {
    split($0, lm, /[ \t]+/)
    cur_line = lm[2] - 1
    cur_file = lm[3]
    gsub(/"/, "", cur_file)
    next
}

{
    cur_line++
    n = split($0, parts, ";")
    for (k = 1; k <= n; k++) statement(parts[k])
}

END {
    if (failed) exit 1
    if (phase != "post") {
        printf("%s: the function `%s` was not found or does not end in a return (phase %s)\n", cur_file, sym, phase) > "/dev/stderr"
        exit 1
    }
    # Pack each paragraph's preprocessed lines into segments.
    if (maxseg == "") maxseg = 22
    n_seg = 0
    n_cut = 0
    i = 1
    while (i <= n_out) {
        e = i
        while (e < n_out && PARA[e + 1] == PARA[i]) e++
        len = e - i + 1
        npart = int((len + maxseg - 1) / maxseg)
        cap = int((len + npart - 1) / npart)
        n_seg++
        used = 0
        k = i
        while (k <= e) {
            m = k
            while (m < e && PLINE[m + 1] == PLINE[k]) m++
            if (used > 0 && used + (m - k + 1) > cap) {
                n_seg++
                n_cut++
                used = 0
            }
            for (t = k; t <= m; t++) SEG[t] = n_seg
            used += m - k + 1
            k = m + 1
        }
        i = e + 1
    }

    # One `def` per segment, then the block as their concatenation.
    i = 1
    for (s = 1; s <= n_seg; s++) {
        j = i
        while (j < n_out && SEG[j + 1] == s) j++
        name = sprintf("%s%02d", prefix, s)
        if (LOC[i] == LOC[j]) range = "line " LOC[i]
        else range = "lines " LOC[i] "–" LOC[j]
        printf("/-- Segment %d of the body: the %d instruction%s from source %s. -/\n", s, j - i + 1, (j > i) ? "s" : "", range)
        printf("def %s : List (JInstr 64) :=\n", name)
        for (k = i; k <= j; k++) {
            printf("  %s %s%s  -- l.%d `%s`\n", (k == i) ? "[" : " ", OUT[k], (k < j) ? "," : " ]", LOC[k], SRC[k])
        }
        printf("\n")
        i = j + 1
    }
    printf("/-- The body of s2n-bignum's `%s`, translated instruction by instruction\n", sym)
    printf("    by `bench/s2n_import/import_s2n.sh`: the concatenation of its %d segments. -/\n", n_seg)
    printf("def %s : List (JInstr 64) :=\n", block)
    line = " "
    for (s = 1; s <= n_seg; s++) {
        piece = sprintf(" %s%02d%s", prefix, s, (s < n_seg) ? " ++" : "")
        if (length(line piece) > 90) { print line; line = " " }
        line = line piece
    }
    print line
    frame = ""
    for (i = 1; i <= n_push; i++) frame = frame (i > 1 ? " " : "") PUSH[i]
    printf("instructions %d\n", n_out) > summary
    printf("segments %d\n", n_seg) > summary
    printf("paragraphs %d\n", n_para) > summary
    printf("cuts %d\n", n_cut) > summary
    printf("maxseg %d\n", maxseg) > summary
    printf("frame %s\n", frame) > summary
    printf("endbr %d\n", endbr) > summary
    printf("xorl %d\nmovl %d\nadcl %d\n", ZEROED32 + 0, MOVL32 + 0, ADCL32 + 0) > summary
    for (m in ADCLREG) printf("adclreg %s\n", m) > summary
    for (m in MNCOUNT) printf("mnemonic %s %d\n", m, MNCOUNT[m]) > summary
    close(summary)
}
