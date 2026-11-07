#!/usr/bin/env bash
# Pre-commit gate: a committed proof holds the frozen result of a search tactic, not the
# search. `grind? +suggestions` prints `grind only [...]`, `try?`, `exact?`, `apply?`,
# `rw?`, `simp?` and `aesop?` print the tactic they found, and `catcrypt_auto?` prints the
# script of the arm that closed the goal; that printed text goes into the source. Left in a
# proof, the search runs again at every elaboration: on 327 goals (HAMMER-1, 2026-11-07)
# `grind? +suggestions` took a median of 606 ms against 18 ms for `grind`, with 53
# heartbeat timeouts of 21-177 s, and a bare `catcrypt_auto` runs the dispatcher's
# `grind +suggestions` arms. On 2026-11-07 no committed proof in CatCrypt, CatCrypt-core or
# catcrypt-compiler held one of these forms.
#
# Usage: search-tactic-gate.sh FILE...   (staged .lean files; exit 1 on a hit)
# Exempt: files under a `Tactics/` directory (they define and test the search tactics) and
# test files (`*Test*`, `Test/`). Comments and string literals are not searched.
set -u
[ "$#" -eq 0 ] && exit 0
python3 -I - "$@" <<'PY'
import re, subprocess, sys

PATTERNS = [
    (re.compile(r"\bgrind\??\s*\+suggestions\b"), "grind +suggestions / grind? +suggestions"),
    (re.compile(r"(?<![\w.'])(grind|try|exact|apply|rw|simp|simp_all|aesop|catcrypt_auto)\?(?![\w?])"), None),
    (re.compile(r"(?<![\w.'])catcrypt_auto(?![\w?'])"), "catcrypt_auto (bare)"),
]


def staged_text(path):
    r = subprocess.run(["git", "show", f":{path}"], capture_output=True, text=True)
    if r.returncode == 0:
        return r.stdout
    try:
        with open(path, encoding="utf-8") as f:
            return f.read()
    except OSError:
        return ""


def code_lines(text):
    """(line number, text) of the code outside comments and string literals."""
    out, buf, depth, i, line, n = [], [], 0, 0, 1, len(text)
    in_str = False
    while i < n:
        c = text[i]
        if c == "\n":
            out.append((line, "".join(buf)))
            buf, line = [], line + 1
            i += 1
            continue
        if in_str:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if depth:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                i += 1
            continue
        if text.startswith("/-", i):
            depth, i = 1, i + 2
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        buf.append(c)
        i += 1
    out.append((line, "".join(buf)))
    return out


hits = []
for path in sys.argv[1:]:
    if not path.endswith(".lean") or "/Tactics/" in f"/{path}" or "Test" in path:
        continue
    for ln, code in code_lines(staged_text(path)):
        for rx, label in PATTERNS:
            m = rx.search(code)
            if m:
                hits.append(f"{path}:{ln}: {label or m.group(0)}: {code.strip()[:100]}")
                break
if hits:
    print("pre-commit: a search tactic is left in a proof; paste the tactic it printed instead")
    print("(the `Try this` text; for grind? +suggestions the `grind only [...]` script):")
    for h in hits:
        print("  " + h)
    print("Files under Tactics/ and test files are exempt; a false positive: git commit --no-verify.")
    sys.exit(1)
PY
