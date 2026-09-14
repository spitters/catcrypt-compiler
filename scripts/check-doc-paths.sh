#!/usr/bin/env bash
# Doc-path gate: every package file path written in a code span of a package
# document names a tracked file or directory.
#
# check-doc-links.sh checks Markdown links `[text](path)`. Documents also name files
# in code spans (`VIR/DIALECTS.md`, `X86Backend/AsmPrinter.lean`), which that gate
# does not read. This script reads every tracked `*.md` file, the Verso manual
# (`docs/*.lean`) and the blueprint source (`blueprint/**/*.tex`), takes each
# code-span token that looks like a path, and resolves it
#   1. against the repository root, the document's directory, or one of the
#      prefixes `CatCrypt/`, `CatCrypt/Crypto/`, `CatCrypt/Crypto/SecureCompilation/`
#      (also written `SC/`) and `bench/`, as given or with `.lean` appended;
#   2. otherwise as a suffix of a tracked path at a `/` boundary.
# A token with a file extension or a `/` is checked. An extension-less token whose
# first component is not the name of a package directory (a repository slug such as
# `opencompl/veir`) is skipped, as are tokens with a URL scheme, a glob or a
# placeholder character. THIRD_PARTY_NOTICES.md and CHANGELOG.md are not read: the
# first names files of upstream repositories, the second files that were removed.
# `scripts/doc-path-exempt.txt` lists `document<TAB>token` pairs that are skipped,
# each with its reason.
#
# Usage: scripts/check-doc-paths.sh
# Exit 1 and list `document:line: token` for each path that resolves to nothing.
set -uo pipefail
cd "$(git rev-parse --show-toplevel 2>/dev/null)" || exit 2

EXEMPT="scripts/doc-path-exempt.txt"
[ -f "$EXEMPT" ] || EXEMPT=/dev/null

docs=$( { git ls-files '*.md'; git ls-files 'docs/*.lean'; git ls-files 'blueprint/*.tex'; } \
  | grep -vxE 'THIRD_PARTY_NOTICES\.md|CHANGELOG\.md' | sort -u)

# One record per code span: document, line, span text.
spans() {
  for doc in $docs; do
    grep -n -o -E '`[^`]+`' "$doc" | awk -v d="$doc" '{
      i = index($0, ":"); ln = substr($0, 1, i - 1); s = substr($0, i + 2); s = substr(s, 1, length(s) - 1)
      printf "%s\t%s\t%s\n", d, ln, s }'
  done
}

out=$(
  { git ls-files | sed 's/^/T\t/'; grep -vE '^\s*(#|$)' "$EXEMPT" | sed 's/^/E\t/'; spans | sed 's/^/S\t/'; } |
  awk -F'\t' '
    function norm(p,   n, a, i, o, k) {
      n = split(p, a, "/"); k = 0
      for (i = 1; i <= n; i++) {
        if (a[i] == "" || a[i] == ".") continue
        if (a[i] == "..") { if (k > 0) k--; continue }
        o[++k] = a[i]
      }
      p = ""; for (i = 1; i <= k; i++) p = (p == "" ? o[i] : p "/" o[i])
      return p
    }
    function known(p) { return (p in file) || (p in dir) }
    function resolves(doc, tok,   d, pre, i, c, n, cand) {
      d = doc; sub(/\/[^\/]*$/, "", d); if (d == doc) d = ""
      n = split("|" d "/|CatCrypt/|CatCrypt/Crypto/|CatCrypt/Crypto/SecureCompilation/|bench/", pre, "|")
      for (i = 1; i <= n; i++) {
        cand[1] = tok; cand[2] = tok ".lean"
        for (c = 1; c <= 2; c++) if (known(norm(pre[i] cand[c]))) return 1
      }
      if (tok ~ /^\.\.\//) return 0
      if ((tok in suffix) || ((tok ".lean") in suffix)) return 1
      return 0
    }
    $1 == "T" {
      p = $2; file[p] = 1
      n = split(p, a, "/"); s = a[n]; suffix[s] = 1
      for (i = n - 1; i >= 1; i--) { s = a[i] "/" s; suffix[s] = 1 }
      q = ""; for (i = 1; i < n; i++) { q = (q == "" ? a[i] : q "/" a[i]); dir[q] = 1; suffix[q] = 1; dirname[a[i]] = 1
        t = a[i]; for (j = i - 1; j >= 1; j--) { t = a[j] "/" t; suffix[t] = 1 } }
      next
    }
    $1 == "E" { ex[$2 "\t" $3] = 1; next }
    $1 == "S" {
      doc = $2; ln = $3; span = $4
      tok = span; sub(/[ \t].*$/, "", tok)
      if (tok != span && substr(span, length(tok) + 1, 1) !~ /[ \t]/) next
      sub(/:[0-9]+(-[0-9]+)?(,[0-9]+(-[0-9]+)?)*$/, "", tok)
      sub(/[),.;:]+$/, "", tok)
      if (tok == "" || tok ~ /:\/\/|[*?\[\]{}<>$=@()~]/ || tok ~ /^[\/.-]/) next
      if (tok !~ /^[A-Za-z0-9_.+-]+(\/[A-Za-z0-9_.+-]+)*\/?$/) next
      hasext = (tok ~ /\.(lean|md|sh|txt|tsv|s|S|asm|tex|yml|json|toml|cff|c|h|rs|jazz|jinc)$/)
      if (!hasext && tok !~ /\//) next
      t = tok; sub(/\/$/, "", t); if (t == "SC") next; sub(/^SC\//, "CatCrypt/Crypto/SecureCompilation/", t)
      if (resolves(doc, t)) next
      if (!hasext) { split(t, a, "/"); if (!(a[1] in dirname) && a[1] != "SC") next }
      if ((doc "\t" tok) in ex) next
      printf "  %s:%s: %s\n", doc, ln, tok
    }'
)

if [ -n "$out" ]; then
  printf '%s\n' "$out"
  echo "FAIL: $(printf '%s\n' "$out" | wc -l) file path(s) in document code spans name no tracked file." >&2
  exit 1
fi
echo "doc-paths: every package file path in a document code span resolves."
