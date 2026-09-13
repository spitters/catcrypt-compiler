#!/usr/bin/env bash
# Ascent corpus: the kernels of this package the ascent can process, which of them
# are named by an ascent correspondence, and which by a closed capstone theorem.
#
# Usage:
#   scripts/ascent-corpus.sh            # table, then the counts
#   scripts/ascent-corpus.sh --count    # the closed-capstone count only
#   ASCENT_CORPUS_KEEP=DIR scripts/ascent-corpus.sh
#                                       # keep the declaration index in DIR
#
# The script reads declaration text of the files git tracks. It runs no Lean, so
# it decides membership from what the statements say, not from what the kernel
# checks, and an untracked file is not read.
#
# ---------------------------------------------------------------------------
# METHOD
# ---------------------------------------------------------------------------
# 1. Index. Every tracked `CatCrypt/**/*.lean` file (`git ls-files`) is read
#    once. Block comments, docstrings and line comments are removed. A
#    declaration starts at a column-0 `theorem`, `lemma`, `def`, `abbrev`,
#    `instance`, `structure`, `inductive`, `opaque` or `axiom` (after attributes
#    and modifiers) and ends at the next column-0 declaration or command. Its
#    fully qualified name is the written name prefixed by the enclosing
#    `namespace` blocks (a written `_root_.` prefix drops them). Column-0
#    `namespace`, `section`, `mutual` and `end` lines maintain the scope stack;
#    a column-0 `open` line adds its namespaces to the current scope, and an
#    `open … in` line adds them to the next declaration only. `open X (a b)`
#    opens only `a` and `b`; `hiding` and `renaming` clauses are read as a full
#    `open X`. The `import` lines of each file are recorded.
#
# 2. Name resolution. A token of a declaration's text (a maximal run of
#    letters, digits, `_`, `'`, `!`, `?` and `.`, leading and trailing dots
#    removed) names every indexed declaration D such that D's module lies in
#    the import closure of the referring module and D's fully qualified name
#    is
#      - N.t for the innermost prefix N of the referring declaration's
#        namespace (the empty prefix included) at which such a D exists, or
#      - Q.X.t for an `open X` in effect and any prefix Q of the namespace in
#        which that `open` was written.
#    When a dotted token names nothing, its longest dotted prefix that names
#    something is used (generalized field notation `c.denote`). Every
#    declaration so named counts; the script does not disambiguate by type.
#
# 3. Kernels. A kernel is a declaration that is one of
#      lowct   a `def` or `abbrev` with no binders whose type is `LowCT`;
#      reify   a `def` or `abbrev` of type `ReifiedFunc` whose body starts with
#              `reifyLowCT%`;
#      impexpr a `def` or `abbrev` whose type is `ImpExpr` (and no binder has
#              that type), named in the statement of a theorem that also names
#              `haxToLowCTFn` or `haxToLowCTK` and contains `= some`: an
#              `ImpExpr` term, written in Lean or extracted, that the exit
#              lowering is stated to accept. The class does not decide whether
#              the term came out of hax.
#
# 4. Ascent columns. A theorem is an ascent correspondence for a kernel when
#    its conclusion (the text of the statement after its top-level `:`) has a
#    token whose last dotted component is `Corres`, `CorresU`, `CorresE`,
#    `CorresUE`, `CorresWhile`, `CorresH` or `Refines`, and its statement (the
#    text before the top-level `:=`) names the kernel. An equation for `ascendG`
#    or `tsLowCT` output alone does not count: its guards may be unsatisfiable.
#    The correspondence is single-store when its statement contains a lambda
#    `fun v => v = …` (or `↦`) with one binder whose body is an equation with
#    that binder on the left: a precondition that fixes the entry store. The
#    ASCENT column names a correspondence that is not single-store; the
#    ONE-STORE column names a single-store correspondence for a kernel with
#    none in the ASCENT column.
#
# 5. Capstone column. A theorem is a capstone candidate when its name ends in
#    one of the capstone conventions of Ascent/AGENTS.md: `_endToEnd`,
#    `_source_to_bytes`, `_source_to_bytes_tower` or `_capstone`, optionally
#    followed by further `_word` components. It is closed when
#      - no binder before the statement's top-level `:` names `hEmit`,
#        `hBridge` or `hSourceWord`, or mentions `denote`, `semScalar`, `semU`,
#        `runBlock`, `RustExec` or `Corres` (an emit, denotation or
#        correspondence equation taken as a hypothesis), and
#      - the conclusion has no premise of the form `… denote … = … →`.
#    Capstone candidates that are not closed are not reported. A closed
#    capstone reaches a kernel when its statement names the kernel, or names a
#    `def`, `abbrev`, `instance` or `opaque` whose text names it, through at
#    most six such intermediate declarations. Names are resolved as in step 2,
#    in the namespace and `open` context of the declaration whose text is read,
#    and against the import closure of the capstone's module. The chain line
#    under a row prints the path from the capstone to the kernel.
#
# The counts are: kernels (per class), kernels with an ascent correspondence
# that is not single-store, kernels with only single-store correspondences, and
# kernels with a closed capstone. A theorem with a `sorry` is not distinguished;
# `scripts/sorry-gate.sh` gates that separately.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

mode="${1:-table}"

if [ -n "${ASCENT_CORPUS_KEEP:-}" ]; then
  tmp="$ASCENT_CORPUS_KEEP"; mkdir -p "$tmp"
else
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
fi
rm -f "$tmp/idx" "$tmp/imp"

git ls-files -z 'CatCrypt/*.lean' > "$tmp/files"

# ---------------------------------------------------------------------------
# Stage 1: declaration and import index.
#   idx: file TAB kind TAB fqname TAB namespace TAB opens TAB text
#   opens: entries ";nsAtOpen|X|names" (names empty for a full open)
# ---------------------------------------------------------------------------
xargs -0 awk -v IDX="$tmp/idx" -v IMP="$tmp/imp" '
function flush() {
  if (cur != "") {
    gsub(/\t/, " ", txt)
    print curfile "\t" kind "\t" cur "\t" curNs "\t" curOpens "\t" txt >> IDX
  }
  cur = ""; txt = ""
}
function parseOpen(o,    out, nm, inner, n, parts, j) {
  gsub(/(^| )scoped( |$)/, " ", o)
  sub(/ +hiding .*$/, "", o); sub(/ +renaming .*$/, "", o)
  sub(/^ +/, "", o); sub(/ +$/, "", o)
  out = ""
  if (index(o, "(") > 0) {
    nm = substr(o, 1, index(o, "(") - 1); sub(/ +$/, "", nm)
    inner = substr(o, index(o, "(") + 1); sub(/\).*$/, "", inner)
    gsub(/ +/, " ", inner); sub(/^ /, "", inner); sub(/ $/, "", inner)
    sub(/^_root_\./, "", nm)
    return ";" ns "|" nm "|" inner
  }
  n = split(o, parts, " ")
  for (j = 1; j <= n; j++) {
    if (parts[j] == "") continue
    nm = parts[j]; sub(/^_root_\./, "", nm)
    out = out ";" ns "|" nm "|"
  }
  return out
}
FNR == 1 {
  flush(); depth = 0; curfile = FILENAME; ns = ""; opens = ""; pend = ""; sp = 0
  print curfile "\t" >> IMP
}
{
  line = $0
  if (depth == 0 && index(line, "/-") == 0) {
    sub(/--.*/, "", line)
  } else {
    out = ""; i = 1; n = length(line)
    while (i <= n) {
      c2 = substr(line, i, 2)
      if (c2 == "/-") { depth++; i += 2; continue }
      if (depth > 0 && c2 == "-/") { depth--; i += 2; continue }
      if (depth == 0) {
        if (c2 == "--") break
        out = out substr(line, i, 1)
      }
      i++
    }
    line = out
  }
  if (line ~ /^((public|private) +)?(meta +)?import +/) {
    m = line; sub(/^.*import +(all +)?/, "", m); sub(/[ \t].*$/, "", m)
    print curfile "\t" m >> IMP
    next
  }
  if (line ~ /^(@\[[^]]*\] *)?((private|protected|noncomputable|partial|unsafe|nonrec|public|meta) +)*(theorem|lemma|def|abbrev|instance|structure|inductive|opaque|axiom) /) {
    flush()
    s = line
    sub(/^@\[[^]]*\] */, "", s)
    while (s ~ /^(private|protected|noncomputable|partial|unsafe|nonrec|public|meta) /) sub(/^[a-z]+ +/, "", s)
    kind = s; sub(/ .*$/, "", kind)
    rest = substr(s, length(kind) + 1); sub(/^ +/, "", rest)
    nm = rest; sub(/[ :({[].*$/, "", nm)
    if (nm == "") nm = "_anon"
    if (nm ~ /^_root_\./) { sub(/^_root_\./, "", nm); cur = nm }
    else cur = (ns == "") ? nm : ns "." nm
    curNs = ns; curOpens = opens pend; pend = ""
    txt = rest
    next
  }
  if (line ~ /^open +/) {
    flush()
    o = line; sub(/^open +/, "", o)
    if (o ~ /(^| )in *$/) { sub(/ *in *$/, "", o); pend = pend parseOpen(o) }
    else opens = opens parseOpen(o)
    next
  }
  if (line ~ /^namespace +/) {
    flush(); pend = ""
    m = line; sub(/^namespace +/, "", m); sub(/[ \t].*$/, "", m)
    stNs[sp] = ns; stOp[sp] = opens; sp++
    ns = (ns == "") ? m : ns "." m
    next
  }
  if (line ~ /^(@\[[^]]*\] *)?((public|private|noncomputable|meta) +)*section( |$)/ || line ~ /^mutual( |$)/) {
    flush(); pend = ""
    stNs[sp] = ns; stOp[sp] = opens; sp++
    next
  }
  if (line ~ /^end( |$)/) {
    flush(); pend = ""
    if (sp > 0) { sp--; ns = stNs[sp]; opens = stOp[sp] }
    next
  }
  if (line ~ /^(#|set_option|variable|attribute|example|macro|syntax|elab|notation|infix|universe|@\[|deriving|initialize|add_decl_doc|scoped|local|export)/) {
    flush()
    if (line !~ / in *$/ && line !~ /^@\[/) pend = ""
    next
  }
  if (cur != "") txt = txt " " line
}
END { flush() }
' < "$tmp/files"

# ---------------------------------------------------------------------------
# Stage 2: kernels, ascent correspondences, closed capstones.
# ---------------------------------------------------------------------------
awk -F'\t' -v MODE="$mode" '
function depth0(t, pat,    i, n, d, c, c3, L) {
  # Byte offset of the first depth-0 occurrence of pat (":=" or ":"), or 0.
  n = length(t); d = 0; L = length(pat)
  for (i = 1; i <= n; i++) {
    c = substr(t, i, 1); c3 = substr(t, i, 3)
    if (c == "(" || c == "[" || c == "{" || c3 == "⟨") { d++; continue }
    if (c == ")" || c == "]" || c == "}" || c3 == "⟩") { d--; continue }
    if (d == 0 && substr(t, i, L) == pat) {
      if (pat == ":" && (substr(t, i, 2) == ":=" || substr(t, i, 2) == "::")) { i++; continue }
      return i
    }
  }
  return 0
}
function stmtOf(t,    k) { k = depth0(t, ":="); return (k > 0) ? substr(t, 1, k - 1) : t }
function conclOf(s,    k) { k = depth0(s, ":"); return (k > 0) ? substr(s, k + 1) : s }
function closure(f,    queue, qh, qt, g, m, parts, np, j, h) {
  if (f in closDone) return
  closDone[f] = 1
  qh = 1; qt = 1; queue[1] = f; inClos[f SUBSEP f] = 1
  while (qh <= qt) {
    g = queue[qh++]
    np = split(imports[g], parts, " ")
    for (j = 1; j <= np; j++) {
      m = parts[j]; if (m == "") continue
      h = m; gsub(/\./, "/", h); h = h ".lean"
      if (!(h in isFile)) continue
      if (!((f SUBSEP h) in inClos)) { inClos[f SUBSEP h] = 1; queue[++qt] = h }
    }
  }
}
function shorten(q) { if (index(q, ".") == 0) return ""; sub(/\.[^.]*$/, "", q); return q }
function addCands(fq, cf, out,    nc, cand, c, x, found) {
  if (!(fq in byFq)) return 0
  nc = split(byFq[fq], cand, " "); found = 0
  for (c = 1; c <= nc; c++) {
    x = cand[c] + 0; if (x == 0) continue
    if (!((cf SUBSEP dFile[x]) in inClos)) continue
    out[x] = 1; found = 1
  }
  return found
}
function resolveOne(t, i, cf, out,    q, found, no, ents, e, parts, names, hd, pre) {
  found = 0
  q = dNs[i]
  while (1) {
    if (addCands((q == "") ? t : q "." t, cf, out)) { found = 1; break }
    if (q == "") break
    q = shorten(q)
  }
  no = split(dOpens[i], ents, ";")
  for (e = 1; e <= no; e++) {
    if (ents[e] == "") continue
    split(ents[e], parts, "|")
    names = parts[3]
    if (names != "") { hd = t; sub(/\..*$/, "", hd); if (index(" " names " ", " " hd " ") == 0) continue }
    q = parts[1]
    while (1) {
      pre = (q == "") ? parts[2] : q "." parts[2]
      if (addCands(pre "." t, cf, out)) found = 1
      if (q == "") break
      q = shorten(q)
    }
  }
  return found
}
function resolve(tok, i, cf, out,    t) {
  # Declarations named by token tok read in declaration i, against the closure of cf.
  t = tok; sub(/^\.+/, "", t); sub(/\.+$/, "", t)
  if (t == "" || t ~ /^[0-9]/) return 0
  while (1) {
    if (resolveOne(t, i, cf, out)) return 1
    if (index(t, ".") == 0) return 0
    t = shorten(t)
  }
}
function tokens(t, arr) { return split(t, arr, TOKRE) }
function lastComp(t) { sub(/^.*\./, "", t); return t }
function oneStore(s,    r, m, v1, v2) {
  r = s
  while (match(r, ONERE)) {
    m = substr(r, RSTART, RLENGTH)
    v1 = m; sub(/^fun +/, "", v1); sub(/ .*$/, "", v1)
    v2 = m; sub(/^fun +[^ ]+ +[^ ]+ +/, "", v2); sub(/[ =].*$/, "", v2)
    if (v1 == v2) return 1
    r = substr(r, RSTART + RLENGTH)
  }
  return 0
}
function shortName(fq) { sub(/^CatCrypt\.Crypto\.SecureCompilation\./, "", fq); return fq }
BEGIN {
  TOKRE = "[^A-Za-z0-9_\047!?.]+"
  ONERE = "fun +[A-Za-z_][A-Za-z0-9_\047]* +(=>|↦) +[A-Za-z_][A-Za-z0-9_\047]* *= *[^=>]"
}
FNR == NR {                       # imports
  isFile[$1] = 1
  if ($2 != "") imports[$1] = imports[$1] " " $2
  next
}
{                                 # declarations
  N++
  dFile[N] = $1; dKind[N] = $2; dName[N] = $3; dNs[N] = $4; dOpens[N] = $5; dTxt[N] = $6
  byFq[$3] = byFq[$3] " " N
}
END {
  # Kernels.
  for (i = 1; i <= N; i++) {
    if (dKind[i] != "def" && dKind[i] != "abbrev") continue
    t = dTxt[i]
    if (t ~ /^[^ ]+ +: +([A-Za-z_]+\.)*LowCT +:=/) { K++; kId[K] = i; kCls[K] = "lowct"; isKernel[i] = K }
    else if (t ~ /^[^ ]+ +: +([A-Za-z_]+\.)*ReifiedFunc +:= +reifyLowCT%/) { K++; kId[K] = i; kCls[K] = "reify"; isKernel[i] = K }
  }
  for (i = 1; i <= N; i++) {
    if (dKind[i] != "theorem" && dKind[i] != "lemma") continue
    s = stmtOf(dTxt[i])
    if (s !~ /haxToLowCT(Fn|K)/ || s !~ /= *some/) continue
    closure(dFile[i])
    nt = tokens(s, tk)
    for (j = 1; j <= nt; j++) {
      delete hit
      if (!resolve(tk[j], i, dFile[i], hit)) continue
      for (x in hit) {
        x = x + 0
        if (x in isKernel) continue
        if (dKind[x] != "def" && dKind[x] != "abbrev") continue
        h = stmtOf(dTxt[x])
        if (h !~ /: +(_root_\.)?([A-Za-z_]+\.)*ImpExpr *$/) continue
        tmpH = h; if (gsub(/ImpExpr/, "", tmpH) != 1) continue
        K++; kId[K] = x; kCls[K] = "impexpr"; isKernel[x] = K
      }
    }
  }

  # Ascent correspondences.
  for (i = 1; i <= N; i++) {
    if (dKind[i] != "theorem" && dKind[i] != "lemma") continue
    s = stmtOf(dTxt[i])
    if (s !~ /Corres|Refines/) continue
    cc = conclOf(s)
    nt = tokens(cc, tk); hasCorres = 0
    for (j = 1; j <= nt; j++) {
      if (lastComp(tk[j]) ~ /^(Corres|CorresU|CorresE|CorresUE|CorresWhile|CorresH|Refines)$/) hasCorres = 1
    }
    if (!hasCorres) continue
    one = oneStore(s)
    closure(dFile[i])
    nt = tokens(s, tk)
    for (j = 1; j <= nt; j++) {
      delete hit
      if (!resolve(tk[j], i, dFile[i], hit)) continue
      for (x in hit) {
        x = x + 0
        if (!(x in isKernel)) continue
        k = isKernel[x]
        if (one) { if (!(k in oneOf)) oneOf[k] = dName[i] }
        else if (!(k in ascentOf)) ascentOf[k] = dName[i]
      }
    }
  }

  # Closed capstones.
  for (i = 1; i <= N; i++) {
    if (dKind[i] != "theorem" && dKind[i] != "lemma") continue
    if (dName[i] !~ /(_endToEnd|_source_to_bytes|_source_to_bytes_tower|_capstone)(_[A-Za-z0-9]+)*\047?$/) continue
    s = stmtOf(dTxt[i])
    colon = depth0(s, ":")
    binders = (colon > 0) ? substr(s, 1, colon - 1) : ""
    concl = (colon > 0) ? substr(s, colon + 1) : s
    if (binders ~ /hEmit|hBridge|hSourceWord|denote|semScalar|semU|runBlock|RustExec|Corres/) continue
    if (concl ~ /denote[^→]*=[^→]*→/) continue
    cf = dFile[i]
    closure(cf)
    delete seen; delete parent; delete dep
    qh = 1; qt = 1; q[1] = i; seen[i] = 1; dep[i] = 0
    while (qh <= qt) {
      y = q[qh++]
      body = (y == i) ? s : dTxt[y]
      nt = tokens(body, tk)
      for (j = 1; j <= nt; j++) {
        delete hit
        if (!resolve(tk[j], y, cf, hit)) continue
        for (x in hit) {
          x = x + 0
          if (x in seen) continue
          seen[x] = 1; parent[x] = y; dep[x] = dep[y] + 1
          if (x in isKernel) {
            k = isKernel[x]
            if (!(k in capOf)) {
              chain = shortName(dName[x]); p = y
              while (p != i) { chain = shortName(dName[p]) " > " chain; p = parent[p] }
              capOf[k] = dName[i]; chainOf[k] = shortName(dName[i]) " > " chain
            }
            continue
          }
          if (dep[x] > 6) continue
          if (dKind[x] != "def" && dKind[x] != "abbrev" && dKind[x] != "instance" && dKind[x] != "opaque") continue
          q[++qt] = x
        }
      }
    }
  }

  nA = 0; nO = 0; nC = 0
  for (k = 1; k <= K; k++) {
    if (k in ascentOf) nA++
    else if (k in oneOf) nO++
    if (k in capOf) nC++
    cls[kCls[k]]++
  }
  if (MODE == "--count") { print nC; exit }
  printf "%-7s  %-44s  %-28s  %-22s  %-26s  %s\n", "CLASS", "KERNEL", "ASCENT", "ONE-STORE", "CLOSED CAPSTONE", "MODULE / CHAIN"
  for (k = 1; k <= K; k++) {
    x = kId[k]
    a = (k in ascentOf) ? shortName(ascentOf[k]) : "-"
    o = (!(k in ascentOf) && (k in oneOf)) ? shortName(oneOf[k]) : "-"
    cp = (k in capOf) ? shortName(capOf[k]) : "-"
    where = dFile[x]; sub(/^CatCrypt\/Crypto\/SecureCompilation\//, "SC/", where)
    printf "%-7s  %-44s  %-28s  %-22s  %-26s  %s\n", kCls[k], shortName(dName[x]), a, o, cp, where
    if (k in capOf) printf "%-7s  %-44s  %-28s  %-22s  %-26s    %s\n", "", "", "", "", "", chainOf[k]
  }
  print ""
  printf "kernels: %d (lowct %d, reify %d, impexpr %d)\n", K, cls["lowct"], cls["reify"], cls["impexpr"]
  printf "kernels with an ascent correspondence that is not single-store: %d\n", nA
  printf "kernels with only single-store ascent correspondences: %d\n", nO
  printf "kernels with a closed capstone: %d\n", nC
}
' "$tmp/imp" "$tmp/idx"
