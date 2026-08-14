#!/usr/bin/env bash
# Vacuous / assumption-shaped "security theorem" ratchet.
#
# CANONICAL RULE: a `theorem` that STATES a security bound must DERIVE it. The
# anti-pattern this guard forbids is the assumption-shaped theorem — one that
# LOOKS like a proved reduction but whose security content is passed in as a
# hypothesis and re-exported, so the proof says nothing:
#
#   * conclusion ≡ a hypothesis, proof `:= h_bound` / `:= h_cpa` / `:= h_fo` /
#     `:= h_total` (the bound is assumed, then returned unchanged);
#   * structure-field projection, proof `:= P.reduction` (the "theorem" is the
#     field of a Params record that already holds the claimed inequality);
#   * identity over an assumed implication, proof `fun _ h => h`;
#   * the security *predicate itself* defined `: Prop := True` (then discharged
#     by `trivial`) — so every "secure" theorem about it is vacuous.
#
# These are NOT the same as the legitimate `(composition plumbing)` UC lifts
# (which apply a PROVED metric lemma to an assumed sdist bound) or genuine
# `le_trans (<proved lemma>) (<hypothesis>)` chains. The detector below targets
# only the four high-signal shapes above, over comment-stripped source so prose
# mentions don't count.
#
# Detector (grep/perl, per file, after stripping `/- … -/` and `-- …`):
#   VACUOUS marker (any one):
#     `: Prop := True`                         (vacuous security predicate)
#     a proof-body line that is exactly one of
#       h_bound | h_cpa | h_fo | h_total | h_link | h_reduce
#       (optionally prefixed `:= `)            (conclusion ≡ hypothesis)
#     `fun _ h => h`                           (identity over assumed implication)
#     `:= <Ident>.reduction`                   (structure-field projection)
#
# Scope: ALL of CatCrypt/.
#
# ALL FOUR dimensions read ZERO in this package, and that is the point of running
# them: this is the verified compiler carved away from the scheme security layer,
# so the security-flavoured statements it does contain — the `sdist` / leakage /
# non-interference results over `Com` — start from a clean slate and the ratchet
# keeps them there. Dimension 2 doubles as a carve invariant: a cryptographic
# hardness assumption appearing as an `axiom` here would mean the security layer
# had leaked back into the compiler package.
#
# FOUR ratchet dimensions, all MONOTONE NON-INCREASING (goal: count stays 0):
#   (1) VACUOUS security PREDICATES — `def <SecurityName> : Prop := True`.
#   (2) CRYPTO ASSUMPTION AXIOMS — a security claim that could not be derived,
#       turned into an explicit named `axiom` (visible in `#print axioms`).
#       Scope: security-named axioms under CatCrypt/Crypto. The package's ISA /
#       jasmin / byte-trust axioms are a different class and are reported by
#       AxiomAudit.lean, not here.
#
#   (3) SELF-HYPOTHESIS RE-EXPORTS — a security-flavoured theorem whose STATEMENT
#       is, verbatim, one of its OWN hypotheses, proved by returning that
#       hypothesis. This replaces the old hardcoded name list
#       (h_bound|h_cpa|h_fo|h_total|h_link|h_reduce) with the binder names taken
#       from each theorem's own signature, so the shape is caught whatever the
#       hypothesis is called. See "Dimension 3" below for the exact rule.
#   (4) UNDERSCORED (UNUSED) CRYPTO ASSUMPTIONS — a theorem that binds a
#       hypothesis as `_h_rsa` / `_hSS` / `(_h : …)`: the underscore suppresses
#       Lean's unused-variable warning, so it is a reliable tell that a NAMED,
#       ADVERTISED assumption is not used by the proof (the theorem holds without
#       it). See "Dimension 4" below for the exact rule.
#
# Each dimension FAILS if it GROWS (a NEW vacuous predicate / NEW crypto-assumption
# axiom appeared — derive the bound, or deliberately re-baseline with a literature
# reference in the axiom's docstring), and AUTO-TIGHTENS its baseline when it
# SHRINKS (a shell was replaced by a proof / an axiom was discharged into a
# theorem). Neither requires removing existing debt; they only forbid growth.
#
# Run from anywhere in the repo: `bash scripts/vacuous-theorem-ratchet.sh`
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
BASELINE_FILE="scripts/vacuous-theorem-baseline.txt"

# A file counts iff, AFTER stripping block/line comments, it contains EITHER a
# vacuous security *predicate* (`: Prop := True`) OR a security-named theorem
# whose proof HEAD is a vacuous term (bare hypothesis / le_trans of two
# hypotheses / structure-field projection / identity-over-assumption). Scoping
# the term-proof shapes to security-named declarations is what keeps genuine
# proofs (bignum-Hoare chains that legitimately name a hypothesis `h_total`,
# tactic combinators `fun _ h => h`) out of the count.
# The ONE shape gated here is the one that is UNAMBIGUOUS under a syntactic scan
# and has ZERO false positives: a security predicate DEFINED as True —
#   `def <…Advantage|…Secure|…Sound|…Unforge> : Prop := True`
# so every "secure" theorem about it (`… := by trivial`) is vacuous. Eight files
# in this package contain `: Prop := True`; none of them names a security
# predicate, which is why the count is 0 rather than the scan being empty.
#
# Dimension 3 gates the bare `:= h` shape where the re-exported term is one of the
# theorem's OWN binders and the statement is that binder's type verbatim. What
# stays OUT of dimension 3: `le_trans h_x h_y` chains and `:= P.reduction`
# structure-field projections. Separating those from real content needs the
# elaborated types, so a text scan can only guess; an environment-level detector
# is the right home for them.
# Perl slurp: exit(0) => counts, exit(1) => skip.
is_vacuous() {
  perl -0777 -ne '
    s{/-.*?-/}{}gs;         # strip block comments/docstrings
    s{--[^\n]*}{}g;         # strip line comments
    # a `def <SecurityName> … : Prop := True` — scoped to a security-flavored
    # name so benign trivial predicates (well-formedness / emit / tooling stubs)
    # do not count. Non-greedy `.*?` skips the binders between name and `: Prop`.
    my $S = qr/(?:Advantage|Secure|Soundness|Sound\b|Unforge|EUFCMA|UFCMA|Anonym|Extractab|Binding|Hiding|IND_?CPA|IND_?CCA|ZeroKnowledge|Knowledge|Privacy|Simulatab)/;
    exit(0) if /\bdef\s+(\w*(?:$S)\w*)\b.*?:\s*Prop\s*:=\s*True\b/s;
    exit(1);
  ' "$1"
}

TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT
for f in $(grep -rlE ': Prop := True' --include='*.lean' CatCrypt/); do
  is_vacuous "$f" || continue
  echo "$f"
done | sort > "$TMP"
CURRENT="$(grep -c . "$TMP" || true)"

BASELINE="$(grep -m1 -oE '^[0-9]+' "$BASELINE_FILE" 2>/dev/null || echo 0)"
echo "Vacuous / assumption-shaped security modules: current=$CURRENT  baseline=$BASELINE"

if [ "$CURRENT" -gt "$BASELINE" ]; then
  echo ""
  echo "FAIL: the vacuous / assumption-shaped security-theorem count GREW ($BASELINE -> $CURRENT)."
  echo "      A theorem that STATES a security bound must DERIVE it — do not assume the"
  echo "      bound as a hypothesis and re-export it (:= h_bound / := P.reduction /"
  echo "      fun _ h => h), and do not define a security predicate as ': Prop := True'."
  echo "      Either prove the reduction, or (if a foundation is genuinely missing) mark"
  echo "      the assumption explicitly in the docstring and add a real hypothesis."
  echo "      NEW vacuous module(s) (not in the baseline):"
  comm -13 <(grep '^CatCrypt/' "$BASELINE_FILE" 2>/dev/null | sort) "$TMP" | sed 's/^/        /'
  exit 1
fi

if [ "$CURRENT" -lt "$BASELINE" ]; then
  echo ""
  echo "Good — the count SHRANK ($BASELINE -> $CURRENT). Auto-tightening the baseline."
  {
    echo "$CURRENT"
    echo "# Vacuous / assumption-shaped security modules (frozen baseline; auto-tightened"
    echo "# by scripts/vacuous-theorem-ratchet.sh). First line = count; the sorted module"
    echo "# list below is for diffability. Goal: derive each bound (or mark the assumption"
    echo "# explicitly), count -> 0."
    cat "$TMP"
  } > "$BASELINE_FILE"
fi

# ---------------------------------------------------------------------------
# Dimension 2: crypto assumption-axiom ratchet
# ---------------------------------------------------------------------------
# The explicit form of a security claim that could not be derived is a named
# `axiom` (surfaced by `#print axioms`). This dimension ratchets that surface so a
# new cryptographic assumption cannot enter the compiler package silently. Scope =
# security-named axioms under CatCrypt/Crypto. The package's own ISA / jasmin /
# byte-trust axioms carry no such name and are reported by AxiomAudit.lean.
AX_BASELINE_FILE="scripts/assumption-axiom-baseline.txt"
AX_TMP="$(mktemp)"
trap 'rm -f "$TMP" "$AX_TMP"' EXIT

# crypto-assumption name markers (case-insensitive); reused for the Crypto scan.
AX_NAME='(qrom|o2h|reprogram|reduction|extractab|ind_?cca|ind_?cpa|owcpa|ow_pcva|_ax\b|advantage|unforge|eufcma|ufcma|binding|hiding|soundness|anonym|_cca|_cpa|hardness|assumption)'
{
  # security-named axioms anywhere under CatCrypt/Crypto
  grep -rniE "^axiom +\w*${AX_NAME}\w*" --include='*.lean' CatCrypt/Crypto/ 2>/dev/null || true
} | sed -E 's/^([^:]+):[0-9]+:axiom +([A-Za-z0-9_]+).*/\1  \2/' | sort -u > "$AX_TMP"
AX_CURRENT="$(grep -c . "$AX_TMP" || true)"
AX_BASELINE="$(grep -m1 -oE '^[0-9]+' "$AX_BASELINE_FILE" 2>/dev/null || echo 0)"
echo "Crypto assumption axioms: current=$AX_CURRENT  baseline=$AX_BASELINE"

if [ "$AX_CURRENT" -gt "$AX_BASELINE" ]; then
  echo ""
  echo "FAIL: the crypto assumption-axiom count GREW ($AX_BASELINE -> $AX_CURRENT)."
  echo "      A NEW named assumption entered the security base of a package that is"
  echo "      supposed to carry none. Either DERIVE it (turn the axiom into a proved"
  echo "      theorem), or re-baseline deliberately with a literature reference in the"
  echo "      axiom's docstring."
  echo "      NEW assumption axiom(s) (not in the baseline):"
  comm -13 <(grep -E '^CatCrypt/' "$AX_BASELINE_FILE" 2>/dev/null | sort) "$AX_TMP" | sed 's/^/        /'
  exit 1
fi

if [ "$AX_CURRENT" -lt "$AX_BASELINE" ]; then
  echo ""
  echo "Good — the assumption-axiom count SHRANK ($AX_BASELINE -> $AX_CURRENT). Auto-tightening."
  {
    echo "$AX_CURRENT"
    echo "# Crypto assumption-axiom surface (frozen baseline; auto-tightened by"
    echo "# scripts/vacuous-theorem-ratchet.sh). First line = count; the sorted"
    echo "# \"<path>  <axiom>\" list below is for diffability. Goal: count -> 0."
    echo "# Scope: security-named axioms under CatCrypt/Crypto."
    cat "$AX_TMP"
  } > "$AX_BASELINE_FILE"
fi

# ---------------------------------------------------------------------------
# Dimensions 3 + 4: one signature-level scan of every theorem/lemma in CatCrypt/
# ---------------------------------------------------------------------------
# Both dimensions read the SIGNATURE of each `theorem`/`lemma` (after stripping
# block/line comments), so neither depends on a hardcoded hypothesis-name list.
# The scan splits a file into declaration chunks, cuts each chunk at its first
# bracket-depth-0 `:=` into signature + proof body, and reads the signature's
# top-level binder groups `(names : type)` / `{…}` / `[…]` plus the conclusion
# (the text after the last depth-0 `:`).
#
# Dimension 3 — SELF-HYPOTHESIS RE-EXPORT. Flag a declaration when ALL hold:
#   * the conclusion mentions a security-flavoured identifier (Advantage / sdist /
#     UCEmulates / Secure / Soundness / Binding / …) — this is what keeps ordinary
#     plumbing lemmas (`Orth.commute := h ha hb`, `IsPure` transport, ZX-graph
#     rewrites) out of the count;
#   * the proof body is exactly `h`, `h a b …` or `by exact h …`, where `h` is a
#     binder of THIS declaration whose name starts with `h`/`H` (optionally
#     underscored) and every argument is a plain identifier or `_`;
#   * the binder's type, with its leading `∀ …,` prefixes stripped, is TEXTUALLY
#     EQUAL to the conclusion with its leading `∀ …,` stripped (whitespace and
#     named implicit arguments `(W := W)` normalised away).
# The last clause is what makes this precise rather than noisy. It admits only
# the tautology `theorem foo (h : P) : P := h` (up to ∀-instantiation), where no
# reading gives the theorem content. It deliberately REJECTS two neighbours a
# text scan cannot judge:
#   * `:= h args` where the conclusion is a DIFFERENT expression that happens to
#     be definitionally equal to the hypothesis. Most are defects, but the same
#     shape covers legitimate specialisation lemmas that instantiate a
#     ∀-quantified bound, which is real content. Separating them needs
#     elaboration, so they are out of scope for this scan.
#   * structure-instance proofs (`… : AEADSecure … where  ind_cpa_bound := h`):
#     one field being a hypothesis does not make a multi-field structure vacuous.
# The security-marker set deliberately omits `prTrue`: a bare `prTrue g ≤ ε` is a
# probability bound that carries correctness statements as often as security ones,
# so admitting it would pull correctness lemmas into a security ratchet.
# Also NOT implemented: "the body is a single call to ANOTHER lemma". That is the
# most common legitimate one-line proof shape; deciding whether the callee's
# statement covers the caller's needs the elaborated types, so a text scan can
# only cry wolf. Left out on purpose.
#
# Dimension 4 — UNDERSCORED (UNUSED) CRYPTO ASSUMPTION. Flag a `(name : type)`
# binder of a theorem/lemma when ALL hold:
#   * the name is underscore-prefixed AND hypothesis-shaped: `_h`, `_h_rsa`,
#     `_hSS`, `_hFoo`. A bare `_`, an instance binder `_inst…`, and data-ish
#     underscored parameters (`_sessId`, `_label`, `_M`, `_f`) are NOT flagged —
#     they are ordinary, and there are ~700 of them, so requiring the `_h` shape
#     is what makes this dimension usable at all;
#   * the type mentions a security-flavoured identifier (as in dimension 3) OR a
#     `_`/camelCase SEGMENT of the name is a crypto-assumption word (rsa, ddh,
#     prf, mlwe, eufcma, …). Segment (not substring) matching is required:
#     `_h_borrow` and `_h_round` contain "ro" but are not assumptions;
#   * the name is NOT referenced in the proof body — Lean permits using an
#     underscored binder, so the underscore alone does not prove it is unused;
#   * the body contains no context-sweeping tactic (`simp_all`, `aesop`, `omega`,
#     `grind`, `linarith`, `tauto`, `simp [*]`, …), which could consume the
#     hypothesis without naming it. This costs recall, and that is the intended
#     trade: a missed site is cheap, a false accusation gets the guard switched off.
#   `assumption` / `trivial` / `decide` are NOT treated as sweeping tactics: they
#   cannot give an assumption content (if `assumption` closes a security goal from
#   `_h_ddh`, the conclusion IS the assumption — dimension 3's defect, not a use).
#
# Both baselines stand at 0 in this package. A baselined site that gets repaired
# makes the count DROP, and the shrink branch tightens the baseline automatically —
# commit the tightened file. Never relax a detector to make a number look better,
# and do not add a per-site exclusion for a site that is simply broken.
SH_BASELINE_FILE="scripts/self-hypothesis-baseline.txt"
UA_BASELINE_FILE="scripts/unused-assumption-baseline.txt"
SCAN_TMP="$(mktemp)"; SH_TMP="$(mktemp)"; UA_TMP="$(mktemp)"
trap 'rm -f "$TMP" "$AX_TMP" "$SCAN_TMP" "$SH_TMP" "$UA_TMP"' EXIT

# Signature-level scanner. One record = one file (perl -0777), $ARGV = its path.
# Emits  SELFHYP<TAB>path<TAB>decl  and  UNUSEDASSUMP<TAB>path<TAB>decl<TAB>binder.
SCAN_PROG='
  BEGIN {
    @ASSUMP = qw(rsa ddh cdh sdh dlog dl dh prf prp prg lwe mlwe mlwr rlwe sis
                 cpa cca ind euf eufcma ufcma sufcma ow owcpa hard hardness
                 sound soundness bind binding hide hiding coll collision
                 preimage kem kdf mac sig sign aead ro rom qrom prom ic ideal
                 simex zk hvzk shvzk pake ake oprf ot dpf lpn sd mq);
    %ASSUMP = map { $_ => 1 } @ASSUMP;
    $SECTY = qr/(?:Advantage|\bAdv\b|Secure|Soundness|\bSound\b|Unforge|EUFCMA|
                   UFCMA|IND_?CPA|IND_?CCA|Binding|Hiding|ZeroKnowledge|
                   Knowledge|[Nn]egligible|sdist|UCEmulates|\bPRF\b|\bPRP\b|
                   \bPRG\b|\bDDH\b|\bCDH\b|DLog|\bRSA\b|\bLWE\b|Collision|
                   Preimage|\bOW\b|hardness)/x;
  }
  sub depth_split {   # first depth-0 occurrence of a 2-char op, or a 1-char one
    my ($s, $op, $notnext) = @_;
    my @c = split //, $s; my $d = 0;
    for (my $i = 0; $i < @c; $i++) {
      if ($c[$i] =~ /[\(\[\{]/) { $d++ }
      elsif ($c[$i] =~ /[\)\]\}]/) { $d-- }
      elsif ($d == 0 && $c[$i] eq substr($op, 0, 1)) {
        if (length($op) == 2) { return $i if $i + 1 < @c && $c[$i+1] eq substr($op, 1, 1) }
        else { return $i unless $notnext && $i + 1 < @c && $c[$i+1] eq $notnext }
      }
    }
    return -1;
  }
  sub strip_foralls {
    my $t = shift; $t =~ s/\s+/ /g;
    while ($t =~ /^\s*(?:∀|Π)/) {   # literal UTF-8 bytes: the input is not decoded
      my $cm = depth_split($t, ",", "");
      last if $cm < 0;
      $t = substr($t, $cm + 1);
    }
    $t;
  }
  sub norm { my $s = shift; $s =~ s/\(\s*\w+\s*:=\s*[^()]*\)//g; $s =~ s/\s+//g; $s }
  sub is_assumption_name {
    my $n = shift; $n =~ s/^_+//; $n =~ s/^[hH](?=[_A-Z]|$)//;
    for my $s (grep { length } map { split /(?=[A-Z])/, $_ } split /_+/, $n) {
      return 1 if $ASSUMP{lc $s};
    }
    return 0;
  }
  $path = $ARGV;
  s{/-.*?-/}{}gs;                     # strip block comments AND docstrings
  s{--[^\n]*}{}g;                     # strip line comments
  $st = qr/(?:\@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+|scoped\s+|local\s+)*(?:theorem|lemma|def|instance|abbrev|axiom|structure|inductive|class|example|end\b|namespace|section|open|variable|universe|set_option|attribute|macro|macro_rules|syntax|elab|notation|deriving|import|#)/;
  for my $chunk (split /\n(?=\s*$st)/, $_) {
    next unless $chunk =~ /^\s*(?:\@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+)*(?:theorem|lemma)\s+([A-Za-z_][\w\x27.]*)/s;
    my $decl = $1;
    my $cut = depth_split($chunk, ":=", "");
    next if $cut < 0;
    my $sig = substr($chunk, 0, $cut);
    my $body = substr($chunk, $cut + 2);
    $body =~ s/\A\s+//; $body =~ s/\s+\z//;
    my $is_where = ($sig =~ /(?<![\w\x27])where\s*$/s) ? 1 : 0;

    # top-level binder groups of the signature
    my (@binders, %hty);
    my @s = split //, $sig;
    for (my $i = 0; $i < @s; $i++) {
      next unless $s[$i] =~ /[\(\[\{]/;
      my $d = 0; my $j = $i;
      for (; $j < @s; $j++) {
        if ($s[$j] =~ /[\(\[\{]/) { $d++ }
        elsif ($s[$j] =~ /[\)\]\}]/) { $d--; last if $d == 0 }
      }
      last if $j >= @s;
      my $inner = join("", @s[$i+1 .. $j-1]);
      my $cp = depth_split($inner, ":", "=");
      if ($cp >= 0) {
        my $names = substr($inner, 0, $cp);
        my $ty = substr($inner, $cp + 1);
        if ($names =~ /^[\s\w\x27\x80-\xff]*$/) {   # \x80-\xff: unicode ident chars (G₁, α)
          $names =~ s/^\s+|\s+$//g;
          for my $n (split /\s+/, $names) {
            push @binders, $n; $hty{$n} = $ty unless exists $hty{$n};
          }
        }
      }
      $i = $j;
    }
    # conclusion: after the LAST depth-0 ":" of the signature
    my $concl = "";
    { my @q = split //, $sig; my $d = 0; my $last = -1;
      for (my $k = 0; $k < @q; $k++) {
        if ($q[$k] =~ /[\(\[\{]/) { $d++ }
        elsif ($q[$k] =~ /[\)\]\}]/) { $d-- }
        elsif ($q[$k] eq ":" && $d == 0 && !($k+1 < @q && $q[$k+1] eq "=")) { $last = $k }
      }
      $concl = $last >= 0 ? substr($sig, $last + 1) : "";
      $concl =~ s/\s+/ /g;
    }

    # ---- dimension 3 ----
    if (!$is_where && $concl =~ $SECTY) {
      my $b = $body; $b =~ s/\s+/ /g;
      for my $h (grep { /^_?[hH]/ } @binders) {
        next unless $b =~ /^(?:by\s+exact\s+)?\Q$h\E(?:\s+(?:[A-Za-z_][\w\x27.]*|_))*\s*$/;
        print "SELFHYP\t$path\t$decl\n"
          if norm(strip_foralls($hty{$h})) eq norm(strip_foralls($concl));
        last;
      }
    }

    # ---- dimension 4 ----
    next if $body =~ /(?<![\w\x27.])(?:simp_all|aesop|omega|tauto|grind|linarith|nlinarith|positivity|gcongr|polyrith|duper|solve_by_elim|hammer|bound)(?![\w\x27])/;
    next if $body =~ /\[\s*\*\s*\]/;
    for my $n (@binders) {
      next unless $n =~ /^_[hH]/;
      next if $body =~ /(?<![\w\x27])\Q$n\E(?![\w\x27])/;
      next unless $hty{$n} =~ $SECTY || is_assumption_name($n);
      print "UNUSEDASSUMP\t$path\t$decl\t$n\n";
    }
  }
'
grep -rl --include='*.lean' -E '^[[:space:]]*(theorem|lemma)' CatCrypt/ \
  | xargs perl -0777 -ne "$SCAN_PROG" > "$SCAN_TMP" || true

sed -n 's/^SELFHYP\t\([^\t]*\)\t\(.*\)$/\1  \2/p' "$SCAN_TMP" | sort -u > "$SH_TMP"
sed -n 's/^UNUSEDASSUMP\t\([^\t]*\)\t\([^\t]*\)\t\(.*\)$/\1  \2  \3/p' "$SCAN_TMP" \
  | sort -u > "$UA_TMP"

SH_CURRENT="$(grep -c . "$SH_TMP" || true)"
SH_BASELINE="$(grep -m1 -oE '^[0-9]+' "$SH_BASELINE_FILE" 2>/dev/null || echo 0)"
echo "Self-hypothesis re-export theorems: current=$SH_CURRENT  baseline=$SH_BASELINE"

if [ "$SH_CURRENT" -gt "$SH_BASELINE" ]; then
  echo ""
  echo "FAIL: the self-hypothesis re-export count GREW ($SH_BASELINE -> $SH_CURRENT)."
  echo "      A NEW security theorem states one of its OWN hypotheses verbatim and"
  echo "      proves it by returning that hypothesis, so it carries no content."
  echo "      DERIVE the conclusion from a weaker, standard assumption, or state the"
  echo "      assumption as an explicit named axiom."
  echo "      NEW self-hypothesis theorem(s) (not in the baseline):"
  comm -13 <(grep -E '^CatCrypt/' "$SH_BASELINE_FILE" 2>/dev/null | sort) "$SH_TMP" | sed 's/^/        /'
  exit 1
fi

if [ "$SH_CURRENT" -lt "$SH_BASELINE" ]; then
  echo ""
  echo "Good — the self-hypothesis count SHRANK ($SH_BASELINE -> $SH_CURRENT). Auto-tightening."
  {
    echo "$SH_CURRENT"
    echo "# Security theorems whose statement IS one of their own hypotheses, proved by"
    echo "# returning it (frozen baseline; auto-tightened by"
    echo "# scripts/vacuous-theorem-ratchet.sh). First line = count; the sorted"
    echo "# \"<path>  <decl>\" list below is for diffability. Goal: count -> 0."
    cat "$SH_TMP"
  } > "$SH_BASELINE_FILE"
fi

UA_CURRENT="$(grep -c . "$UA_TMP" || true)"
UA_BASELINE="$(grep -m1 -oE '^[0-9]+' "$UA_BASELINE_FILE" 2>/dev/null || echo 0)"
echo "Underscored (unused) crypto assumptions: current=$UA_CURRENT  baseline=$UA_BASELINE"

if [ "$UA_CURRENT" -gt "$UA_BASELINE" ]; then
  echo ""
  echo "FAIL: the underscored-crypto-assumption count GREW ($UA_BASELINE -> $UA_CURRENT)."
  echo "      A NEW theorem advertises a cryptographic assumption in its signature but"
  echo "      binds it underscored, i.e. the proof never uses it and the statement holds"
  echo "      without it. Either USE the assumption (do the reduction), or DROP it from"
  echo "      the signature and say in the docstring what is actually proved."
  echo "      NEW underscored assumption(s) (not in the baseline):"
  comm -13 <(grep -E '^CatCrypt/' "$UA_BASELINE_FILE" 2>/dev/null | sort) "$UA_TMP" | sed 's/^/        /'
  exit 1
fi

if [ "$UA_CURRENT" -lt "$UA_BASELINE" ]; then
  echo ""
  echo "Good — the underscored-assumption count SHRANK ($UA_BASELINE -> $UA_CURRENT). Auto-tightening."
  {
    echo "$UA_CURRENT"
    echo "# Theorems binding an advertised crypto assumption as an UNUSED underscored"
    echo "# hypothesis (frozen baseline; auto-tightened by"
    echo "# scripts/vacuous-theorem-ratchet.sh). First line = count; the sorted"
    echo "# \"<path>  <decl>  <binder>\" list below is for diffability. Goal: count -> 0."
    cat "$UA_TMP"
  } > "$UA_BASELINE_FILE"
fi

echo "OK: vacuous-predicate, assumption-axiom, self-hypothesis and"
echo "    unused-assumption ratchets satisfied."
