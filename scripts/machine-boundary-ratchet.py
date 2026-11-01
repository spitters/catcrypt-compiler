#!/usr/bin/env python3
"""Machine-boundary ratchet: the import edges between the machine library and the rest.

The machine library is the set of modules whose tier (scripts/machine-boundary-tiers.txt)
is listed on that file's `machine:` line: machine models, decoders and encoders, the flag
and address machines, the ISA records, ascent, separation logic, constant time, the ARM
and RISC-V back ends and the x86 back half. The script reads the import headers of every
module of the workspace (catcrypt-compiler, CatCrypt-core, SSProve-lean, ParamTransfer,
hax-lean, nominal-lean; module name = path, `.lake` skipped) and computes

  edge   a machine module imports a module whose tier is neither a machine tier nor an
         allowed tier (`allowed:`, the Lean toolchain and Mathlib);
  escape a machine module whose transitive import closure contains such a module;
  closed a machine module whose closure stays within the machine and allowed tiers;
  cycle  a module outside the machine tiers, reached from a machine module, imports a
         machine module (a cycle between tiers: it must move down or lose the import).

The default mode compares these sets with scripts/machine-boundary-baseline.txt. It fails
when an edge, an escaping module or a cycle edge appears that the baseline does not list,
and it reports, without failing, entries of the baseline that are gone; `--write` records
the smaller baseline. A renamed or new machine module appears as new entries: rewrite the
baseline in the commit that adds it, after checking that its edges are intended.

  python3 -I scripts/machine-boundary-ratchet.py            check against the baseline
  python3 -I scripts/machine-boundary-ratchet.py --write    write the baseline
  python3 -I scripts/machine-boundary-ratchet.py --list     print the edges and cycles
  python3 -I scripts/machine-boundary-ratchet.py --report [--top N]
        rank the edge targets by the lines their closure pulls into the library

Sibling checkouts are found next to this repository; CATCRYPT_WORKSPACE overrides the
parent directory and CATCRYPT_DEV_ROOT the SSProve-lean checkout. This repository and
CatCrypt-core are required; a missing other checkout is reported and its modules count as
unresolved (no module of this repository or CatCrypt-core imports a dev module, so the
dev tree changes no entry). Families are read from SSProve-lean
scripts/code-map/annotations.txt (`--annotations` overrides). The script uses the Python
standard library only and loads no Lean.
"""

import argparse
import collections
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
COMP = os.path.dirname(HERE)
WS = os.environ.get('CATCRYPT_WORKSPACE', os.path.dirname(COMP))
DEV = os.environ.get('CATCRYPT_DEV_ROOT', os.path.join(WS, 'SSProve-lean'))

# repo letter -> (checkout, scanned paths relative to it, required)
REPOS = {
    'C': (COMP, ('CatCrypt', 'HaxAscent'), True),
    'K': (os.path.join(WS, 'CatCrypt-core'), ('CatCryptCore', 'CatCryptCore.lean'), True),
    'D': (DEV, ('CatCrypt', 'CatCrypt.lean', 'CatCryptAll.lean'), False),
    'P': (os.path.join(WS, 'ParamTransfer'),
          ('Transfer', 'Transfer.lean', 'ReprTransfer.lean', 'ReprTransferExpr.lean'), False),
    'H': (os.path.join(WS, 'hax-lean'), ('HaxLean', 'HaxLean.lean'), False),
    'N': (os.path.join(WS, 'nominal-lean'),
          ('Nominal', 'NominalIris', 'Nominal.lean', 'NominalIris.lean'), False),
}
TIERS = os.path.join(HERE, 'machine-boundary-tiers.txt')
BASELINE = os.path.join(HERE, 'machine-boundary-baseline.txt')
ANNOTATIONS = os.path.join(DEV, 'scripts', 'code-map', 'annotations.txt')
HEADER_WORDS = ('module', 'prelude', 'public', 'meta', 'private')
BLOCK = re.compile(r'/-|-/')
WORD = re.compile(r'\S+')
SECTIONS = ('edge', 'escape', 'closed', 'cycle')


class Module:
    __slots__ = ('repo', 'rel', 'imports', 'lines', 'family')

    def __init__(self, repo, rel, imports, lines):
        self.repo, self.rel, self.imports, self.lines = repo, rel, imports, lines
        self.family = None


def die(msg):
    print(f'machine-boundary: {msg}', file=sys.stderr)
    sys.exit(2)


def header_imports(text):
    """The modules named by the `import` commands of a Lean header.

    The header is everything before the first command other than `module`, `prelude` and
    `[public] [meta] import [all] M`; comments are skipped, so an `import` in a docstring
    or in the body is not read."""
    i, n, out, want = 0, len(text), [], False
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j + 1
        elif text.startswith('/-', i):
            depth, i = 1, i + 2
            while depth:
                m = BLOCK.search(text, i)
                if not m:
                    return out
                depth += 1 if m.group(0) == '/-' else -1
                i = m.end()
        else:
            m = WORD.match(text, i)
            tok = re.split(r'--|/-', m.group(0))[0]
            i = m.start() + len(tok)
            if want:
                if tok != 'all':
                    out.append(tok)
                    want = False
            elif tok == 'import':
                want = True
            elif tok not in HEADER_WORDS:
                break
    return out


def scan():
    mods, missing = {}, []
    for repo, (root, paths, required) in REPOS.items():
        if not os.path.isdir(root):
            if required:
                die(f'checkout {root} not found (set CATCRYPT_WORKSPACE or CATCRYPT_DEV_ROOT)')
            missing.append(root)
            continue
        for p in paths:
            full = os.path.join(root, p)
            if p.endswith('.lean'):
                files = [full] if os.path.isfile(full) else []
            else:
                files = []
                for dp, dns, fns in os.walk(full):
                    dns[:] = [d for d in dns if d != '.lake']
                    files += [os.path.join(dp, f) for f in fns if f.endswith('.lean')]
            for f in files:
                rel = os.path.relpath(f, root)
                name = rel[:-5].replace(os.sep, '.')
                with open(f, 'rb') as fh:
                    text = fh.read().decode('utf-8', 'replace')
                lines = text.count('\n') + (0 if not text or text.endswith('\n') else 1)
                if name in mods:
                    print(f'machine-boundary: warning: {name} in repos {mods[name].repo} and '
                          f'{repo}; the first is used', file=sys.stderr)
                    continue
                mods[name] = Module(repo, rel, header_imports(text), lines)
    for root in missing:
        print(f'machine-boundary: warning: {root} not found; its modules count as unresolved',
              file=sys.stderr)
    return mods


def glob_re(g):
    """`**` matches across directories, `*` and `?` within one path component."""
    out, i = [], 0
    while i < len(g):
        if g.startswith('**', i):
            out.append('.*')
            i += 2
        elif g[i] == '*':
            out.append('[^/]*')
            i += 1
        elif g[i] == '?':
            out.append('[^/]')
            i += 1
        else:
            out.append(re.escape(g[i]))
            i += 1
    return re.compile(''.join(out) + r'\Z')


def read_families(path, mods):
    """Assign each module of the compiler and dev trees its code-map family."""
    if not os.path.isfile(path):
        die(f'annotation file {path} not found (--annotations overrides)')
    rows = []
    with open(path) as fh:
        for line in fh:
            if not line.strip() or line.startswith('#'):
                continue
            t = [f.strip() for f in line.rstrip('\n').split('|')]
            if len(t) < 3:
                die(f'{path}: malformed row: {line.strip()[:80]}')
            rows.append((t[0], t[1], [glob_re(g) for g in t[2].split()]))
    for m in mods.values():
        for label, repo, pats in rows:
            if repo == m.repo and any(p.match(m.rel) for p in pats):
                m.family = label
                break
    return {label for label, _, _ in rows}


def read_tiers(path, labels):
    machine, allowed, rules = None, None, []
    with open(path) as fh:
        for n, line in enumerate(fh, 1):
            s = line.strip()
            if not s or s.startswith('#'):
                continue
            if s.startswith('machine:'):
                machine = set(s[8:].split())
                continue
            if s.startswith('allowed:'):
                allowed = set(s[8:].split())
                continue
            t = s.split(None, 2)
            if len(t) != 3 or t[1] not in ('family', 'glob', 'name'):
                die(f'{path}:{n}: expected `<tier> family|glob|name <pattern>`')
            tier, kind, pat = t
            if kind == 'family':
                if pat not in labels:
                    die(f'{path}:{n}: no code-map family is labelled {pat!r}')
                rules.append((tier, kind, pat))
            elif kind == 'glob':
                if pat[1:2] != ':' or pat[0] not in REPOS:
                    die(f'{path}:{n}: a glob is written <repo>:<path glob>')
                rules.append((tier, kind, (pat[0], glob_re(pat[2:]))))
            else:
                rules.append((tier, kind, pat))
    if not machine:
        die(f'{path}: no `machine:` line')
    return machine, allowed or set(), rules


def classify(name, mods, rules):
    m = mods.get(name)
    for tier, kind, pat in rules:
        if kind == 'name':
            if name == pat or name.startswith(pat + '.'):
                return tier
        elif m is None:
            continue
        elif kind == 'family':
            if m.family == pat:
                return tier
        elif m.repo == pat[0] and pat[1].match(m.rel):
            return tier
    return 'other' if m else 'unresolved'


def closure(mods, starts):
    seen, stack = set(), list(starts)
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        if x in mods:
            stack.extend(mods[x].imports)
    return seen


def analyse(mods, machine_tiers, allowed, rules):
    names = set(mods)
    for m in mods.values():
        names.update(m.imports)
    tier = {x: classify(x, mods, rules) for x in names}
    machine = {x for x in mods if tier[x] in machine_tiers}
    outside = {x for x in names if tier[x] not in machine_tiers and tier[x] not in allowed}
    edges = {(s, t) for s in machine for t in mods[s].imports if t in outside}
    # A module escapes when an outside module is reachable from it: search backwards
    # from every outside module.
    rev = collections.defaultdict(set)
    for s, m in mods.items():
        for t in m.imports:
            rev[t].add(s)
    taint, stack = set(), list(outside)
    while stack:
        x = stack.pop()
        if x in taint:
            continue
        taint.add(x)
        stack.extend(rev.get(x, ()))
    escape = machine & taint
    reach = closure(mods, machine)
    cycles = {(s, t) for s in reach if s in outside and s in mods
              for t in mods[s].imports if t in machine}
    return {'tier': tier, 'machine': machine, 'outside': outside, 'reach': reach,
            'edge': edges, 'escape': escape, 'closed': machine - escape, 'cycle': cycles}


def entries(a):
    """The baseline lines of each section: `A -> B` for an edge, the name for a module."""
    def fmt(v):
        return f'{v[0]} -> {v[1]}' if isinstance(v, tuple) else v
    return {sec: {fmt(v) for v in a[sec]} for sec in SECTIONS}


def lines_of(mods, xs):
    return sum(mods[x].lines for x in xs if x in mods)


def summary(mods, a):
    machine = a['machine']
    importers = {s for s, _ in a['edge']}
    targets = {t for _, t in a['edge']}
    pulled = (a['reach'] & a['outside']) - machine
    return (f"{len(machine)} machine modules ({lines_of(mods, machine):,} lines); "
            f"{len(importers)} import outside the machine tiers "
            f"({len(a['edge'])} edges to {len(targets)} targets); "
            f"{len(a['escape'])} escape transitively, {len(a['closed'])} closed "
            f"({lines_of(mods, a['closed']):,} lines); "
            f"{len(a['cycle'])} cycle edges; the closure adds {len(pulled)} outside "
            f"modules ({lines_of(mods, pulled):,} lines)")


def read_baseline(path):
    if not os.path.isfile(path):
        die(f'baseline {path} not found; write it with --write')
    out = {sec: set() for sec in SECTIONS}
    with open(path) as fh:
        for n, line in enumerate(fh, 1):
            s = line.strip()
            if not s or s.startswith('#'):
                continue
            sec, _, rest = s.partition(' ')
            if sec not in out:
                die(f'{path}:{n}: unknown section {sec!r}')
            out[sec].add(rest.strip())
    return out


def write_baseline(path, cur, summ):
    with open(path, 'w') as fh:
        fh.write('# Machine-boundary baseline, written by scripts/machine-boundary-ratchet.py '
                 '--write.\n'
                 '# edge: a machine module imports a module outside the machine and allowed '
                 'tiers.\n'
                 '# escape: a machine module whose import closure leaves those tiers; '
                 'closed: one whose closure does not.\n'
                 '# cycle: a module outside the machine tiers, reached from a machine module, '
                 'imports a machine module.\n'
                 '# Tiers: scripts/machine-boundary-tiers.txt.\n'
                 f'# {summ}\n')
        for sec in SECTIONS:
            fh.write('\n')
            for e in sorted(cur[sec]):
                fh.write(f'{sec} {e}\n')


def check(cur, base):
    new = {sec: cur[sec] - base[sec] for sec in ('edge', 'escape', 'cycle')}
    gone = {sec: base[sec] - cur[sec] for sec in ('edge', 'escape', 'cycle')}
    for e in sorted(new['edge']):
        print(f'new edge: {e}')
    for e in sorted(new['escape']):
        why = 'a closed module now escapes' if e in base['closed'] else 'a new machine module'
        print(f'new escape: {e} ({why})')
    for e in sorted(new['cycle']):
        print(f'new cycle edge: {e}')
    nnew = sum(map(len, new.values()))
    ngone = sum(map(len, gone.values()))
    if ngone:
        print(f"machine-boundary: gone from the baseline: {len(gone['edge'])} edges, "
              f"{len(gone['escape'])} escaping modules, {len(gone['cycle'])} cycle edges; "
              f"--write records the smaller baseline")
    if nnew:
        print(f'machine-boundary: FAIL: {nnew} entries not in the baseline (above). Remove the '
              f'import, or move the module to the tier it belongs to; if the entries are '
              f'intended (a renamed or new machine module), rewrite the baseline with --write.')
        return 1
    print('machine-boundary: ok')
    return 0


def list_edges(a):
    tier = a['tier']
    print(f"# {len(a['edge'])} edges leaving the machine tiers (source -> target  [target tier])")
    for s, t in sorted(a['edge']):
        print(f'{s} -> {t}  [{tier[t]}]')
    print(f"\n# {len(a['cycle'])} cycle edges (outside module -> machine module  [source tier])")
    for s, t in sorted(a['cycle']):
        print(f'{s} -> {t}  [{tier[s]}]')


def report(mods, a, top):
    tier, machine, outside = a['tier'], a['machine'], a['outside']
    by_target = collections.defaultdict(set)
    for s, t in a['edge']:
        by_target[t].add(s)
    pulled, reached_by = {}, collections.Counter()
    for t in by_target:
        c = (closure(mods, [t]) & outside) - machine
        pulled[t] = c
        reached_by.update(c)
    print('\nEdges and targets by target tier:')
    per_tier = collections.defaultdict(lambda: [0, 0])
    for s, t in a['edge']:
        per_tier[tier[t]][0] += 1
    for t in by_target:
        per_tier[tier[t]][1] += 1
    for k, (ne, nt) in sorted(per_tier.items(), key=lambda kv: -kv[1][0]):
        print(f'  {k:<12} {ne:5d} edges  {nt:4d} targets')
    print('\nMachine modules by family:')
    fam = collections.defaultdict(lambda: [0, 0, 0, 0])
    importers = {s for s, _ in a['edge']}
    for x in machine:
        row = fam[(tier[x], mods[x].family or '-')]
        row[0] += 1
        row[1] += mods[x].lines
        row[2] += x in importers
        row[3] += x in a['escape']
    print(f'  {"modules":>7} {"lines":>8} {"direct":>6} {"escape":>6}  tier / family')
    for (k, f), (n, ln, d, e) in sorted(fam.items()):
        print(f'  {n:7d} {ln:8,d} {d:6d} {e:6d}  {k} / {f}')
    print(f'\nTop {top} edge targets by the lines of their closure outside the machine tiers '
          f'(pulled), the part reached through no other target (only), and their importers:')
    print(f'  {"pulled":>9} {"only":>9} {"imp":>4}  target [tier]  <- importers')
    ranked = sorted(by_target, key=lambda t: (-lines_of(mods, pulled[t]), t))
    for t in ranked[:top]:
        only = [x for x in pulled[t] if reached_by[x] == 1]
        srcs = sorted(by_target[t])
        tail = ', '.join(s.rsplit('.', 1)[-1] for s in srcs[:3]) + (', ...' if len(srcs) > 3 else '')
        print(f'  {lines_of(mods, pulled[t]):9,d} {lines_of(mods, only):9,d} {len(srcs):4d}  '
              f'{t} [{tier[t]}]  <- {tail}')
    unresolved = sorted({t for _, t in a['edge'] if tier[t] == 'unresolved'})
    if unresolved:
        print('\nTargets that resolve to no scanned module and match no `name` rule:')
        for t in unresolved:
            print(f'  {t}')


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    g = ap.add_mutually_exclusive_group()
    g.add_argument('--write', action='store_true', help='write the baseline')
    g.add_argument('--list', action='store_true', help='print the edges and cycle edges')
    g.add_argument('--report', action='store_true', help='rank the edge targets')
    ap.add_argument('--top', type=int, default=30, help='targets shown by --report')
    ap.add_argument('--tiers', default=TIERS)
    ap.add_argument('--baseline', default=BASELINE)
    ap.add_argument('--annotations', default=ANNOTATIONS)
    args = ap.parse_args()

    if not os.path.isfile(args.annotations):
        print(f'machine-boundary: skipped, no family annotation file {args.annotations} '
              '(it is part of the development tree; --annotations names another)')
        return 0

    t0 = time.monotonic()
    mods = scan()
    labels = read_families(args.annotations, mods)
    machine_tiers, allowed, rules = read_tiers(args.tiers, labels)
    a = analyse(mods, machine_tiers, allowed, rules)
    cur = entries(a)
    summ = summary(mods, a)
    print(f'machine-boundary: {summ} ({time.monotonic() - t0:.1f} s)')
    if args.write:
        write_baseline(args.baseline, cur, summ)
        print(f'machine-boundary: wrote {os.path.relpath(args.baseline, COMP)}')
        return 0
    if args.list:
        list_edges(a)
        return 0
    if args.report:
        report(mods, a, args.top)
        return 0
    return check(cur, read_baseline(args.baseline))


if __name__ == '__main__':
    sys.exit(main())
