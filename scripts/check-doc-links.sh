#!/usr/bin/env bash
# Doc-link gate: every relative file link in the package's Markdown must resolve.
# A shared doc set rots silently when a referenced file is renamed or removed; this
# turns "the links still work" from a manual assumption into a checked fact. It
# inspects only RELATIVE links to local files (.md/.lean/.cff/.toml/.sh/.png); http(s)
# links, anchors, and mailto are out of scope. Exit 1 on any dangling link.
set -uo pipefail
cd "$(git rev-parse --show-toplevel 2>/dev/null)" || exit 1

broken=0
while IFS= read -r f; do
  d=$(dirname "$f")
  # extract ](target) where target is a local file path (no scheme, no leading #)
  grep -oE '\]\(([^)#][^)]*\.(md|lean|cff|toml|sh|png|svg|json))\)' "$f" 2>/dev/null \
    | sed -E 's/^\]\((.*)\)$/\1/' | while IFS= read -r tgt; do
      case "$tgt" in http*|mailto:*|/*) continue ;; esac
      tgt="${tgt%%#*}"                       # strip any #anchor
      [ -z "$tgt" ] && continue
      if [ ! -e "$d/$tgt" ] && [ ! -e "$tgt" ]; then
        echo "  BROKEN: $f -> $tgt"
        echo x >> /tmp/.doclink_broken.$$
      fi
    done
done < <(git ls-files '*.md' 2>/dev/null)

[ -f /tmp/.doclink_broken.$$ ] && broken=$(wc -l < /tmp/.doclink_broken.$$) && rm -f /tmp/.doclink_broken.$$
if [ "${broken:-0}" -gt 0 ]; then
  echo "FAIL: $broken dangling doc link(s) above." >&2
  exit 1
fi
echo "doc-links: all Markdown file links resolve."
