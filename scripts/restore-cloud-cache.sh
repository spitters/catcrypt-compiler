#!/usr/bin/env bash
# ci-gates-local: network (reads a release of the cache repository; builds nothing)
# Restores the Lean build outputs of this package and of the packages it shares with the dev
# workspace from a dev cache release of spitters/catcrypt-cloud-cache, so that CI elaborates
# only the modules changed since the cache snapshot.
#
# The release holds devbuild.tar.zst.NN, a tar of the build directories of the dev workspace
# (one top-level directory per repository), and SHA256SUMS. The parts are streamed into tar and
# never stored. Extracted: this package's .lake/build, and the builds of CatCrypt-core,
# hax-lean, ParamTransfer, nominal-lean, Veir and CompPoly into .lake/packages/<name>. Run it
# after `lake update`, so that the package directories exist. A build whose sources differ
# from the snapshot is rebuilt by Lake from its trace; the build that follows is the verdict.
#
# Needs zstd and GH_TOKEN with read access to the cache repository; without either it restores
# nothing and exits 0, so the build that follows elaborates from source. CATCRYPT_DEV_TAG selects
# the release (default: the latest). Exit 1 on a checksum mismatch. On GitHub Actions
# (GITHUB_ACTIONS=true) the extracted builds are then removed; elsewhere they are kept, since
# the directories also hold the builds of a local checkout, which a removal would delete.
set -euo pipefail
command -v zstd >/dev/null 2>&1 \
  || { echo "restore-cloud-cache: zstd not found; nothing restored" >&2; exit 0; }
[ -n "${GH_TOKEN:-}" ] \
  || { echo "restore-cloud-cache: GH_TOKEN not set; nothing restored" >&2; exit 0; }
REPO=spitters/catcrypt-cloud-cache
TAG="${CATCRYPT_DEV_TAG:-$(gh api "repos/$REPO/releases/latest" -q .tag_name)}"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT

gh api "repos/$REPO/releases/tags/$TAG" -q '.assets[] | "\(.id) \(.name)"' | sort -k2 > "$T/assets"
sums_id=$(awk '$2 == "SHA256SUMS" {print $1}' "$T/assets")
[ -n "$sums_id" ] || { echo "restore-cloud-cache: release $TAG has no SHA256SUMS" >&2; exit 1; }
gh api -H 'Accept: application/octet-stream' "repos/$REPO/releases/assets/$sums_id" > "$T/SHA256SUMS"

PK=.lake/packages
DIRS=(.lake/build "$PK/catcryptCore/.lake/build" "$PK/hax-lean/.lake/build"
  "$PK/paramTransfer/.lake/build" "$PK/nominalLean/.lake/build" "$PK/Veir/.lake/build"
  "$PK/CompPoly/.lake/build")

: > "$T/got"
while read -r id name; do
  case "$name" in devbuild.tar.zst.*) ;; *) continue ;; esac
  gh api -H 'Accept: application/octet-stream' "repos/$REPO/releases/assets/$id" \
    | tee >(sha256sum | sed "s#-\$#$name#" >> "$T/got")
done < "$T/assets" | zstd -d -q | tar -xf - --wildcards \
  --transform 's#^catcrypt-compiler/\.lake/#.lake/#' \
  --transform "s#^CatCrypt-core/#$PK/catcryptCore/#" \
  --transform "s#^hax-lean/#$PK/hax-lean/#" \
  --transform "s#^ParamTransfer/#$PK/paramTransfer/#" \
  --transform "s#^nominal-lean/#$PK/nominalLean/#" \
  --transform "s#^SSProve-lean/\.lake/packages/#$PK/#" \
  'catcrypt-compiler/.lake/build/*' 'CatCrypt-core/.lake/build/*' 'hax-lean/.lake/build/*' \
  'ParamTransfer/.lake/build/*' 'nominal-lean/.lake/build/*' \
  'SSProve-lean/.lake/packages/Veir/.lake/build/*' \
  'SSProve-lean/.lake/packages/CompPoly/.lake/build/*' || true

sleep 2
want=$(grep ' devbuild.tar.zst.' "$T/SHA256SUMS" | tr -s ' ' | sort)
got=$(tr -s ' ' < "$T/got" | sort)
if [ "$want" != "$got" ]; then
  if [ "${GITHUB_ACTIONS:-}" = true ]; then
    echo "restore-cloud-cache: checksum mismatch in $TAG; removing the extracted builds" >&2
    rm -rf "${DIRS[@]}"
  else
    echo "restore-cloud-cache: checksum mismatch in $TAG; the extracted builds are kept, outside" \
      "GitHub Actions nothing is removed" >&2
  fi
  exit 1
fi
for d in "${DIRS[@]}"; do
  [ -d "$d" ] && echo "restored $d ($(find "$d" -name '*.olean' | wc -l) oleans)"
done
echo "restore-cloud-cache: $TAG restored"
