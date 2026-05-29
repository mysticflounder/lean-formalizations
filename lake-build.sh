#!/usr/bin/env bash
# Memory-capped, single-flight wrapper around `lake build`.
# - Wraps `lean` with `-M $MEMORY_MB` (default 16 GB) so elaboration can't OOM
#   the machine (lake itself has no memory cap; lean takes -M, lake does not).
# - Holds a lockfile so two builds never run concurrently in this repo.
# Usage: ./lake-build.sh [lake build args...]
#   ./lake-build.sh                                              # default target
#   ./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma # one module
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LOCKFILE="${LOCKFILE:-$ROOT/.lake/lake-build.lock}"
MEMORY_MB="${MEMORY_MB:-16384}"

REAL_LAKE="${REAL_LAKE:-$(command -v lake)}"
REAL_LEAN="${REAL_LEAN:-$(command -v lean)}"
if [[ -z "$REAL_LAKE" || -z "$REAL_LEAN" ]]; then
  echo "lake/lean not on PATH. Install via elan: https://leanprover-community.github.io/install/" >&2
  exit 1
fi

mkdir -p "$(dirname "$LOCKFILE")"

acquire_lock() {
  while true; do
    if (set -o noclobber; printf '%s\n' "$$" >"$LOCKFILE") 2>/dev/null; then
      return 0
    fi
    if IFS= read -r lock_pid <"$LOCKFILE" && [[ "$lock_pid" =~ ^[0-9]+$ ]] &&
        kill -0 "$lock_pid" 2>/dev/null; then
      echo "another lake build is already running (pid $lock_pid): $LOCKFILE" >&2
      exit 1
    fi
    rm -f "$LOCKFILE"
  done
}

WRAP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/lf-lake-wrap.XXXXXX")"
cleanup() { rm -rf "$WRAP_DIR"; rm -f "$LOCKFILE"; }
trap cleanup EXIT INT TERM HUP

acquire_lock

cat >"$WRAP_DIR/lean" <<EOF
#!/usr/bin/env bash
exec "$REAL_LEAN" -M "$MEMORY_MB" "\$@"
EOF
chmod 755 "$WRAP_DIR/lean"

cd "$ROOT"
PATH="$WRAP_DIR:$PATH" "$REAL_LAKE" build "$@"
