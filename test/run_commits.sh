#!/usr/bin/env bash
# For each Mathlib commit given, build its tree from Mathlib's cache, run leanchecker-inc with the verdict store and
# the id cache, and delete the tree. Logs go to test/work/run-<commit>.log. Usage: test/run_commits.sh COMMIT...
set -euo pipefail
cd "$(dirname "$0")/.."
W=test/work
export LEAN_SYSROOT=~/.elan/toolchains/leanprover--lean4---v4.37.0-rc1
for c in "$@"; do
  full=$(git -C $W/mathlib-src rev-parse "$c")
  short=${full:0:8}
  LEAN_PATH=$(python3 test/mathlib_tree.py "$full")
  export LEAN_PATH
  (cd $W && nice -n 19 /usr/bin/time -f "wall %e s, user %U s, peak %M KB" ../../.lake/build/bin/leanchecker-inc \
      --store mathlib.store --id-cache mathlib.ids --log-checked "checked-$short.txt" Mathlib) > "$W/run-$short.log" 2>&1 \
    && echo "exit 0" >> "$W/run-$short.log" || echo "exit $?" >> "$W/run-$short.log"
  rm -rf "${W:?}/tree-$short"
  echo "== $short"; tail -5 "$W/run-$short.log"
done
