#!/usr/bin/env bash
# Classical conservativity check.
#
# Rebuilds the whole project -- minus counterexamples/ -- against the
# classical AProp kernel (classical/aprop_kernel.v: SProp excluded middle,
# Classicality = decidability) in an isolated tree under .build/classical/.
# The default constructive build, and rocqtui's view of the project, are
# untouched.
#
# Everything that compiles here is a theorem of the classical model too,
# i.e. compatible with classical mathematics.  counterexamples/ is excluded
# by design: those files construct anticlassical witnesses and must fail
# against this kernel.
set -euo pipefail
cd "$(dirname "$0")/.."
B=.build/classical
mkdir -p "$B"

rsync -a --delete --prune-empty-dirs \
  --exclude='/.git/' \
  --exclude='/.build/' \
  --exclude='/counterexamples/' \
  --exclude='/interfaces/aprop_kernel.v' \
  --include='*/' --include='*.v' --exclude='*' \
  ./ "$B/"

# cmp-guarded installs: don't churn mtimes, keep the build incremental
install_if_changed() { cmp -s "$1" "$2" 2>/dev/null || cp "$1" "$2"; }

install_if_changed classical/aprop_kernel.v "$B/interfaces/aprop_kernel.v"

{ grep -v '^counterexamples/' _RocqProject; echo classical/sanity.v; } > "$B/_RocqProject.new"
install_if_changed "$B/_RocqProject.new" "$B/_RocqProject"
rm -f "$B/_RocqProject.new"

cd "$B"
rocq makefile -f _RocqProject -o Makefile 2>/dev/null
make -j"$(nproc)" all
echo "classical build OK"
