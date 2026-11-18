#!/bin/bash
# Usage: $0 <scratch-dir> <name> [ipc_solver options...]
set -ue
workdir=$1; shift
name=$1; shift
# ipc_solver is built next to this script.
srcdir=$(dirname "$(readlink -f "$0")")

ulimit -St 10
ulimit -Sf 300000
ulimit -Sv 512000
cd "$workdir"
"$srcdir/ipc_solver" --latex $name.tex "$@" < $name-prop.txt > $name.out 2>$name.log
latex -halt-on-error $name.tex >>$name.log 2>&1
dvipng $name.dvi
