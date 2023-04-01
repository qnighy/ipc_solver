#!/bin/bash
set -ue
name=$1; shift

ulimit -St 10
ulimit -Sf 300000
ulimit -Sv 512000
cd workdir_mastodon
../ipc_solver --latex $name.tex "$@" < $name-prop.txt > $name.out 2>$name.log
latex -halt-on-error $name.tex >>$name.log 2>&1
dvipng $name.dvi
