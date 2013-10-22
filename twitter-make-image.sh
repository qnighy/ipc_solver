#!/bin/bash
ulimit -St 10
ulimit -Sf 300000
ulimit -Sv 512000
cd workdir && \
../ipc_solver < $1-prop.txt >$1.tex 2>$1.log && \
latex -halt-on-error $1.tex >>$1.log 2>&1 && \
dvipng $1.dvi
