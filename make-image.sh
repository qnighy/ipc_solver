#!/bin/bash
ulimit -St 10
ulimit -Sf 300000
ulimit -Sv 512000
name="test"
./ipc_solver > $name.tex && \
latex -halt-on-error $name.tex && \
dvipng $name.dvi
