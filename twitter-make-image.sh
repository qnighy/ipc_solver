#!/bin/bash
ulimit -St 10
ulimit -Sf 300000
ulimit -Sv 512000
cd workdir && \
../ipc_solver < $1-prop.txt >$1.tex 2>$1.log && \
pdflatex $1.tex >>$1.log 2>&1 && \
convert -density 300 $1.pdf -quality 90 -limit area 0 -resize '4000>' \
  -fill white -opaque none -alpha off $1.png 2>> $1.log
