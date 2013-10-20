#!/bin/sh
ulimit -t 10
ulimit -f 300000
ulimit -l 512000
./ipc_solver > $1.tex && \
pdflatex $1.tex -output-directory `dirname $1` && \
convert -density 300 $1.pdf -quality 90 -limit area 0 -resize '4000>' \
  -fill white -opaque none -alpha off $1.png
