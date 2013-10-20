#!/bin/sh
./ipc_solver > $1.tex
pdflatex $1.tex
# convert -density 300 $1.pdf -quality 90 -limit area 0 -resize 1680 $1.png
# convert -density 300 $1.pdf -quality 90 -limit area 0 $1.png
convert -density 300 $1.pdf -quality 90 -limit area 0 -resize '1680>' $1.png
# gs -sDEVICE=jpeg -o $1.jpg -dJPEGQ=80 -r200x200 -g1653x2339 $1.pdf
