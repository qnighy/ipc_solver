#!/usr/bin/make -f

SOURCES := \
	term.mli term.ml \
	parser.mly \
	lexer.mll \
	solver.mli solver.ml \
	lf_proof.mli lf_proof.ml \
	nj_proof.mli nj_proof.ml \
	sat.mli sat.ml \
	kripke.mli kripke.ml \
	ppHaskell.mli ppHaskell.ml \
	main.ml

RESULT := ipc_solver

OCAMLFLAGS := -w Aelyz

include OCamlMakefile

