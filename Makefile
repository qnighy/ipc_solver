#!/usr/bin/make -f

SOURCES := \
	term.ml \
	parser.mly \
	lexer.mll \
	solver.ml \
	lf_proof.ml \
	nj_proof.ml \
	kripke.mli kripke.ml \
	main.ml

RESULT := ipc_solver

OCAMLFLAGS := -w Aelyz

include OCamlMakefile

