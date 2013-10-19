#!/usr/bin/make -f

SOURCES := \
	misc.ml \
	term.ml \
	parser.mly \
	lexer.mll \
	solver.ml \
	main.ml

RESULT := ipc_solver

OCAMLFLAGS := -w Aelyz

include OCamlMakefile

