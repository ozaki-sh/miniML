
# Usage:
# Type 'make bc' for byte code.
# Type 'make nc' for native code.
# Type 'make dc' for code with debugging information.
# For more detail, see http://mmottl.github.io/ocaml-makefile/

SOURCES=mySet.mli mySet.ml syntax.ml debug.ml parser.mly lexer.mll environment.mli environment.ml rev_environment.mli rev_environment.ml store.mli store.ml eval.ml typing.ml define.ml main.ml
RESULT=miniml
YFLAGS=-v
OCAMLYACC=menhir

all: nc

include OCamlMakefile
