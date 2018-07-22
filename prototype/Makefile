OCAMLOPT=ocamlfind ocamlopt -g -w -40
OCAMLLEX=ocamllex
MENHIR=menhir

CFLAGS=-package menhirLib
LFLAGS=-linkpkg -package menhirLib

MODULES=ast.cmx parser.cmx parserMessages.cmx lexer.cmx types.cmx infer.cmx main.cmx

.PHONY: all clean check-errors

all: prototype

ast.cmi: ast.mli
	${OCAMLOPT} ${CFLAGS} -c ast.mli

ast.cmx: ast.ml ast.cmi
	${OCAMLOPT} ${CFLAGS} -c ast.ml

lexer.ml: lexer.mll
	${OCAMLLEX} lexer.mll

lexer.cmi: lexer.mli parser.cmi
	${OCAMLOPT} ${CFLAGS} -c lexer.mli

lexer.cmx lexer.o: lexer.ml lexer.cmi parser.cmi parser.cmx
	${OCAMLOPT} ${CFLAGS} -c lexer.ml

parser.ml parser.mli: parser.mly
	${MENHIR} --table parser.mly

parser.cmi: parser.mli ast.cmi
	${OCAMLOPT} ${CFLAGS} -c parser.mli

parser.cmx parser.o: parser.ml parser.cmi ast.cmi
	${OCAMLOPT} ${CFLAGS} -c parser.ml

parserMessages.ml: parser.mly parser.messages
	${MENHIR} --compile-errors parser.messages parser.mly > parserMessages.ml

parserMessages.cmi: parserMessages.mli
	${OCAMLOPT} ${CFLAGS} -c parserMessages.mli

parserMessages.cmx parserMessages.o: parserMessages.ml parserMessages.cmi
	${OCAMLOPT} ${CFLAGS} -c parserMessages.ml

types.cmi: types.mli
	${OCAMLOPT} ${CFLAGS} -c types.mli

types.cmx types.o: types.ml types.cmi
	${OCAMLOPT} ${CFLAGS} -c types.ml

infer.cmi: infer.mli ast.cmi types.cmi
	${OCAMLOPT} ${CFLAGS} -c infer.mli

infer.cmx infer.o: infer.ml infer.cmi ast.cmi types.cmi ast.cmx types.cmx
	${OCAMLOPT} ${CFLAGS} -c infer.ml

main.cmx: main.ml ast.cmi lexer.cmi parser.cmi parserMessages.cmi infer.cmi types.cmi \
          ast.cmx lexer.cmx parser.cmx parserMessages.cmx infer.cmx types.cmx
	${OCAMLOPT} ${CFLAGS} -c main.ml

prototype: ${MODULES}
	${OCAMLOPT} ${LFLAGS} -o prototype ${MODULES}

clean:
	-rm *.cmx
	-rm *.cmi
	-rm *.o
	-rm parser.ml
	-rm parser.mli
	-rm lexer.ml

parser.new-messages: parser.mly
	${MENHIR} --list-errors parser.mly > parser.new-messages

check-errors: parser.messages parser.new-messages
	${MENHIR} --compare-errors parser.new-messages --compare-errors parser.messages parser.mly
