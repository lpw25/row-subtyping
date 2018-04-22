OCAMLOPT=ocamlfind ocamlopt
OCAMLLEX=ocamllex
MENHIR=menhir

CFLAGS=-package menhirLib
LFLAGS=-linkpkg -package menhirLib

MODULES=ast.cmx parser.cmx parserMessages.cmx lexer.cmx main.cmx

all: prototype

ast.cmi: ast.mli
	${OCAMLOPT} ${CFLAGS} -c ast.mli

ast.cmx: ast.ml ast.cmi
	${OCAMLOPT} ${CFLAGS} -c ast.ml

lexer.ml: lexer.mll
	${OCAMLLEX} lexer.mll

lexer.cmi: lexer.mli parser.cmi
	${OCAMLOPT} ${CFLAGS} -c lexer.mli

lexer.cmx lexer.o: lexer.ml lexer.cmi parser.cmi
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

main.cmx: main.ml ast.cmi lexer.cmi parser.cmi parserMessages.cmi
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
