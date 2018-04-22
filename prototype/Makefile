OCAMLOPT=ocamlopt
OCAMLLEX=ocamllex
MENHIR=menhir

MODULES=ast.cmx parser.cmx lexer.cmx main.cmx

all: prototype

ast.cmi: ast.mli
	${OCAMLOPT} -c ast.mli

ast.cmx: ast.ml ast.cmi
	${OCAMLOPT} -c ast.ml

lexer.ml: lexer.mll
	${OCAMLLEX} lexer.mll

lexer.cmi: lexer.mli parser.cmi
	${OCAMLOPT} -c lexer.mli

lexer.cmx lexer.o: lexer.ml lexer.cmi parser.cmi
	${OCAMLOPT} -c lexer.ml

parser.ml parser.mli: parser.mly
	${MENHIR} parser.mly

parser.cmi: parser.mli ast.cmi
	${OCAMLOPT} -c parser.mli

parser.cmx parser.o: parser.ml parser.cmi ast.cmi
	${OCAMLOPT} -c parser.ml

main.cmx: main.ml ast.cmx lexer.cmx parser.cmx
	${OCAMLOPT} -c main.ml

prototype: ${MODULES}
	${OCAMLOPT} -o prototype ${MODULES}
