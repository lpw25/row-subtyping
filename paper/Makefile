
OTTFLAGS=-tex_show_meta false -signal_parse_errors true -tex_wrap false

all : subtyping.pdf

subtyping-gen.tex : subtyping.ott
	ott ${OTTFLAGS} -i subtyping.ott -o subtyping-gen.tex

subtyping.pdf : subtyping.tex subtyping-gen.tex
	latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make subtyping.tex

clean:
	latexmk -CA
	rm subtyping-gen.tex
