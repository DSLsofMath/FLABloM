NAME    := abstract

LHS2TEX := lhs2TeX
LATEXMK := latexmk

AGDAFILES = $(wildcard ../*.lagda)

default: $(NAME).pdf

$(NAME).tex: $(AGDAFILES)

%.tex: %.lagda paper.format
	$(LHS2TEX) --agda $< > $@

%.pdf: %.tex paper.bib
	$(LATEXMK) -xelatex $<

clean:
	latexmk -C $(NAME).tex
	$(RM) $(NAME).tex $(NAME).pdf
