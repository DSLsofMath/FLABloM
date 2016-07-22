NAME    := abstract

LHS2TEX := lhs2TeX
LATEXMK := latexmk

AGDAFILES = $(wildcard ../*.lagda)

default: $(NAME).pdf

PAPERNAME = icfpws16tydemain-tydemainid12-p

submit: abstract.tex
	mkdir submit
	cp abstract.tex sigplanconf.cls matrix.tex unicode.tex paper.bib submit
	(cd submit; latexmk -pdf abstract.tex)
	-rm -r ${PAPERNAME} ${PAPERNAME}.tgz
	mv submit ${PAPERNAME}
	tar -zcf ${PAPERNAME}.tar.gz ${PAPERNAME}
	ln -s ${PAPERNAME}/abstract.pdf ${PAPERNAME}.pdf

$(NAME).tex: $(AGDAFILES)

%.tex: %.lagda paper.format
	$(LHS2TEX) --agda $< > $@

%.pdf: %.tex paper.bib
	$(LATEXMK) -pdf $<

clean:
	latexmk -C $(NAME).tex
	$(RM) $(NAME).tex $(NAME).pdf
