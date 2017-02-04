target=report

default: pdf

pdf:
	lhs2TeX source.tex > $(target).tex
	latex $(target)
	bibtex $(target)
	pdflatex $(target).tex


watch: pdf
	evince $(target).pdf

clean:

	@rm -f $(target).aux $(target).dvi $(target).toc manual.pdf
	@rm -f $(target).bbl  $(target).blg  $(target).log  $(target).tex
	@rm -f *~
