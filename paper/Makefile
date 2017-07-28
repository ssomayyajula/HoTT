AGDA=agda
AFLAGS=-i. --latex
SOURCE=Pi
POSTPROCESS=postprocess-latex.pl
LATEX=latexmk -pdf -use-make -e '$$pdflatex=q/lualatex %O %S/'

all:
	$(AGDA) $(AFLAGS) $(SOURCE).lagda
	cd latex/ && \
	perl ../$(POSTPROCESS) $(SOURCE).tex > $(SOURCE).processed && \
	mv $(SOURCE).processed $(SOURCE).tex && \
	$(LATEX) $(SOURCE).tex && \
	mv $(SOURCE).pdf ..

