AGDA=agda
AFLAGS=-i. --latex
SOURCE=paper
POSTPROCESS=postprocess-latex.pl
LATEX=latexmk -pdf -use-make -e '$$pdflatex=q/xelatex %O %S/'

all:
	$(AGDA) $(AFLAGS) $(SOURCE).lagda
	cd latex/ && \
	perl ../$(POSTPROCESS) $(SOURCE).tex > $(SOURCE).processed && \
	mv $(SOURCE).processed $(SOURCE).tex && \
	$(LATEX) $(SOURCE).tex && \
	mv $(SOURCE).pdf ..

