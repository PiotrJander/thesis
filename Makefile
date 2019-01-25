PCF.tex: PCF.lagda
	agda --latex --only-scope-checking --latex-dir=. $<

Closure.tex: Closure.lagda
	agda --latex --only-scope-checking --latex-dir=. $<

Conversion.tex: Conversion.lagda
	agda --latex --only-scope-checking --latex-dir=. $<

SubContext.tex: SubContext.lagda
	agda --latex --only-scope-checking --latex-dir=. $<

.PHONY: agda

agda: PCF.tex Closure.tex Conversion.tex SubContext.tex

main.pdf: agda
	pdflatex main.tex 

.all: main.pdf
