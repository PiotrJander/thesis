sa=aacmm/StateOfTheArt

aacmm/StateOfTheArt/Bisimulation.tex: aacmm/StateOfTheArt/Bisimulation.lagda
	agda --latex --only-scope-checking --latex-dir=. $<

# %.tex: %.lagda
# 	agda --latex --only-scope-checking --latex-dir=. $<

.PHONY: agda

agda: PCF.tex Closure.tex Conversion.tex SubContext.tex aacmm/StateOfTheArt/Bisimulation.tex

main.pdf: agda
	pdflatex main.tex 

.all: main.pdf
