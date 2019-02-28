main: PCF.tex Closure.tex Conversion.tex SubContext.tex StateOfTheArt/Bisimulation.tex
	pdflatex main.tex 

StateOfTheArt/Bisimulation.tex: StateOfTheArt/Bisimulation.lagda
	agda --latex --only-scope-checking --latex-dir=. $<

%.tex: %.lagda
	agda --latex --only-scope-checking --latex-dir=. $<

