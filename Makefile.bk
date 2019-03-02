main: PCF.tex Closure.tex Conversion.tex SubContext.tex StateOfTheArt/Bisimulation.tex StateOfTheArt/Closure-Thms.tex
	pdflatex main.tex
	# latexmk -pdf -use-make -xelatex main.tex 

StateOfTheArt/Bisimulation.tex: StateOfTheArt/Bisimulation.lagda StateOfTheArt/Closure-Thms.tex
	agda --latex --only-scope-checking --latex-dir=. $<

StateOfTheArt/Closure-Thms.tex: StateOfTheArt/Closure-Thms.lagda
	agda --latex --only-scope-checking --latex-dir=. $<

%.tex: %.lagda
	agda --latex --only-scope-checking --latex-dir=. $<

clean:
	find . -name "*.agdai" -o -name "*.aux" -o -name "*.ptb" -o -name "*.toc" -o -name "*.log" -type f -delete
