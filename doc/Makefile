SED=sed
PAPER=main
AGDA=agda

all: latex/$(PAPER).pdf

AGDA_FILES:=\
  STLC.lagda \
  Common.lagda \
  StateOfTheArt/Bisimulation.lagda \
  StateOfTheArt/Closure-Thms.lagda \
  StateOfTheArt/Closure.lagda

AGDA_OUTPUT:=$(patsubst %.lagda,latex-agda-output/%.tex,$(AGDA_FILES))
AGDA_OUTPUT_PROCESSED:=$(patsubst %.lagda,latex/%.tex,$(AGDA_FILES))

.SECONDARY: $(AGDA_OUTPUT)

PAPER_DEPENDENCIES:=\
  latex/$(PAPER).tex\
  latex/main.bib \
  latex/infthesis.cls \
  latex/eushield.sty \
  latex/commands.tex \
  latex/agda.sty \
  $(AGDA_OUTPUT_PROCESSED)

latex/$(PAPER).pdf: $(PAPER_DEPENDENCIES)
	cd latex; latexmk -interaction=nonstopmode -halt-on-error -pdf -bibtex $(PAPER).tex

latex/agda.sty: $(AGDA_OUTPUT)
	@mkdir -p $(dir $@)
	cp latex-agda-output/agda.sty $@

latex/main.bib: main.bib
	@mkdir -p $(dir $@)
	cp $< $@

latex/commands.tex: commands.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/infthesis.cls: infthesis.cls
	@mkdir -p $(dir $@)
	cp $< $@

latex/eushield.sty: eushield.sty
	@mkdir -p $(dir $@)
	cp $< $@

latex/$(PAPER).tex: $(PAPER).tex rules.sed
	@mkdir -p $(dir $@)
	${SED} -f rules.sed $< > $@

latex/syntax.tex: syntax.tex rules.sed
	@mkdir -p $(dir $@)
	${SED} -f rules.sed $< > $@

latex/%.tex: latex-agda-output/%.tex rules.sed
	@mkdir -p $(dir $@)
	${SED} -f rules.sed $< > $@
	${SED} -f rules.sed -i '' $@
	${SED} -f rules.sed -i '' $@

latex-agda-output/%.tex: %.lagda
	@mkdir -p $(dir $@)
	${AGDA} -i . --allow-unsolved-metas --latex $< --latex-dir=latex-agda-output > $(basename $@).log

clean:
	find . -name '*.agdai' | xargs rm
	rm -rf latex
	rm -rf latex-agda-output
