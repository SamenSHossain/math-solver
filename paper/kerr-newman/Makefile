# Build the paper with pdflatex + bibtex (arXiv-compatible toolchain).
main.pdf: main.tex stats.tex refs.bib
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

# Source bundle for arXiv: main.tex, stats.tex, refs.bib and the generated main.bbl.
arxiv: main.pdf
	rm -rf arxiv && mkdir arxiv
	cp main.tex stats.tex refs.bib main.bbl arxiv/
	tar -czf kerr-newman-arxiv.tar.gz -C arxiv .

clean:
	latexmk -C
	rm -rf arxiv kerr-newman-arxiv.tar.gz

.PHONY: arxiv clean
