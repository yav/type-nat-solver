

paper.pdf: paper.tex refs.bib
	mkdir -p build
	pdflatex -output-directory build $<
	# bibtex build/paper.aux
	pdflatex -output-directory build $<
	pdflatex -output-directory build $<
	cp build/paper.pdf .

paper.zip: paper.tex sigplanconf.cls
	zip paper.zip $^
