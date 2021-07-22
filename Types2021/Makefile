all : types2021.pdf

types2021.pdf : AgdaTypes.tex types2021.tex Graph/lib_description.tex Graph/voca_datatypes.tex commands.tex type-transformers.png
	latexmk -pdf -synctex=1 -interaction=nonstopmode -recorder types2021.tex

AgdaTypes.tex :  AgdaTypes.lagda agda.sty
	agda --latex --latex-dir="." AgdaTypes.lagda

clean :
	rm -rf AgdaTypes.tex AgdaTypes.agdai *.aux *.fls types2021.pdf *.synctex.gz *.fdb_latexmk *.log *.ptb *.bbl *.blg *.out *.vtc
