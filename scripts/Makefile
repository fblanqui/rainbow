# Rainbow, a termination proof certification tool
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2010-11-10
#
# Makefile for checking a directory of CPF files with Rainbow

.SUFFIXES:

.PHONY: default clean results html log

CPF := $(shell ls *.cpf | sed -e 's|.cpf$$||')

default: $(CPF:%=%.vo)

%.vo: %.cpf
	check_coq $< > $*.log 2>&1

clean:
	rm -f *~ *.vo *.v *.log *.glob cpf v vo

results:
	@ls *.cpf | sed -e 's|.cpf$$||' | sort > cpf
	@echo cpf: `cat cpf | wc -l`
	@ls *.v | sed -e 's|.v$$||' | sort > v
	@echo '  v:' `cat v | wc -l`
	@ls *.vo | sed -e 's|.vo$$||' | sort > vo
	@echo ' vo:' `cat vo | wc -l`
	@-diff v vo | sed -e 's|[0-9,]*d[0-9,]*$$||' -e 's|< ||' | sed -e '/^$$/d' > diff-v-vo

log: results
	@echo create log file...; rm -f log
	@for f in $(CPF); do echo $$f >> log; cat $$f.log >> log; done
	@echo create errors file...
	@echo '#!/bin/sh' > errors.sh; grep Error log | sort | uniq | sed -e 's|"|\\"|g' -e 's|\(.*\)|echo \"\1:\" \`grep \"\1\" log \| wc -l\`|' >> errors.sh; sh errors.sh > errors; cat errors

html: $(CPF:%=%.html)

%.html: %.cpf
	xsltproc --maxparserdepth 10000 ~/src/cpf-hg/cpfHTML.xsl $< > $@
