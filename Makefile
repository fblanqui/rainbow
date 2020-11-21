# Rainbow, a termination proof certification tool
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2010-11-15

.PHONY: all xml-light tpdb-tools rainbow extract \
	examples clean-all dist install-dist new lib print #TEST

first: convert

FORCE:

include Makefile.ocaml

###############################################################################
# other targets

examples:
	$(MAKE)
	$(MAKE) -C examples

clean-all: clean
	$(MAKE) -C xml-light clean
	$(MAKE) -C tpdb-tools clean
	rm -f xml-light/xml-light.a
	(cd tpdb-tools && rm -f *.a *.cm* .depend)

clean::
	-$(MAKE) -C coq clean
	rm -rf tmp extract coq/Makefile order_deps
	rm -f parser.ml parser.mli lexer.ml

###############################################################################
# distribution installation (Frederic only)

dist:
	scripts/create_dist

DIR := ~/web/formes

install-dist: $(DIR)
	cp Rainbow_`date +%y%m%d`.tar.gz $(DIR)/Rainbow.tar.gz
	cp CHANGES $(DIR)/CHANGES.Rainbow
	cp CHANGES ~/web/color/site/CHANGES.Rainbow

###############################################################################
# old rainbow program not based on CoLoR extraction

convert: xml-light tpdb-tools
	$(MAKE) -f Makefile.convert depend
	$(MAKE) -f Makefile.convert

clean::
	$(MAKE) -f Makefile.convert clean

###############################################################################
# rainbow program based on CoLoR extraction and ProofChecker

check: lib color
	$(MAKE) -f Makefile.check depend
	$(MAKE) -f Makefile.check

clean::
	$(MAKE) -f Makefile.check clean

###############################################################################
# new rainbow program based on CoLoR extraction and ./rainbow.v

new: xml-light tpdb-tools color newcpf.ml
	$(MAKE) -f Makefile.new_convert depend
	$(MAKE) -f Makefile.new_convert

newcpf.ml: xsd2ml grammar/cpf.xsd
	./xsd2ml < grammar/cpf.xsd > $@

clean::
	$(MAKE) -f Makefile.new_convert clean
	rm -f newcpf.ml

###############################################################################
# TEST 

print: xml-light tpdb-tools print_function.ml
	$(MAKE) -f Makefile.print depend
	$(MAKE) -f Makefile.print

clean::
	$(MAKE) -f Makefile.print clean

###############################################################################
# compilation of xsd2ml and xsd2coq

xsd2ml:
	$(MAKE) -f Makefile.xsd2ml depend
	$(MAKE) -f Makefile.xsd2ml

clean::
	$(MAKE) -f Makefile.xsd2ml clean

xsd2coq:
	$(MAKE) -f Makefile.xsd2coq depend
	$(MAKE) -f Makefile.xsd2coq

clean::
	$(MAKE) -f Makefile.xsd2coq clean

###############################################################################
# extraction and compilation of the CoLoR library

color: coq/cpf.v
	$(MAKE) -C coq

coq/cpf.v: xsd2coq grammar/cpf.xsd
	./xsd2coq < grammar/cpf.xsd > $@

clean::
	rm -f coq/cpf.v

###############################################################################
# compilation of the rainbow library

lib: convert.cma convert.cmxa

convert.cma convert.cmxa: xml-light tpdb-tools
	$(MAKE) -f Makefile.convert depend
	$(MAKE) -f Makefile.convert $@

clean::
	rm -f convert.cma convert.cmxa

###############################################################################
# compilation of the xml-light library

XMLLIGHT_PARSERS := xml_parser xml_lexer

.PRECIOUS: $(XMLLIGHT_PARSERS:%=xml-light/%.ml)

XMLLIGHT := $(XMLLIGHT_PARSERS) dtd xmlParser xml

XMLLIGHT_FILES := $(XMLLIGHT:%=xml-light/%)
XMLLIGHT_CMOFILES := $(XMLLIGHT_FILES:%=%.cmo)
XMLLIGHT_CMXFILES := $(XMLLIGHT_FILES:%=%.cmx)

xml-light:
	$(MAKE) -C xml-light
	$(MAKE) -C xml-light opt

xml-light/xml-light.cma: $(XMLLIGHT_CMOFILES)
	$(SHOW) OCAMLC -a -o $@
	$(HIDE) $(OCAMLC) -a -o $@ $+

xml-light/xml-light.cmxa: $(XMLLIGHT_CMXFILES)
	$(SHOW) OCAMLOPT -a -o $@
	$(HIDE) $(OCAMLOPT) -a -o $@ $+

###############################################################################
# compilation of the tpdb-tools library

TPDB_PARSERS := srs_lexer srs_parser trs_lexer trs_parser lp_lexer lp_parser

.PRECIOUS: $(TPDB_PARSERS:%=tpdb-tools/%.ml)

TPDB := srs_ast trs_ast lp_ast $(TPDB_PARSERS) trs_sem #cime trs_check

TPDB_FILES := $(TPDB:%=tpdb-tools/%)
TPDB_CMOFILES := $(TPDB_FILES:%=%.cmo)
TPDB_CMXFILES := $(TPDB_FILES:%=%.cmx)

tpdb-tools:
	$(MAKE) -C tpdb-tools $(TPDB:%=%.cmo)
	$(MAKE) -C tpdb-tools
	$(MAKE) tpdb-tools/tpdb-tools.cma tpdb-tools/tpdb-tools.cmxa

tpdb-tools/tpdb-tools.cma: $(TPDB_CMOFILES)
	$(SHOW) OCAMLC -a -o $@
	$(HIDE) $(OCAMLC) -a -o $@ $+

tpdb-tools/tpdb-tools.cmxa: $(TPDB_CMXFILES)
	$(SHOW) OCAMLOPT -a -o $@
	$(HIDE) $(OCAMLOPT) -a -o $@ $+
