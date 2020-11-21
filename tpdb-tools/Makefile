
CMX=trs_ast.cmx trs_parser.cmx trs_lexer.cmx \
	srs_ast.cmx srs_parser.cmx srs_lexer.cmx \
	lp_ast.cmx lp_parser.cmx lp_lexer.cmx \
	trs_sem.cmx cime.cmx trs_check.cmx

GENERATED=trs_parser.ml trs_lexer.ml trs_parser.mli \
	srs_parser.ml srs_lexer.ml srs_parser.mli \
	lp_parser.ml lp_lexer.ml lp_parser.mli \
	testotrs.ml

all: trs_check testotrs

trs_check: $(CMX)
	ocamlopt -o trs_check $(CMX)

testotrs: testotrs.cmx
	ocamlopt -o testotrs testotrs.cmx

trs_parser.ml trs_parser.mli: trs_parser.mly
	ocamlyacc -v trs_parser.mly

srs_parser.ml srs_parser.mli: srs_parser.mly
	ocamlyacc -v srs_parser.mly

lp_parser.ml lp_parser.mli: lp_parser.mly
	ocamlyacc -v lp_parser.mly

# generic rules
#########

.SUFFIXES: .mli .ml .cmi .cmo .cmx .mll .mly

.mll.ml:
	ocamllex $<

.mli.cmi:
	ocamlc -g -c $<

.ml.cmo:
	ocamlc -g -c $<

.ml.cmx:
	ocamlopt -c $<


# clean and depend
##################

clean:
	rm -f *~ *.cm[iox] *.o *.output
	rm -f testotrs trs_check
	rm -f $(GENERATED)

depend .depend: $(GENERATED)
	rm -f .depend
	ocamldep  *.mli *.ml > .depend

include .depend


