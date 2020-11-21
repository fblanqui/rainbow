# Rainbow, a termination proof certification tool
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2007-05-21

.SUFFIXES:

.PHONY: default clean

SRS := rev1 loop3 loop4 loop5

ARCTIC_TRS := simple jw1 z086 beerendonk_1

TROPICAL_TRS := b01 e01 g07

TRS := rename pi1 pi2 pi3 af1 af2 z086 decomp1 decomp2 loop1 loop2 \
	unlab rootlab rpo1 rev2 rev3 \
	$(ARCTIC_TRS:%=arctic/%) \
	$(TROPICAL_TRS:%=tropical/%)

PRF := $(SRS) $(TRS)

default: $(PRF:%=%.vo)

ifdef COQ_INIT_FILE
OPT := -init-file $(COQ_INIT_FILE)
endif

%.vo: %.v
	coqc $(OPT) -dont-load-proofs $<

%.v: ../convert %.trs %.prf
	../convert -itrs $*.trs -iprf $*.prf -ocoq > $@

%.v: ../convert %.srs %.prf
	../convert -isrs $*.srs -iprf $*.prf -ocoq > $@

.PRECIOUS: $(PRF:%=%.v)

clean:
	rm -f `find . -name \*~ -o -name \*.glob -o -name \*.vo -o -name \*.v`
