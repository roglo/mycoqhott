all: chap1.vo chap2.vo hott.vo

clean:
	rm -f *.vo *.glob

.SUFFIXES: .v .vo

.v.vo:
	coqc $<

chap2.vo: chap1.vo
