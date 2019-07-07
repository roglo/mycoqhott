all: hott4cat.vo chap1.vo chap2.vo chap3.vo chap4.vo chap5.vo

clean:
	rm -f *.vo *.glob

.SUFFIXES: .v .vo

.v.vo:
	coqc -indices-matter $<

chap2.vo: chap1.vo
chap3.vo: chap2.vo
chap4.vo: chap3.vo
chap5.vo: chap4.vo
