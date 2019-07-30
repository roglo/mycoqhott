FILESFORDEP=`LC_ALL=C ls *.v`

all: category.vo misc_cat.vo cone_lim.vo yoneda.vo chap4.vo

clean:
	rm -f *.vo *.glob

depend:
	mv .depend .depend.bak
	coqdep $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	coqc -indices-matter $<

chap2.vo: chap1.vo
chap3.vo: chap2.vo
chap4.vo: chap3.vo
chap5.vo: chap4.vo

include .depend
