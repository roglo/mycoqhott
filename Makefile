FILESFORDEP=`LC_ALL=C ls *.v`

all: category.vo misc_cat.vo cone_lim.vo adjunction.vo yoneda.vo chap4.vo

clean:
	rm -f *.vo *.glob

depend:
	mv .depend .depend.bak
	coqdep $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	coqc -indices-matter $<

include .depend
