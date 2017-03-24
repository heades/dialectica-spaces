AGDA_BINARYS = prelude.agdai              \
	       lineale.agdai              \
	       lineale-thms.agdai         \
	       concrete-lineales.agdai    \
               colineale.agdai            \
               concrete-colineales.agdai  \
               biclosed-poset.agdai       \
               biclosed-poset-thms.agdai  \
               DCSets.agdai               \
               NCDialSets.agdai           \
               DialSets.agdai             \
               concurrency.agdai

AGDA = @agda -v 0

all : $(AGDA_BINARYS)

prelude.agdai : prelude.agda
	@echo "Building prelude.agda"
	$(AGDA) prelude.agda

lineale.agdai : lineale.agda
	@echo "Building lineale.agda"
	$(AGDA) lineale.agda

lineale-thms.agdai : lineale-thms.agda
	@echo "Building lineale-thms.agda"
	$(AGDA) lineale-thms.agda

concrete-lineales.agdai : concrete-lineales.agda
	@echo "Building concrete-lineales.agda"
	$(AGDA) concrete-lineales.agda

colineale.agdai : colineale.agda
	@echo "Building colineale.agda"
	$(AGDA) colineale.agda


concrete-colineales.agdai : concrete-colineales.agda
	@echo "Building concrete-colineales.agda"
	$(AGDA) concrete-colineales.agda

biclosed-poset.agdai : biclosed-poset.agda
	@echo "Building biclosed-poset.agda"
	$(AGDA) biclosed-poset.agda


biclosed-poset-thms.agdai : biclosed-poset-thms.agda
	@echo "Building biclosed-poset-thms.agda"
	$(AGDA) biclosed-poset-thms.agda


DCSets.agdai : DCSets.agda
	@echo "Building DCSets.agda"
	$(AGDA) DCSets.agda


NCDialSets.agdai : NCDialSets.agda
	@echo "Building NCDialSets.agda"
	$(AGDA) NCDialSets.agda


DialSets.agdai : DialSets.agda
	@echo "Building DialSets.agda"
	$(AGDA) DialSets.agda

concurrency.agdai : concurrency.agda
	@echo "Building concurrency.agda"
	$(AGDA) concurrency.agda

clean :
	rm -f *.agdai
