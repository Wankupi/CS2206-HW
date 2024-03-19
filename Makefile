CURRENT_DIR=.
SETS_DIR = sets
COMPCERT_DIR = compcert_lib
PV_DIR = pv
ASSIGNMENT_DIR = Assignment

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

PV_FLAG = -R $(PV_DIR) PV -R $(SETS_DIR) SetsClass -R $(COMPCERT_DIR) compcert.lib

SETS_FLAG = -R $(SETS_DIR) SetsClass

COMPCERT_FLAG = -R $(COMPCERT_DIR) compcert.lib

DEP_FLAG = -R $(PV_DIR) PV -R $(SETS_DIR) SetsClass -R $(COMPCERT_DIR) compcert.lib

SETS_FILE_NAMES = \
   SetsClass.v SetsDomain.v SetElement.v RelsDomain.v SetElementProperties.v SetProd.v SetsClass_AxiomFree.v SetsDomain_Classic.v
   
SETS_FILES=$(SETS_FILE_NAMES:%.v=$(SETS_DIR)/%.v)
   
COMPCERT_FILE_NAMES = \
    Coqlib.v Integers.v Zbits.v
    
COMPCERT_FILES=$(COMPCERT_FILE_NAMES:%.v=$(COMPCERT_DIR)/%.v)

PV_FILE_NAMES = \
  Intro.v SimpleProofsAndDefs.v InductiveType.v Syntax.v RecurProp.v DenotationalSemantics.v \
  BuiltInNat.v Logic.v RelsAsDenotations.v FixedPoint.v
  
PV_FILES=$(PV_FILE_NAMES:%.v=$(PV_DIR)/%.v)

ASSIGNMENT_FILE_NAMES = \
  Assignment0220.v  Assignment0223.v Assignment0305.v Assignment0312.v

ASSIGNMENT_FILES=$(ASSIGNMENT_FILE_NAMES:%.v=$(ASSIGNMENT_DIR)/%.v)

FILES = $(PV_FILES) \
  $(ASSIGNMENT_FILES) \
  $(SETS_FILES) \
  $(COMPCERT_FILES)

$(SETS_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<
	@$(COQC) $(SETS_FLAG) $<

$(COMPCERT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<
	@$(COQC) $(COMPCERT_FLAG) $<
			
$(PV_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(PV_FLAG) $<

$(ASSIGNMENT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(PV_FLAG) $<
	
all: $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f *.glob */*.glob
	@rm -f *.vo */*.vo
	@rm -f *.vok */*.vok
	@rm -f *.vos */*.vos 
	@rm -f .*.aux */.*.aux
	@rm -f .depend

.PHONY: clean depend
.DEFAULT_GOAL := all

-include .depend
