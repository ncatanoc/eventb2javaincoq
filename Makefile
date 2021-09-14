
#***************************************************************************
#
#  Rules and dependencies.
#
#  target  - the parameter given to make: What to build
#  depends - file or other targets target depends on
#  rule    - how to create target
#  $(VAR)  - environment variable or variable defined above
#  $@      - Current target
#  $*      - Current target without extension
#  $<      - Current dependencies
#
#***************************************************************************

OCAMLC = ocamlc

COQC = coqc
COQDEP = coqdep
COQ_INCLUDE=. 
COQ_FLAGS =

COQOBJS = state_types.vo \
	coqpredicate.vo \
	btypes.vo \
	jmltypes.vo \
	bsemantics.vo \
	jmlsemantics.vo \
	b2jml.vo \
	theproof.vo \
	extract.vo

MLFILES = machine2jml.ml \
	example01.ml

all : $(COQOBJS)

%.vo : %.v
	$(COQC) -include $(COQ_INCLUDE) $(COQ_FLAGS) $<

machine2jml.cmi : machine2jml.mli 
	$(OCAMLC) -g -c $<

machine2jml.cmo : machine2jml.ml \
	machine2jml.cmi 
	$(OCAMLC) -g -c $<

example01 : example01.ml \
	machine2jml.cmo
	$(OCAMLC) -g -o example01.sh $<	

clean:
	rm -f *.vo *.glob *.crashcoqide *~ *.cmi *.cmo *.sh machine2jml.ml machinejml.mli


