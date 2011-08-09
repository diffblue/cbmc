include ../config.inc

all: solvers$(LIBEXT)

ifneq ($(CHAFF),)
  CHAFF_SRC=sat/satcheck_zchaff.cpp sat/satcheck_zcore.cpp
  CHAFF_INCLUDE=-I $(CHAFF)
  CHAFF_LIB=$(CHAFF)/libsat.a
endif

ifneq ($(MINISAT),)
  MINISAT_SRC=sat/satcheck_minisat.cpp 
  MINISAT_INCLUDE=-I $(MINISAT)
  MINISAT_LIB=$(MINISAT)/Solver$(OBJEXT) $(MINISAT)/Proof$(OBJEXT) $(MINISAT)/File$(OBJEXT)
  CXXFLAGS += -DHAVE_MINISAT
endif

ifneq ($(MINISAT2),)
  MINISAT2_SRC=sat/satcheck_minisat2.cpp
  MINISAT2_INCLUDE=-I $(MINISAT2)
  MINISAT2_LIB=$(MINISAT2)/simp/SimpSolver$(OBJEXT) $(MINISAT2)/core/Solver$(OBJEXT)
  CXXFLAGS += -DHAVE_MINISAT2 -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS
  GCCFLAGS := $(filter-out -pedantic, $(GCCFLAGS))
endif

ifneq ($(SMVSAT),)
  SMVSAT_SRC=sat/satcheck_smvsat.cpp
  SMVSAT_INCLUDE=-I $(SMVSAT)/include
  SMVSAT_LIB=$(SMVSAT)/lib/libsmvsat.a
endif

ifneq ($(SQUOLEM2),)
  SQUOLEM2_SRC=qbf/qbf_squolem.cpp qbf/qbf_squolem_core.cpp
  SQUOLEM2_INCLUDE=-I $(SQUOLEM2)
  SQUOLEM2_LIB=-L $(SQUOLEM2) -lsquolem2
endif

ifneq ($(CUDD),)
  CUDD_SRC=qbf/qbf_bdd_core.cpp qbf/qbf_skizzo_core.cpp
  CUDD_INCLUDE=-I $(CUDD)/include
  CUDD_LIB=-L $(CUDD)/cudd -L $(CUDD)/util -L $(CUDD)/mtr \
           -L $(CUDD)/st -L $(CUDD)/obj -L $(CUDD)/dddmp \
           -L $(CUDD)/epd -lobj -lcudd -lmtr -lst -lutil -lepd -ldddmp
endif

SRC = $(CHAFF_SRC) $(BOOLEFORCE_SRC) $(MINISAT_SRC) $(MINISAT2_SRC) \
      $(SMVSAT_SRC) $(SQUOLEM2_SRC) $(CUDD_SRC) $(BOOLECTOR_SRC) \
      $(Z3_SRC) \
      sat/cnf.cpp sat/dimacs_cnf.cpp sat/cnf_clause_list.cpp \
      sat/pbs_dimacs_cnf.cpp sat/read_dimacs_cnf.cpp \
      sat/resolution_proof.cpp sat/satcheck.cpp \
      qbf/qdimacs_cnf.cpp qbf/qbf_quantor.cpp \
      qbf/qbf_skizzo.cpp qbf/qdimacs_core.cpp qbf/qbf_qube.cpp \
      qbf/qbf_qube_core.cpp \
      prop/prop.cpp prop/prop_conv.cpp prop/prop_conv_store.cpp \
      prop/aig_formula.cpp \
      prop/aig.cpp prop/aig_prop.cpp \
      cvc/cvc_prop.cpp cvc/cvc_conv.cpp cvc/cvc_dec.cpp \
      smt1/smt1_dec.cpp smt1/smt1_prop.cpp smt1/smt1_conv.cpp \
      smt2/smt2_dec.cpp smt2/smt2_prop.cpp smt2/smt2_conv.cpp \
      dplib/dplib_conv.cpp dplib/dplib_dec.cpp dplib/dplib_prop.cpp \
      flattening/equality.cpp flattening/arrays.cpp \
      flattening/functions.cpp flattening/sat_minimizer.cpp \
      flattening/boolbv_width.cpp flattening/boolbv.cpp \
      flattening/boolbv_constraint_select_one.cpp \
      flattening/bv_pointers.cpp flattening/bv_utils.cpp \
      flattening/boolbv_abs.cpp flattening/boolbv_with.cpp \
      flattening/boolbv_typecast.cpp flattening/boolbv_index.cpp \
      flattening/boolbv_member.cpp flattening/boolbv_if.cpp \
      flattening/boolbv_byte_extract.cpp flattening/boolbv_add_sub.cpp \
      flattening/boolbv_mult.cpp flattening/boolbv_constant.cpp \
      flattening/boolbv_extractbit.cpp flattening/boolbv_bv_rel.cpp \
      flattening/boolbv_shift.cpp flattening/boolbv_case.cpp \
      flattening/boolbv_cond.cpp flattening/boolbv_concatenation.cpp \
      flattening/boolbv_div.cpp flattening/boolbv_mod.cpp \
      flattening/boolbv_extractbits.cpp flattening/boolbv_replication.cpp \
      flattening/boolbv_reduction.cpp flattening/boolbv_overflow.cpp \
      flattening/boolbv_get.cpp flattening/boolbv_bitwise.cpp \
      flattening/boolbv_equality.cpp flattening/boolbv_unary_minus.cpp \
      flattening/boolbv_ieee_float_rel.cpp flattening/pointer_logic.cpp \
      flattening/boolbv_quantifier.cpp flattening/boolbv_struct.cpp \
      flattening/boolbv_byte_update.cpp flattening/boolbv_array_of.cpp \
      flattening/boolbv_map.cpp flattening/boolbv_type.cpp \
      flattening/boolbv_union.cpp flattening/flatten_byte_operators.cpp

OBJ = $(SRC:.cpp=$(OBJEXT))

ifneq ($(SQUOLEM2),)
  CXXFLAGS += -DHAVE_QBF_CORE
else
ifneq ($(CUDD),)
  CXXFLAGS += -DHAVE_QBF_CORE
endif
endif

ifdef MODULE_FLOATBV
  CXXFLAGS += -DHAVE_FLOATBV
  OBJ += ../floatbv/floatbv$(LIBEXT)
endif

INCLUDES= -I .. \
  $(CHAFF_INCLUDE) $(BOOLEFORCE_INCLUDE) $(MINISAT_INCLUDE) $(MINISAT2_INCLUDE) \
  $(SMVSAT_INCLUDE) $(SQUOLEM2_INC) $(CUDD_INCLUDE) $(BOOLECTOR_INCLUDE) -I ../util 

include ../common

###############################################################################

solvers$(LIBEXT): $(OBJ) $(CHAFF_LIB) $(BOOLEFORCE_LIB) $(MINISAT_LIB) \
        $(MINISAT2_LIB) $(SMVSAT_LIB) $(SQUOLEM2_LIB) $(CUDD_LIB) \
        $(BOOLECTOR_LIB)
	$(LINKLIB)

clean:
	rm -f $(OBJ) solvers$(LIBEXT)
