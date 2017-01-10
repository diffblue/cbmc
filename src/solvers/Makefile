include ../config.inc
include ../common

ifneq ($(CHAFF),)
  CHAFF_SRC=sat/satcheck_zchaff.cpp sat/satcheck_zcore.cpp
  CHAFF_INCLUDE=-I $(CHAFF)
  CHAFF_LIB=$(CHAFF)/libsat$(LIBEXT)
endif

ifneq ($(MINISAT),)
  MINISAT_SRC=sat/satcheck_minisat.cpp
  MINISAT_INCLUDE=-I $(MINISAT)
  MINISAT_LIB=$(MINISAT)/Solver$(OBJEXT) $(MINISAT)/Proof$(OBJEXT) $(MINISAT)/File$(OBJEXT)
  CP_CXXFLAGS += -DHAVE_MINISAT
endif

ifneq ($(MINISAT2),)
  MINISAT2_SRC=sat/satcheck_minisat2.cpp
  MINISAT2_INCLUDE=-I $(MINISAT2)
  MINISAT2_LIB=$(MINISAT2)/minisat/simp/SimpSolver$(OBJEXT) $(MINISAT2)/minisat/core/Solver$(OBJEXT)
  CP_CXXFLAGS += -DHAVE_MINISAT2 -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS
endif

ifneq ($(GLUCOSE),)
  GLUCOSE_SRC=sat/satcheck_glucose.cpp
  GLUCOSE_INCLUDE=-I $(GLUCOSE)
  GLUCOSE_LIB=$(GLUCOSE)/simp/SimpSolver$(OBJEXT) $(GLUCOSE)/core/Solver$(OBJEXT)
  CP_CXXFLAGS += -DHAVE_GLUCOSE -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS
endif

ifneq ($(SMVSAT),)
  SMVSAT_SRC=sat/satcheck_smvsat.cpp
  SMVSAT_INCLUDE=-I $(SMVSAT)/include
  SMVSAT_LIB=$(SMVSAT)/lib/libsmvsat$(LIBEXT)
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

ifneq ($(PRECOSAT),)
  PRECOSAT_SRC=sat/satcheck_precosat.cpp
  PRECOSAT_INCLUDE=-I $(PRECOSAT)
  PRECOSAT_LIB=$(PRECOSAT)/precosat$(OBJEXT)
  CP_CXXFLAGS += -DHAVE_PRECOSAT
endif

ifneq ($(PICOSAT),)
  PICOSAT_SRC=sat/satcheck_picosat.cpp
  PICOSAT_INCLUDE=-I $(PICOSAT)
  PICOSAT_LIB=$(PICOSAT)/libpicosat$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_PICOSAT
endif

ifneq ($(LINGELING),)
  LINGELING_SRC=sat/satcheck_lingeling.cpp
  LINGELING_INCLUDE=-I $(LINGELING)
  LINGELING_LIB=$(LINGELING)/liblgl$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_LINGELING
endif

SRC = $(BOOLEFORCE_SRC) \
      $(CHAFF_SRC) \
      $(CUDD_SRC) \
      $(GLUCOSE_SRC) \
      $(LINGELING_SRC) \
      $(MINISAT2_SRC) \
      $(MINISAT_SRC) \
      $(PICOSAT_SRC) \
      $(PRECOSAT_SRC) \
      $(SMVSAT_SRC) \
      $(SQUOLEM2_SRC) \
      cvc/cvc_conv.cpp \
      cvc/cvc_dec.cpp \
      flattening/arrays.cpp \
      flattening/boolbv.cpp \
      flattening/boolbv_abs.cpp \
      flattening/boolbv_add_sub.cpp \
      flattening/boolbv_array.cpp \
      flattening/boolbv_array_of.cpp \
      flattening/boolbv_bitwise.cpp \
      flattening/boolbv_bv_rel.cpp \
      flattening/boolbv_byte_extract.cpp \
      flattening/boolbv_byte_update.cpp \
      flattening/boolbv_case.cpp \
      flattening/boolbv_complex.cpp \
      flattening/boolbv_concatenation.cpp \
      flattening/boolbv_cond.cpp \
      flattening/boolbv_constant.cpp \
      flattening/boolbv_constraint_select_one.cpp \
      flattening/boolbv_div.cpp \
      flattening/boolbv_equality.cpp \
      flattening/boolbv_extractbit.cpp \
      flattening/boolbv_extractbits.cpp \
      flattening/boolbv_floatbv_op.cpp \
      flattening/boolbv_get.cpp \
      flattening/boolbv_ieee_float_rel.cpp \
      flattening/boolbv_if.cpp \
      flattening/boolbv_index.cpp \
      flattening/boolbv_map.cpp \
      flattening/boolbv_member.cpp \
      flattening/boolbv_mod.cpp \
      flattening/boolbv_mult.cpp \
      flattening/boolbv_not.cpp \
      flattening/boolbv_onehot.cpp \
      flattening/boolbv_overflow.cpp \
      flattening/boolbv_power.cpp \
      flattening/boolbv_quantifier.cpp \
      flattening/boolbv_reduction.cpp \
      flattening/boolbv_replication.cpp \
      flattening/boolbv_shift.cpp \
      flattening/boolbv_struct.cpp \
      flattening/boolbv_type.cpp \
      flattening/boolbv_typecast.cpp \
      flattening/boolbv_unary_minus.cpp \
      flattening/boolbv_union.cpp \
      flattening/boolbv_update.cpp \
      flattening/boolbv_vector.cpp \
      flattening/boolbv_width.cpp \
      flattening/boolbv_with.cpp \
      flattening/bv_minimize.cpp \
      flattening/bv_pointers.cpp \
      flattening/bv_utils.cpp \
      flattening/c_bit_field_replacement_type.cpp \
      flattening/equality.cpp \
      flattening/flatten_byte_operators.cpp \
      flattening/functions.cpp \
      flattening/pointer_logic.cpp \
      floatbv/float_bv.cpp \
      floatbv/float_utils.cpp \
      miniBDD/miniBDD.cpp \
      prop/aig.cpp \
      prop/aig_prop.cpp \
      prop/bdd_expr.cpp \
      prop/cover_goals.cpp \
      prop/literal.cpp \
      prop/minimize.cpp \
      prop/prop.cpp \
      prop/prop_assignment.cpp \
      prop/prop_conv.cpp \
      prop/prop_conv_store.cpp \
      qbf/qbf_quantor.cpp \
      qbf/qbf_qube.cpp \
      qbf/qbf_qube_core.cpp \
      qbf/qbf_skizzo.cpp \
      qbf/qdimacs_cnf.cpp \
      qbf/qdimacs_core.cpp \
      refinement/bv_refinement_loop.cpp \
      refinement/refine_arithmetic.cpp \
      refinement/refine_arrays.cpp \
      refinement/string_refinement.cpp \
      refinement/string_constraint_generator_code_points.cpp \
      refinement/string_constraint_generator_comparison.cpp \
      refinement/string_constraint_generator_concat.cpp \
      refinement/string_constraint_generator_constants.cpp \
      refinement/string_constraint_generator_indexof.cpp \
      refinement/string_constraint_generator_insert.cpp \
      refinement/string_constraint_generator_main.cpp \
      refinement/string_constraint_generator_testing.cpp \
      refinement/string_constraint_generator_transformation.cpp \
      refinement/string_constraint_generator_valueof.cpp \
      sat/cnf.cpp \
      sat/cnf_clause_list.cpp \
      sat/dimacs_cnf.cpp \
      sat/pbs_dimacs_cnf.cpp \
      sat/read_dimacs_cnf.cpp \
      sat/resolution_proof.cpp \
      sat/satcheck.cpp \
      smt1/smt1_conv.cpp \
      smt1/smt1_dec.cpp \
      smt2/smt2_conv.cpp \
      smt2/smt2_dec.cpp \
      smt2/smt2_parser.cpp \
      smt2/smt2irep.cpp \
      # Empty last line

INCLUDES += -I .. \
  $(CHAFF_INCLUDE) $(BOOLEFORCE_INCLUDE) $(MINISAT_INCLUDE) $(MINISAT2_INCLUDE) \
  $(SMVSAT_INCLUDE) $(SQUOLEM2_INC) $(CUDD_INCLUDE) $(GLUCOSE_INCLUDE) \
	$(PRECOSAT_INCLUDE) $(PICOSAT_INCLUDE) $(LINGELING_INCLUDE)

CLEANFILES = solvers$(LIBEXT)

all: solvers$(LIBEXT)

ifneq ($(SQUOLEM2),)
  CP_CXXFLAGS += -DHAVE_QBF_CORE
else
ifneq ($(CUDD),)
  CP_CXXFLAGS += -DHAVE_QBF_CORE
endif
endif

# extra dependencies

-include $(SRC:.cpp=.d)

###############################################################################

solvers$(LIBEXT): $(OBJ) $(CHAFF_LIB) $(BOOLEFORCE_LIB) $(MINISAT_LIB) \
        $(MINISAT2_LIB) $(SMVSAT_LIB) $(SQUOLEM2_LIB) $(CUDD_LIB) \
	$(PRECOSAT_LIB) $(PICOSAT_LIB) $(LINGELING_LIB) $(GLUCOSE_LIB)
	$(LINKLIB)
