include ../config.inc

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
  CLEANFILES += $(MINISAT_LIB) $(patsubst %$(OBJEXT), %$(DEPEXT), $(MINISAT_LIB))
endif

ifneq ($(MINISAT2),)
  MINISAT2_SRC=sat/satcheck_minisat2.cpp
  MINISAT2_INCLUDE=-I $(MINISAT2)
  MINISAT2_LIB=$(MINISAT2)/minisat/simp/SimpSolver$(OBJEXT) $(MINISAT2)/minisat/core/Solver$(OBJEXT)
  CP_CXXFLAGS += -DHAVE_MINISAT2 -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS
  CLEANFILES += $(MINISAT2_LIB) $(patsubst %$(OBJEXT), %$(DEPEXT), $(MINISAT2_LIB))
endif

ifneq ($(IPASIR),)
  IPASIR_SRC=sat/satcheck_ipasir.cpp
  IPASIR_INCLUDE=-I $(IPASIR)
  CP_CXXFLAGS += -DHAVE_IPASIR -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS
  override CXXFLAGS := $(filter-out -pedantic, $(CXXFLAGS))
endif

ifneq ($(GLUCOSE),)
  GLUCOSE_SRC=sat/satcheck_glucose.cpp
  GLUCOSE_INCLUDE=-I $(GLUCOSE)
  GLUCOSE_LIB=$(GLUCOSE)/simp/SimpSolver$(OBJEXT) $(GLUCOSE)/core/Solver$(OBJEXT)
  CP_CXXFLAGS += -DHAVE_GLUCOSE -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS
  CLEANFILES += $(GLUCOSE_LIB) $(patsubst %$(OBJEXT), %$(DEPEXT), $(GLUCOSE_LIB))
endif

ifneq ($(SQUOLEM2),)
  SQUOLEM2_SRC=qbf/qbf_squolem.cpp qbf/qbf_squolem_core.cpp
  SQUOLEM2_INCLUDE=-I $(SQUOLEM2)
  SQUOLEM2_LIB=-L $(SQUOLEM2) -lsquolem2
endif

ifneq ($(CUDD),)
  CUDD_LIB=$(CUDD)/cudd/.libs/libcudd$(LIBEXT) $(CUDD)/cplusplus/.libs/libobj$(LIBEXT)
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

ifneq ($(CADICAL),)
  CADICAL_SRC=sat/satcheck_cadical.cpp
  CADICAL_INCLUDE=-I $(CADICAL)/src
  CADICAL_LIB=$(CADICAL)/build/libcadical$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_CADICAL
endif

SRC = $(BOOLEFORCE_SRC) \
      $(CHAFF_SRC) \
      $(CUDD_SRC) \
      $(GLUCOSE_SRC) \
      $(LINGELING_SRC) \
      $(MINISAT2_SRC) \
      $(IPASIR_SRC) \
      $(MINISAT_SRC) \
      $(PICOSAT_SRC) \
      $(SQUOLEM2_SRC) \
      $(CADICAL_SRC) \
      decision_procedure.cpp \
      solver_hardness.cpp \
      flattening/arrays.cpp \
      flattening/boolbv.cpp \
      flattening/boolbv_abs.cpp \
      flattening/boolbv_add_sub.cpp \
      flattening/boolbv_array.cpp \
      flattening/boolbv_array_of.cpp \
      flattening/boolbv_bitwise.cpp \
      flattening/boolbv_bswap.cpp \
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
      flattening/boolbv_floatbv_mod_rem.cpp \
      flattening/boolbv_floatbv_op.cpp \
      flattening/boolbv_get.cpp \
      flattening/boolbv_ieee_float_rel.cpp \
      flattening/boolbv_if.cpp \
      flattening/boolbv_index.cpp \
      flattening/boolbv_let.cpp \
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
      flattening/bv_dimacs.cpp \
      flattening/bv_minimize.cpp \
      flattening/bv_pointers.cpp \
      flattening/bv_utils.cpp \
      flattening/c_bit_field_replacement_type.cpp \
      flattening/equality.cpp \
      flattening/pointer_logic.cpp \
      floatbv/float_bv.cpp \
      floatbv/float_utils.cpp \
      floatbv/float_approximation.cpp \
      lowering/byte_operators.cpp \
      lowering/functions.cpp \
      bdd/miniBDD/miniBDD.cpp \
      prop/bdd_expr.cpp \
      prop/cover_goals.cpp \
      prop/literal.cpp \
      prop/prop_minimize.cpp \
      prop/prop.cpp \
      prop/prop_conv.cpp \
      prop/prop_conv_solver.cpp \
      qbf/qbf_quantor.cpp \
      qbf/qbf_qube.cpp \
      qbf/qbf_qube_core.cpp \
      qbf/qbf_skizzo.cpp \
      qbf/qdimacs_cnf.cpp \
      qbf/qdimacs_core.cpp \
      refinement/bv_refinement_loop.cpp \
      refinement/refine_arithmetic.cpp \
      refinement/refine_arrays.cpp \
      strings/array_pool.cpp \
      strings/equation_symbol_mapping.cpp \
      strings/format_specifier.cpp \
      strings/string_builtin_function.cpp \
      strings/string_dependencies.cpp \
      strings/string_concatenation_builtin_function.cpp \
      strings/string_format_builtin_function.cpp \
      strings/string_insertion_builtin_function.cpp \
      strings/string_refinement.cpp \
      strings/string_refinement_util.cpp \
      strings/string_constraint.cpp \
      strings/string_constraint_generator_code_points.cpp \
      strings/string_constraint_generator_comparison.cpp \
      strings/string_constraint_generator_constants.cpp \
      strings/string_constraint_generator_indexof.cpp \
      strings/string_constraint_generator_float.cpp \
      strings/string_constraint_generator_main.cpp \
      strings/string_constraint_generator_testing.cpp \
      strings/string_constraint_generator_transformation.cpp \
      strings/string_constraint_generator_valueof.cpp \
      strings/string_constraint_instantiation.cpp \
      sat/cnf.cpp \
      sat/cnf_clause_list.cpp \
      sat/dimacs_cnf.cpp \
      sat/external_sat.cpp \
      sat/pbs_dimacs_cnf.cpp \
      sat/resolution_proof.cpp \
      smt2/letify.cpp \
      smt2/smt2_conv.cpp \
      smt2/smt2_dec.cpp \
      smt2/smt2_format.cpp \
      smt2/smt2_parser.cpp \
      smt2/smt2_tokenizer.cpp \
      smt2/smt2irep.cpp \
      smt2_incremental/convert_expr_to_smt.cpp \
      smt2_incremental/smt_bit_vector_theory.cpp \
      smt2_incremental/smt_commands.cpp \
      smt2_incremental/smt_core_theory.cpp \
      smt2_incremental/smt_logics.cpp \
      smt2_incremental/smt_options.cpp \
      smt2_incremental/smt_response_validation.cpp \
      smt2_incremental/smt_responses.cpp \
      smt2_incremental/smt_solver_process.cpp \
      smt2_incremental/smt_sorts.cpp \
      smt2_incremental/smt_terms.cpp \
      smt2_incremental/smt_to_smt2_string.cpp \
      smt2_incremental/smt2_incremental_decision_procedure.cpp \
      # Empty last line

include ../common

ifneq ($(MINISAT2),)
ifeq ($(BUILD_ENV_),MSVC)
sat/satcheck_minisat2$(OBJEXT): sat/satcheck_minisat2.cpp
	$(CXX) $(CP_CXXFLAGS) /w /nologo /c /EHsc $< /Fo$@

$(MINISAT2)/minisat/simp/SimpSolver$(OBJEXT): $(MINISAT2)/minisat/simp/SimpSolver.cc
	$(CXX) $(CP_CXXFLAGS) /w /nologo /c /EHsc $< /Fo$@

$(MINISAT2)/minisat/core/Solver$(OBJEXT): $(MINISAT2)/minisat/core/Solver.cc
	$(CXX) $(CP_CXXFLAGS) /w /nologo /c /EHsc $< /Fo$@
endif
endif

ifneq ($(GLUCOSE),)
ifeq ($(BUILD_ENV_),MSVC)
sat/satcheck_glucose$(OBJEXT): sat/satcheck_glucose.cpp
	$(CXX) $(CP_CXXFLAGS) /w /nologo /c /EHsc $< /Fo$@

$(GLUCOSE)/simp/SimpSolver$(OBJEXT): $(GLUCOSE)/simp/SimpSolver.cc
	$(CXX) $(CP_CXXFLAGS) /w /nologo /c /EHsc $< /Fo$@

$(GLUCOSE)/core/Solver$(OBJEXT): $(GLUCOSE)/core/Solver.cc
	$(CXX) $(CP_CXXFLAGS) /w /nologo /c /EHsc $< /Fo$@
endif
endif

INCLUDES += -I .. \
  $(CHAFF_INCLUDE) $(BOOLEFORCE_INCLUDE) $(MINISAT_INCLUDE) $(MINISAT2_INCLUDE) \
  $(IPASIR_INCLUDE) \
  $(SQUOLEM2_INC) $(CUDD_INCLUDE) $(GLUCOSE_INCLUDE) \
	$(PICOSAT_INCLUDE) $(LINGELING_INCLUDE) $(CADICAL_INCLUDE)

CLEANFILES += solvers$(LIBEXT) \
  smt2_solver$(EXEEXT) smt2/smt2_solver$(OBJEXT) smt2/smt2_solver$(DEPEXT)

all: solvers$(LIBEXT) smt2_solver$(EXEEXT)

ifneq ($(SQUOLEM2),)
  CP_CXXFLAGS += -DHAVE_QBF_CORE
else
ifneq ($(CUDD),)
  CP_CXXFLAGS += -DHAVE_QBF_CORE
endif
endif

SOLVER_LIB = $(CHAFF_LIB) $(BOOLEFORCE_LIB) $(MINISAT_LIB) \
        $(MINISAT2_LIB) $(SQUOLEM2_LIB) $(CUDD_LIB) \
        $(PICOSAT_LIB) $(LINGELING_LIB) $(GLUCOSE_LIB) $(CADICAL_LIB)

SOLVER_OBJS = $(filter %$(OBJEXT), $(SOLVER_LIB))
ifneq ($(SOLVER_OBJS),)
-include $(SOLVER_OBJS:$(OBJEXT)=$(DEPEXT))
endif

###############################################################################

solvers$(LIBEXT): $(OBJ) $(SOLVER_LIB)
	$(LINKLIB)

-include smt2/smt2_solver$(DEPEXT)

smt2_solver$(EXEEXT): $(OBJ) smt2/smt2_solver$(OBJEXT) \
	../util/util$(LIBEXT) ../big-int/big-int$(LIBEXT) $(SOLVER_LIB)
	$(LINKBIN)
