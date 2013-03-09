SRC = goto_convert.cpp goto_convert_function_call.cpp \
      goto_convert_side_effect.cpp goto_program.cpp basic_blocks.cpp \
      remove_function_pointers.cpp goto_functions.cpp goto_inline.cpp \
      remove_skip.cpp goto_convert_functions.cpp string_instrumentation.cpp \
      builtin_functions.cpp show_claims.cpp destructor.cpp set_claims.cpp \
      reachability_slicer.cpp read_goto_binary.cpp goto_asm.cpp elf_reader.cpp \
      string_abstraction.cpp \
      goto_program_serialization.cpp goto_function_serialization.cpp \
      read_bin_goto_object.cpp goto_program_irep.cpp interpreter.cpp \
      interpreter_evaluate.cpp flow_insensitive_analysis.cpp \
      format_strings.cpp loop_ids.cpp pointer_arithmetic.cpp \
      goto_program_template.cpp write_goto_binary.cpp remove_unreachable.cpp \
      remove_unused_functions.cpp \
      wp.cpp goto_rw.cpp goto_clean_expr.cpp safety_checker.cpp \
      compute_called_functions.cpp link_to_library.cpp \
      remove_return_values.cpp

INCLUDES= -I .. -I ../util

include ../config.inc
include ../common

LIBS = ../ansi-c/ansi-c$(LIBEXT) \
       ../cpp/cpp$(LIBEXT) \
       ../linking/linking$(LIBEXT) \
       ../util/util$(LIBEXT) \
	../big-int/bigint$(OBJEXT) goto-programs$(LIBEXT) \
	../pointer-analysis/pointer-analysis$(LIBEXT) \
	../langapi/langapi$(LIBEXT)

CLEANFILES = goto-programs$(LIBEXT) test_wp$(EXEEXT)

all: goto-programs$(LIBEXT)

###############################################################################

goto-programs$(LIBEXT): $(OBJ)
	$(LINKLIB)

test_wp$(EXEEXT): test_wp$(OBJEXT) goto-programs$(LIBEXT)
	$(LINKBIN)

