SRC = basic_blocks.cpp \
      builtin_functions.cpp \
      class_hierarchy.cpp \
      class_identifier.cpp \
      compute_called_functions.cpp \
      convert_nondet.cpp \
      destructor.cpp \
      elf_reader.cpp \
      format_strings.cpp \
      initialize_goto_model.cpp \
      goto_asm.cpp \
      goto_clean_expr.cpp \
      goto_convert.cpp \
      goto_convert_exceptions.cpp \
      goto_convert_function_call.cpp \
      goto_convert_functions.cpp \
      goto_convert_side_effect.cpp \
      goto_functions.cpp \
      goto_inline.cpp \
      goto_inline_class.cpp \
      goto_program.cpp \
      goto_program_irep.cpp \
      goto_program_template.cpp \
      goto_trace.cpp \
      graphml_witness.cpp \
      interpreter.cpp \
      interpreter_evaluate.cpp \
      json_goto_trace.cpp \
      link_to_library.cpp \
      loop_ids.cpp \
      mm_io.cpp \
      osx_fat_reader.cpp \
      parameter_assignments.cpp \
      pointer_arithmetic.cpp \
      property_checker.cpp \
      read_bin_goto_object.cpp \
      read_goto_binary.cpp \
      remove_asm.cpp \
      remove_complex.cpp \
      remove_const_function_pointers.cpp \
      remove_exceptions.cpp \
      remove_function_pointers.cpp \
      remove_instanceof.cpp \
      remove_returns.cpp \
      remove_skip.cpp \
      remove_static_init_loops.cpp \
      remove_unreachable.cpp \
      remove_unused_functions.cpp \
      remove_vector.cpp \
      remove_virtual_functions.cpp \
      replace_java_nondet.cpp \
      safety_checker.cpp \
      set_properties.cpp \
      show_goto_functions.cpp \
      show_goto_functions_json.cpp \
      show_goto_functions_xml.cpp \
      show_properties.cpp \
      show_symbol_table.cpp \
      slice_global_inits.cpp \
      string_abstraction.cpp \
      string_instrumentation.cpp \
      string_refine_preprocess.cpp \
      system_library_symbols.cpp \
      vcd_goto_trace.cpp \
      wp.cpp \
      write_goto_binary.cpp \
      xml_goto_trace.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = goto-programs$(LIBEXT)

all: goto-programs$(LIBEXT)

###############################################################################

goto-programs$(LIBEXT): $(OBJ)
	$(LINKLIB)
