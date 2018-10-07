SRC = adjust_float_expressions.cpp \
      builtin_functions.cpp \
      class_hierarchy.cpp \
      class_identifier.cpp \
      compute_called_functions.cpp \
      destructor.cpp \
      elf_reader.cpp \
      format_strings.cpp \
      generate_function_bodies.cpp \
      goto_asm.cpp \
      goto_clean_expr.cpp \
      goto_convert.cpp \
      goto_convert_exceptions.cpp \
      goto_convert_function_call.cpp \
      goto_convert_functions.cpp \
      goto_convert_side_effect.cpp \
      goto_function.cpp \
      goto_functions.cpp \
      goto_inline_class.cpp \
      goto_inline.cpp \
      goto_program.cpp \
      goto_trace.cpp \
      graphml_witness.cpp \
      initialize_goto_model.cpp \
      instrument_preconditions.cpp \
      interpreter.cpp \
      interpreter_evaluate.cpp \
      json_goto_trace.cpp \
      lazy_goto_model.cpp \
      link_goto_model.cpp \
      link_to_library.cpp \
      loop_ids.cpp \
      mm_io.cpp \
      osx_fat_reader.cpp \
      parameter_assignments.cpp \
      pointer_arithmetic.cpp \
      printf_formatter.cpp \
      property_checker.cpp \
      read_bin_goto_object.cpp \
      read_goto_binary.cpp \
      rebuild_goto_start_function.cpp \
      remove_asm.cpp \
      remove_calls_no_body.cpp \
      remove_complex.cpp \
      remove_const_function_pointers.cpp \
      remove_function_pointers.cpp \
      remove_returns.cpp \
      remove_skip.cpp \
      remove_unreachable.cpp \
      remove_unused_functions.cpp \
      remove_vector.cpp \
      remove_virtual_functions.cpp \
      rewrite_union.cpp \
      replace_calls.cpp \
      resolve_inherited_component.cpp \
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
