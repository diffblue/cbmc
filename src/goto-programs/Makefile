SRC = adjust_float_expressions.cpp \
      class_hierarchy.cpp \
      class_identifier.cpp \
      compute_called_functions.cpp \
      elf_reader.cpp \
      ensure_one_backedge_per_target.cpp \
      goto_check.cpp \
      goto_function.cpp \
      goto_functions.cpp \
      goto_inline_class.cpp \
      goto_inline.cpp \
      goto_instruction_code.cpp \
      goto_program.cpp \
      goto_trace.cpp \
      graphml_witness.cpp \
      initialize_goto_model.cpp \
      instrument_preconditions.cpp \
      interpreter.cpp \
      interpreter_evaluate.cpp \
      json_expr.cpp \
      json_goto_trace.cpp \
      label_function_pointer_call_sites.cpp \
      link_goto_model.cpp \
      loop_ids.cpp \
      mm_io.cpp \
      name_mangler.cpp \
      osx_fat_reader.cpp \
      parameter_assignments.cpp \
      pointer_arithmetic.cpp \
      process_goto_program.cpp \
      read_bin_goto_object.cpp \
      read_goto_binary.cpp \
      rebuild_goto_start_function.cpp \
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
      restrict_function_pointers.cpp \
      rewrite_rw_ok.cpp \
      rewrite_union.cpp \
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
      structured_trace_util.cpp \
      system_library_symbols.cpp \
      validate_code.cpp \
      validate_goto_model.cpp \
      vcd_goto_trace.cpp \
      wp.cpp \
      write_goto_binary.cpp \
      xml_expr.cpp \
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
