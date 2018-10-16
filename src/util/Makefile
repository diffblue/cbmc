SRC = arith_tools.cpp \
      array_name.cpp \
      base_type.cpp \
      bv_arithmetic.cpp \
      byte_operators.cpp \
      c_types.cpp \
      cmdline.cpp \
      config.cpp \
      cout_message.cpp \
      decision_procedure.cpp \
      dstring.cpp \
      endianness_map.cpp \
      expr.cpp \
      expr_initializer.cpp \
      expr_util.cpp \
      exception_utils.cpp \
      file_util.cpp \
      find_macros.cpp \
      find_symbols.cpp \
      fixedbv.cpp \
      format_constant.cpp \
      format_expr.cpp \
      format_number_range.cpp \
      format_type.cpp \
      fresh_symbol.cpp \
      get_base_name.cpp \
      get_module.cpp \
      guard.cpp \
      identifier.cpp \
      ieee_float.cpp \
      invariant.cpp \
      irep.cpp \
      irep_hash.cpp \
      irep_hash_container.cpp \
      irep_ids.cpp \
      irep_serialization.cpp \
      invariant_utils.cpp \
      json.cpp \
      json_expr.cpp \
      json_irep.cpp \
      json_stream.cpp \
      lispexpr.cpp \
      lispirep.cpp \
      mathematical_types.cpp \
      memory_info.cpp \
      merge_irep.cpp \
      message.cpp \
      mp_arith.cpp \
      namespace.cpp \
      nondet.cpp \
      options.cpp \
      parse_options.cpp \
      parser.cpp \
      pointer_offset_size.cpp \
      pointer_predicates.cpp \
      rational.cpp \
      rational_tools.cpp \
      ref_expr_set.cpp \
      refined_string_type.cpp \
      rename.cpp \
      rename_symbol.cpp \
      replace_expr.cpp \
      replace_symbol.cpp \
      run.cpp \
      signal_catcher.cpp \
      simplify_expr.cpp \
      simplify_expr_array.cpp \
      simplify_expr_boolean.cpp \
      simplify_expr_floatbv.cpp \
      simplify_expr_int.cpp \
      simplify_expr_pointer.cpp \
      simplify_expr_struct.cpp \
      simplify_utils.cpp \
      source_location.cpp \
      ssa_expr.cpp \
      std_code.cpp \
      std_expr.cpp \
      std_types.cpp \
      string2int.cpp \
      string_constant.cpp \
      string_container.cpp \
      string_hash.cpp \
      string_utils.cpp \
      symbol.cpp \
      symbol_table_base.cpp \
      symbol_table.cpp \
      tempdir.cpp \
      tempfile.cpp \
      threeval.cpp \
      timestamper.cpp \
      type.cpp \
      type_eq.cpp \
      typecheck.cpp \
      ui_message.cpp \
      unicode.cpp \
      union_find.cpp \
      union_find_replace.cpp \
      unwrap_nested_exception.cpp \
      version.cpp \
      xml.cpp \
      xml_expr.cpp \
      xml_irep.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

# get version from git
GIT_INFO = $(shell git describe --tags --always --dirty || echo "n/a")
RELEASE_INFO = const char *CBMC_VERSION="$(CBMC_VERSION) ($(GIT_INFO))";
GIT_INFO_FILE = version.cpp

$(GIT_INFO_FILE):
	echo '$(RELEASE_INFO)' > $@

generated_files: $(GIT_INFO_FILE)

# mark the actually generated file as a phony target to enforce a rebuild - but
# only if the version information has changed!
KNOWN_RELEASE_INFO = $(shell cat $(GIT_INFO_FILE) 2>/dev/null)
ifneq ($(RELEASE_INFO), $(KNOWN_RELEASE_INFO))
.PHONY: $(GIT_INFO_FILE)
endif

CLEANFILES = $(GIT_INFO_FILE) util$(LIBEXT)

all: util$(LIBEXT) $(GIT_INFO_FILE)

util$(LIBEXT): $(OBJ)
	$(LINKLIB)
