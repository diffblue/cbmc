SRC = java_bytecode_language.cpp java_bytecode_parse_tree.cpp \
      java_bytecode_typecheck.cpp expr2java.cpp \
      java_bytecode_convert_class.cpp java_types.cpp java_entry_point.cpp \
      java_bytecode_typecheck_code.cpp java_bytecode_typecheck_expr.cpp \
      java_bytecode_typecheck_type.cpp java_bytecode_internal_additions.cpp \
      java_root_class.cpp java_bytecode_parser.cpp bytecode_info.cpp \
      java_class_loader.cpp jar_file.cpp java_object_factory.cpp \
      java_bytecode_convert_method.cpp java_local_variable_table.cpp \
      java_pointer_casts.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = java_bytecode$(LIBEXT)

ifneq ($(wildcard $(LIBZIPINC)),)
  INCLUDES += -I $(LIBZIPINC)
  CP_CXXFLAGS += -DHAVE_LIBZIP
endif

all: java_bytecode$(LIBEXT)

###############################################################################

java_bytecode$(LIBEXT): $(OBJ)
	$(LINKLIB)
