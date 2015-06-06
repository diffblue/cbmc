SRC = java_bytecode_language.cpp java_bytecode_parse_tree.cpp \
      java_bytecode_typecheck.cpp expr2java.cpp \
      java_bytecode_convert.cpp java_types.cpp java_entry_point.cpp \
      java_bytecode_typecheck_code.cpp java_bytecode_typecheck_expr.cpp \
      java_bytecode_typecheck_type.cpp java_bytecode_internal_additions.cpp \
      java_bytecode_load_class.cpp java_bytecode_vtable.cpp \
      java_bytecode_parser.cpp bytecode_info.cpp \
      java_class_loader.cpp

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = java_bytecode$(LIBEXT)

all: java_bytecode$(LIBEXT)

###############################################################################

java_bytecode$(LIBEXT): $(OBJ)
	$(LINKLIB)

