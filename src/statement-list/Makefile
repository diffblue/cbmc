SRC = converters/convert_bool_literal.cpp \
      converters/convert_dint_literal.cpp \
      converters/convert_int_literal.cpp \
      converters/convert_real_literal.cpp \
      converters/convert_string_value.cpp \
      converters/expr2statement_list.cpp \
      converters/statement_list_types.cpp \
      statement_list_entry_point.cpp \
      statement_list_language.cpp \
      statement_list_lex.yy.cpp \
      statement_list_parse_tree.cpp \
      statement_list_parse_tree_io.cpp \
      statement_list_parser.cpp \
      statement_list_typecheck.cpp \
      statement_list_y.tab.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = statement-list$(LIBEXT) \
  statement_list_y.tab.h statement_list_y.tab.cpp \
  statement_list_lex.yy.cpp statement_list_y.tab.cpp.output \
  statement_list_y.output

all: statement-list$(LIBEXT)

###############################################################################

statement_list_y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyystatement_list parser.y --defines=statement_list_y.tab.h -o $@

statement_list_y.tab.h: statement_list_y.tab.cpp

statement_list_lex.yy.cpp: scanner.l
	$(LEX) -Pyystatement_list -o$@ scanner.l

# extra dependencies
statement_list_y.tab$(OBJEXT): statement_list_y.tab.cpp \
  statement_list_y.tab.h
statement_list_lex.yy$(OBJEXT): statement_list_y.tab.cpp \
  statement_list_lex.yy.cpp statement_list_y.tab.h

###############################################################################

generated_files: statement_list_y.tab.cpp statement_list_lex.yy.cpp \
  statement_list_y.tab.h

###############################################################################

statement-list$(LIBEXT): $(OBJ)
	$(LINKLIB)

