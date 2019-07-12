SRC = graphml.cpp \
      xml_interface.cpp \
      xml_lex.yy.cpp \
      xml_parse_tree.cpp \
      xml_parser.cpp \
      xml_y.tab.cpp \
      # Empty last line
INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES=xmllang$(LIBEXT) xml_y.tab.h xml_y.tab.cpp xml_lex.yy.cpp \
           xml_y.tab.cpp.output xml_y.output

all: xmllang$(LIBEXT)

###############################################################################

xmllang$(LIBEXT): $(OBJ)
	$(LINKLIB)

xml_y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyxml parser.y --defines=xml_y.tab.h -o $@

xml_y.tab.h: xml_y.tab.cpp

xml_lex.yy.cpp: scanner.l
	$(LEX) -Pyyxml -o$@ scanner.l

generated_files: xml_lex.yy.cpp xml_y.tab.cpp xml_y.tab.h

# extra dependencies
xml_y.tab$(OBJEXT): xml_y.tab.cpp xml_y.tab.h
xml_lex.yy$(OBJEXT): xml_y.tab.cpp xml_lex.yy.cpp xml_y.tab.h
