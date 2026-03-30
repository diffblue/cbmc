%{
#include <cstring>

#include "xml_parser.h"

int yyxmllex(void *);
char *yyxmlget_text(void *);

int yyxmlerror(xml_parsert &xml_parser, void *scanner, const std::string &error)
{
  xml_parser.parse_error(error, yyxmlget_text(scanner));
  return 0;
}

#ifdef _MSC_VER
// possible loss of data
#pragma warning(disable:4242)
// possible loss of data
#pragma warning(disable:4244)
// signed/unsigned mismatch
#pragma warning(disable:4365)
// switch with default but no case labels
#pragma warning(disable:4065)
// unreachable code
#pragma warning(disable:4702)
#endif

// Bison-generated yydestruct only handles symbols with %destructor;
// suppress the warning about unhandled enum values in that switch.
#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wswitch-enum"
#endif
%}

%parse-param {xml_parsert &xml_parser}
%parse-param {void *scanner}
%lex-param {void *scanner}

%union {char *s;}

%token STARTXMLDECL
%token VERSION ENDPI EQ SLASH CLOSE END
%token <s> ENCODING NAME VALUE DATA COMMENT START STARTPI
%type <s> name_opt

// Memory management: ensure allocated string tokens are freed during error recovery
%destructor { free($$); } ENCODING NAME VALUE DATA COMMENT START STARTPI name_opt

%%

document
 : prolog element misc_seq_opt
 ;

prolog
 : XMLDecl_opt misc_seq_opt
 ;

XMLDecl_opt
 : STARTXMLDECL
   { xml_parser.stack.push_back(&xml_parser.parse_tree.xml); }
   attribute_seq_opt
   { xml_parser.stack.pop_back(); }
   ENDPI
 | /*empty*/
 ;

misc_seq_opt
 : misc_seq_opt misc
 | /*empty*/
 ;

misc
 : COMMENT      { free($1); }
 | PI
 ;

PI
 : STARTPI NAME
   { xml_parser.stack.push_back(&xml_parser.parse_tree.xml); }
   attribute_seq_opt
   { xml_parser.stack.pop_back(); }
   ENDPI
   { free($1); free($2); }
 ;

element
 : START   { xml_parser.current().name=$1; }
   attribute_seq_opt
   empty_or_content
   { free($1); }
 ;

empty_or_content
 : SLASH CLOSE  { }
 | CLOSE  { }
   content END name_opt CLOSE  { free($5); }
 ;

content
 : content DATA  { xml_parser.current().data+=xmlt::unescape($2); free($2); }
 | content misc
 | content
   { xml_parser.new_level(); }
   element
   { xml_parser.stack.pop_back(); }
 | /*empty*/
 ;

name_opt
 : NAME  { $$=$1; }
 | /*empty*/  { $$=strdup(""); }
 ;

attribute_seq_opt
 : attribute_seq_opt attribute
 | /*empty*/
 ;

attribute
 : NAME EQ VALUE  { xml_parser.current().set_attribute(
                                    xmlt::unescape($1), xmlt::unescape($3));
                                  free($1); free($3);}
 ;


%%

#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic pop
#endif
