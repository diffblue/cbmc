%{
#include <string.h>

#include "xml_parser.h"

int yyxmllex();
extern char *yyxmltext;

int yyxmlerror(const std::string &error)
{
  xml_parser.parse_error(error, yyxmltext);
  return 0;
}

%}

%error-verbose

%union {char *s;}

%token STARTXMLDECL
%token VERSION STARTPI ENDPI EQ SLASH CLOSE END
%token <s> ENCODING NAME VALUE DATA COMMENT START
%type <s> name_opt

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
 : COMMENT			{ free($1); }
 | PI
 ;

PI
 : STARTPI NAME
   { free($2); xml_parser.stack.push_back(&xml_parser.parse_tree.xml); }
   attribute_seq_opt
   { xml_parser.stack.pop_back(); }
   ENDPI
 ;	

element
 : START			{ xml_parser.current().name=$1;
                                  free($1);
				}
   attribute_seq_opt
   empty_or_content
 ;

empty_or_content
 : SLASH CLOSE			{ }
 | CLOSE			{ }
   content END name_opt CLOSE	{ free($5); }
 ;

content
 : content DATA			{ xml_parser.current().data+=xmlt::unescape($2); free($2); }
 | content misc
 | content
   { xml_parser.new_level(); }
   element
   { xml_parser.stack.pop_back(); }
 | /*empty*/
 ;

name_opt
 : NAME				{ $$=$1; }
 | /*empty*/			{ $$=strdup(""); }
 ;

attribute_seq_opt
 : attribute_seq_opt attribute
 | /*empty*/
 ;

attribute
 : NAME EQ VALUE		{ xml_parser.current().set_attribute(
                                    xmlt::unescape($1), xmlt::unescape($3));
                                  free($1); free($3);}
 ;

