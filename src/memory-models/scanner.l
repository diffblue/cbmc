%option 8bit nodefault
%option nounput
%option noinput

%{
#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

#define YYSTYPE unsigned
#define PARSER mm_parser

#include "mm_parser.h"
#include "mm_y.tab.h"

#define loc() \
  { newstack(yymmlval); PARSER.set_source_location(stack(yymmlval)); }

%}

nl		(\r\n|\r|\n)
ws		(" "|\t|\r|\n)
letter          [a-z]|[A-Z]
digit		[0-9]
number		{digit}+
identifier	{letter}({letter}|{digit}|"_"|"."|"-")*
tagidentifier	"'"{letter}({letter}|{digit}|"_"|"."|"-")*
string          ["][^"\n]*["]
comment         "(*"(.|\n)*"*)"

%%

{comment}       { /* ignore */ }
{string}        { loc(); return TOK_STRING; }
"^-1"		{ loc(); return TOK_INVERSE; }
"->"		{ loc(); return TOK_MAPS_TO; }
"++"		{ loc(); return TOK_PLUSPLUS; }
"||"		{ loc(); return TOK_OROR; }
"flag"          { loc(); return TOK_FLAG; }
"let"		{ loc(); return TOK_LET; }
"in"		{ loc(); return TOK_IN; }
"match"		{ loc(); return TOK_MATCH; }
"with"		{ loc(); return TOK_WITH; }
"acyclic"       { loc(); return TOK_ACYCLIC; }
"irreflexive"   { loc(); return TOK_IRRELFEXIVE; }
"empty"         { loc(); return TOK_EMPTY; }
"include"	{ /* TODO */ }
"fun"		{ loc(); return TOK_FUN; }
"rec"           { loc(); return TOK_REC; }
"begin"         { loc(); return TOK_BEGIN; }
"end"           { loc(); return TOK_END; }
"show"          { loc(); return TOK_SHOW; }
"unshow"        { loc(); return TOK_UNSHOW; }
"procedure"     { loc(); return TOK_PROCEDURE; }
"enum"          { loc(); return TOK_ENUM; }
"forall"        { loc(); return TOK_FORALL; }
"as"            { loc(); return TOK_AS; }
{identifier}	{ loc(); return TOK_IDENTIFIER; }
{tagidentifier}	{ loc(); return TOK_TAG_IDENTIFIER; }
{number}	{ loc(); return TOK_NUMBER; }

{nl}		{ /* ignore */ }
{ws}		{ /* ignore */ }
.		{ loc(); return yytext[0]; }
<<EOF>>		{ yyterminate(); /* done! */ }

%%

int yywrap() { return 1; }

int yymmerror(const std::string &error)
{
  mm_parser.parse_error(error, yytext);
  return 0;
}

