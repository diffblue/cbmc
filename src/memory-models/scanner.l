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

unsigned comment_nesting;

#include <util/pragma_wsign_compare.def>
#include <util/pragma_wnull_conversion.def>
#include <util/pragma_wdeprecated_register.def>

%}

%x GRAMMAR
%s COMMENT

nl              (\r\n|\r|\n)
ws              (" "|\t|\r|\n)
letter          [a-z]|[A-Z]
digit           [0-9]
number          {digit}+
identifier      {letter}({letter}|{digit}|"_"|"."|"-"|"'")*
tagidentifier   "'"{letter}({letter}|{digit}|"_"|"."|"-"|"'")*
string          ["][^"\n]*["]
cppcomment      "//".*\n

%%

<INITIAL>.|\n   { BEGIN(GRAMMAR); yyless(0); }

<GRAMMAR>{
"(*"            { comment_nesting=1; BEGIN(COMMENT); }
{cppcomment}    { /* ignore */ }
{string}        { loc(); return TOK_STRING; }
"^-1"           { loc(); return TOK_INVERSE; }
"->"            { loc(); return TOK_MAPS_TO; }
"++"            { loc(); return TOK_PLUSPLUS; }
"||"            { loc(); return TOK_OROR; }
"flag"          { loc(); return TOK_FLAG; }
"let"           { loc(); return TOK_LET; }
"in"            { loc(); return TOK_IN; }
"do"            { loc(); return TOK_DO; }
"match"         { loc(); return TOK_MATCH; }
"with"          { loc(); return TOK_WITH; }
"from"          { loc(); return TOK_FROM; }
"acyclic"       { loc(); return TOK_ACYCLIC; }
"irreflexive"   { loc(); return TOK_IRRELFEXIVE; }
"empty"         { loc(); return TOK_EMPTY; }
"include"       { loc(); return TOK_INCLUDE; }
"fun"           { loc(); return TOK_FUN; }
"rec"           { loc(); return TOK_REC; }
"begin"         { loc(); return TOK_BEGIN; }
"call"          { loc(); return TOK_CALL; }
"end"           { loc(); return TOK_END; }
"show"          { loc(); return TOK_SHOW; }
"unshow"        { loc(); return TOK_UNSHOW; }
"procedure"     { loc(); return TOK_PROCEDURE; }
"enum"          { loc(); return TOK_ENUM; }
"forall"        { loc(); return TOK_FORALL; }
"as"            { loc(); return TOK_AS; }
"and"           { loc(); return TOK_AND; }
"∩"             { loc(); return TOK_SET_INTERSECTION; }
"∪"             { loc(); return TOK_SET_UNION; }
"⨯"             { loc(); return TOK_CROSS_PRODUCT; }
"∅"             { loc(); return TOK_EMPTY_SET; }
{identifier}    { loc(); return TOK_IDENTIFIER; }
{tagidentifier} { loc(); return TOK_TAG_IDENTIFIER; }
{number}        { loc(); return TOK_NUMBER; }

{nl}            { /* ignore */ }
{ws}            { /* ignore */ }
.               { loc(); return yytext[0]; }
<<EOF>>         { yyterminate(); /* done! */ }
}

<COMMENT>{
"*)"            { comment_nesting--;
                  if(comment_nesting==0) BEGIN(GRAMMAR); }
"(*"            { comment_nesting++; }
\n|.            { /* ignore */ }
}

%%

int yywrap() { return 1; }

int yymmerror(const std::string &error)
{
  mm_parser.parse_error(error, yytext);
  return 0;
}

