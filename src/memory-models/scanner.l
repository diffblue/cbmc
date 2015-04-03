%option 8bit nodefault
%option nounput
%option noinput

%{
#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

#include <ctype.h>
#include <string.h>
#include <stdlib.h>

#include "mm_parser.h"
#include "mm_y.tab.h"

#define PARSER mm_parser

%}

nl		(\r\n|\r|\n)
ws		[ \t\r\n]+

%s GRAMMAR

%%

GRAMMAR {

letter          [a-z]|[A-Z]
digit		[0-9]
identifier	({letter}({letter}|{digit}|"_"|"."|"-")*)



.		{ yyxmlerror("unexpected character"); }
}

%%

int yywrap() { return 1; }
