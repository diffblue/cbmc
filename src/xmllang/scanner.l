%option 8bit nodefault
%option nounput

%{
#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

#include <ctype.h>
#include <string.h>
#include <stdlib.h>

#include "xml_parser.h"
#include "y.tab.h"

#define PARSER xml_parser

//static int keep;			/* To store start condition */

static char *word(char *s)
{
  char *buf;
  int i, k;
  for (k = 0; isspace(s[k]) || s[k] == '<'; k++) ;
  for (i = k; s[i] && ! isspace(s[i]); i++) ;
  buf = (char *)malloc((i - k + 1) * sizeof(char));
  strncpy(buf, &s[k], i - k);
  buf[i - k] = '\0';
  return buf;
}

%}


nl		(\r\n|\r|\n)
ws		[ \t\r\n]+
open		{nl}?"<"
close		">"{nl}?
namestart	[A-Za-z\200-\377_]
namechar	[A-Za-z\200-\377_0-9.:-]
esc		"&#"[0-9]+";"|"&#x"[0-9a-fA-F]+";"|"&"[a-zA-Z]+";"
name		{namestart}{namechar}*
data		([^<\n&]|\n[^<&]|\n{esc}|{esc})+
comment		{open}"!--"([^-]|"-"[^-])*"--"{close}
string		\"([^"&]|{esc})*\"|\'([^'&]|{esc})*\'

/*
 * The CONTENT mode is used for the content of elements, i.e.,
 * between the ">" and "<" of element tags.
 * The INITIAL mode is used outside the top level element
 * and inside markup.
 */

%s CONTENT
%s PI


%%

<INITIAL>{ws}		{/* skip */}
<INITIAL>"/"		{return SLASH;}
<INITIAL>"="		{return EQ;}
<INITIAL>{close}	{BEGIN(CONTENT); return CLOSE;}
<INITIAL>{name}		{yyxmllval.s=strdup(yytext); return NAME;}
<INITIAL>{string}	{yyxmllval.s=strdup(yytext); return VALUE;}
<INITIAL>"?"{close}	{BEGIN(INITIAL); return ENDPI;}

{open}{ws}?{name}	{BEGIN(INITIAL); yyxmllval.s=word(yytext); return START;}
{open}{ws}?"/"		{BEGIN(INITIAL); return END;}
{open}"?xml"		{BEGIN(INITIAL); return STARTXMLDECL;}
{open}"?"		{BEGIN(PI); yyxmllval.s=word(yytext); return STARTPI;}
{comment}		{yyxmllval.s=strdup(yytext); return COMMENT;}

<PI>"?"{close}		{BEGIN(INITIAL); return ENDPI;}
<PI>{data}		{yyxmllval.s=strdup(yytext); return DATA;}

<CONTENT>{data}		{yyxmllval.s=strdup(yytext); return DATA;}

.			{ yyxmlerror("unexpected charater"); }
{nl}			{/* skip, must be an extra one at EOF */;}

%%

int yywrap() { return 1; }
