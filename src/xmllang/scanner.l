%option 8bit nodefault
%option nounput
%option noinput
%option nounistd
%option never-interactive

%{

#if defined _MSC_VER
// signed/unsigned mismatch
#pragma warning(disable:4365)
// macro re-definition: flex conditonally defines INT32_MAX et al. and thus
// they are set before library headers get to define them
#pragma warning(disable:4005)
#endif

#include <cctype>
#include <cstring>
#include <cstdlib>

#include "xml_parser.h"
#include "xml_y.tab.h"

#define PARSER xml_parser

//static int keep;  /* To store start condition */

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

#include <util/pragma_wsign_compare.def>
#include <util/pragma_wnull_conversion.def>
#include <util/pragma_wdeprecated_register.def>

%}


nl         (\r\n|\r|\n)
ws         [ \t\r\n]+
open       {nl}?"<"
close      ">"{nl}?
namestart  [A-Za-z\200-\377_]
namechar   [A-Za-z\200-\377_0-9.:-]
esc        "&#"[0-9]+";"|"&#x"[0-9a-fA-F]+";"|"&"[a-zA-Z]+";"
name       {namestart}{namechar}*
data       ([^<\n&]|\n[^<&]|\n{esc}|{esc})+
comment    {open}"!--"([^-]|"-"[^-])*"--"{close}
string     \"([^"&]|{esc})*\"|\'([^'&]|{esc})*\'

/*
 * The CONTENT mode is used for the content of elements, i.e.,
 * between the ">" and "<" of element tags.
 * The INITIAL mode is used outside the top level element
 * and inside markup.
 */

%s CONTENT
%s PI
%s DTD

%%

<INITIAL,PI>{ws}  {/* skip */}
<INITIAL>"/"      {return SLASH;}
<INITIAL,PI>"="   {return EQ;}
<INITIAL>{close}  {BEGIN(CONTENT); return CLOSE;}
<INITIAL,PI>{name}    {yyxmllval.s=strdup(yytext); return NAME;}
<INITIAL,PI>{string}  {yyxmllval.s=strdup(yytext); return VALUE;}
<INITIAL,PI>"?"{close}  {BEGIN(INITIAL); return ENDPI;}

{open}{ws}?{name} {BEGIN(INITIAL); yyxmllval.s=word(yytext); return START;}
{open}{ws}?"/"    {BEGIN(INITIAL); return END;}
{open}"?xml"      {BEGIN(INITIAL); return STARTXMLDECL;}
{open}"?"         {BEGIN(PI); yyxmllval.s=word(yytext); return STARTPI;}
{comment}         {yyxmllval.s=strdup(yytext); return COMMENT;}

<CONTENT>{data}   {yyxmllval.s=strdup(yytext); return DATA;}

<INITIAL>{open}"!"{ws}?"DOCTYPE"   {BEGIN(DTD); /* skip */}
<DTD>.            {/* skip */}
<DTD>\]{close}    {BEGIN(INITIAL); /* skip */}

.                 { yyxmlerror("unexpected character"); }
{nl}              {/* skip, must be an extra one at EOF */;}

%%

int yywrap() { return 1; }
