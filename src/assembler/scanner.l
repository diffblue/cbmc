%option nounput
%option noinput
%option nounistd
%option never-interactive
%option noyywrap
%option reentrant
%option extra-type="assembler_parsert *"

%{

#if defined _MSC_VER
// signed/unsigned mismatch
#pragma warning(disable:4365)
// macro re-definition: flex conditonally defines INT32_MAX et al. and thus
// they are set before library headers get to define them
#pragma warning(disable:4005)
#endif

#define PARSER (*yyextra)
#define YYSTYPE unsigned
#undef  ECHO
#define ECHO

#include "assembler_parser.h"

#include <util/pragma_wsign_compare.def> // IWYU pragma: keep
#include <util/pragma_wnull_conversion.def> // IWYU pragma: keep
#include <util/pragma_wdeprecated_register.def> // IWYU pragma: keep

/*** macros for easier rule definition **********************************/
%}

delimiter       [ \t\b\r]
newline         [\n\f\v]|"\\\n"
whitespace      {delimiter}+
ws              {delimiter}*
ws_or_newline   ({delimiter}|{newline})*
ucletter        [A-Z]
lcletter        [a-z]
letter          ({ucletter}|{lcletter})
digit           [0-9]
bindigit        [01]
octdigit        [0-7]
hexdigit        [0-9a-fA-F]
identifier      (({letter}|"_"|"$"|".")({letter}|{digit}|"_"|"$"|".")*)
integer         {digit}+
binary          {bindigit}+
bininteger      "0"[bB]{bindigit}+{int_suffix}
decinteger      [1-9]{digit}*{int_suffix}
octinteger      "0"{octdigit}*{int_suffix}
hexinteger      "0"[xX]{hexdigit}+{int_suffix}
integer_s       {decinteger}|{bininteger}|{octinteger}|{hexinteger}
octchar         "\\"{octdigit}{1,3}
hexchar         "\\x"{hexdigit}+

escape_sequence [\\][^\n]
c_char [^'\\\n]|{escape_sequence}
s_char [^"\\\n]|{escape_sequence}

char_lit        ("L"|"u"|"U")?[']{c_char}+[']
string_lit      ("L"|"u"|"U"|"u8")?["]{s_char}*["]

%x GRAMMAR
%x LINE_COMMENT

%%

<INITIAL>.|\n   { BEGIN(GRAMMAR);
                  yyless(0); /* start again with this character */
                }

<GRAMMAR>"#"    { PARSER.new_instruction(); BEGIN(LINE_COMMENT); } /* begin comment state */

<LINE_COMMENT>{
   \n           { BEGIN(GRAMMAR); } /* end comment state, back GRAMMAR */
   .*           { } /* all characters within comments are ignored */
}

<GRAMMAR>{newline} { PARSER.new_instruction(); }
<GRAMMAR>";"    { PARSER.new_instruction(); }
<GRAMMAR>{whitespace} { } /* skipped */

 /*** keywords ***/

<GRAMMAR>{
".data"         { }
}

 /*** rest ***/

<GRAMMAR>{
{ws}            { /* ignore */ }
{identifier}    { irept identifier(ID_symbol);
                  identifier.set(ID_identifier, yytext);
                  PARSER.add_token(identifier);
                }

">>"            { PARSER.add_token(irept(ID_shr)); }
"<<"            { PARSER.add_token(irept(ID_shl)); }
.               { std::string s;
                  s+=yytext[0];
                  PARSER.add_token(irept(s));
                }
}

<<EOF>>         { yyterminate(); /* done! */ }
