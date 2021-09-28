%option nounput
%option noinput

HexDigit                        [[:xdigit:]]
UnicodeEscape                   \\u+{HexDigit}{HexDigit}{HexDigit}{HexDigit}
OctalEscape                     \\([0-7]{1,2}|[0-3][0-7]{2})
EscapeSequence                  \\[btnfr"'\\]|{OctalEscape}|{UnicodeEscape}
LineTerminator                  \n|\r\n?
WhiteSpace                      [ \t\f]+

TraditionalComment              "/*"([^*]|(\*+[^*/]))*\*+\/
EndOfLineComment                "//"[^\r\n]*

IdentifierStart                 ([A-Z]|[a-z]|"_"|"$"|[\x80-\xff])
IdentifierPart                  ({IdentifierStart}|[0-9])

Identifier                      {IdentifierStart}{IdentifierPart}*

IntegerTypeSuffix               [lL]?

DecimalNumeral                  0|[1-9][0-9_]*
DecimalIntegerLiteral           {DecimalNumeral}{IntegerTypeSuffix}?

HexNumeral                      0[xX][[:xdigit:]_]+
HexIntegerLiteral               {HexNumeral}{IntegerTypeSuffix}?

OctalNumeral                    0[0-7_]+
OctalIntegerLiteral             {OctalNumeral}{IntegerTypeSuffix}?

BinaryNumeral                   0[bB][01_]+
BinaryIntegerLiteral            {BinaryNumeral}{IntegerTypeSuffix}?

IntegerLiteral                  {DecimalIntegerLiteral}|{HexIntegerLiteral}|{OctalIntegerLiteral}|{BinaryIntegerLiteral}

FloatTypeSuffix                 [fFdD]
DecimalFloatingPointLiteral     ([0-9_]+\.?[0-9_]*|\.[0-9_]+)([eE][-+]{DecimalNumeral}+)?{FloatTypeSuffix}?
HexadecimalFloatingPointLiteral 0[xX][[:xdigit:]_]*\.[[:xdigit:]_]*[pP][-+]{DecimalNumeral}+{FloatTypeSuffix}?
FloatingPointLiteral            {DecimalFloatingPointLiteral}|{HexadecimalFloatingPointLiteral}

CharacterLiteral                '([^'\\\n]|{EscapeSequence})'

StringLiteral                   \"([^"\\\n]|{EscapeSequence})*\"

Separator                       [(){}\[\];,.@]|"..."|::

Operator                        [-+=<>*/&|^%!~?:]|[-=<>!+*/&|^%]=|&&|"||"|"++"|--|<<=?|>>>?=?

PreprocessorStart               {WhiteSpace}*"#"{WhiteSpace}*
PreprocessorDirective           {PreprocessorStart}[^\r\n]*

%{
#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

#include <util/pragma_wdeprecated_register.def>

#include <set>
#include <istream>
#include <cstdio>

#include "cscanner.h"

#define YY_INPUT(buf, result, max_size) \
    do { \
        if(!cscanner_ptr->in) \
          result=YY_NULL; \
        else \
        { \
          cscanner_ptr->in.read(buf, max_size); \
          result = cscanner_ptr->in.gcount(); \
        } \
    } while(0)

#define token(t) (cscanner_ptr->set_token(yytext, ctokent::t), ctokent::t)
%}

%%

{IntegerLiteral}       return token(INT_LIT);
{FloatingPointLiteral} return token(FLOAT_LIT);
{CharacterLiteral}     return token(CHAR_LIT);
{StringLiteral}        return token(STRING_LIT);
{Separator}            return token(SEPARATOR);
{Operator}             return token(OPERATOR);
{Identifier}           return token(IDENTIFIER);
{PreprocessorDirective} return token(PREPROCESSOR_DIRECTIVE);
{TraditionalComment}   { for(const char *t = yytext; *t!=0; t++) // need to count newlines
                           if(*t=='\n') cscanner_ptr->line_number++;
                         if(cscanner_ptr->return_WS_and_comments) return token(C_COMMENT); }
{EndOfLineComment}     { if(cscanner_ptr->return_WS_and_comments) return token(CPP_COMMENT); }
{WhiteSpace}           if(cscanner_ptr->return_WS_and_comments) return token(WS);
{LineTerminator}       { cscanner_ptr->line_number++; if(cscanner_ptr->return_WS_and_comments) return token(WS); }
<<EOF>>                return token(END_OF_FILE);
.                      return token(UNKNOWN);

%%

void initialize_yyc_scanner()
{
  BEGIN(INITIAL);
}

int yywrap() { return 1; }
