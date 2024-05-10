%{

// This scanner is based on the IEC standard 61131-3 which, among other things,
// includes a BNF grammar for the Instruction List (IL) language. The
// Statement List language (STL) by Siemens complies with the standards 
// defined by the IEC, although some modifications were made for compatibility
// reasons. As a consequence, the general language structure specified by the 
// IEC is similar to the structure of STL, but there are differences between
// their syntax and some language features (In general, Siemens implements more
// language features in STL than described in the standard).

// Conversion from yytext to expressions.
#include "converters/convert_bool_literal.h"
#include "converters/convert_int_literal.h"
#include "converters/convert_dint_literal.h"
#include "converters/convert_real_literal.h"
#include "converters/convert_string_value.h"

// Disable warnings for generated file.
#include <util/pragma_wsign_compare.def> // IWYU pragma: keep
#include <util/pragma_wnull_conversion.def> // IWYU pragma: keep
#include <util/pragma_wdeprecated_register.def> // IWYU pragma: keep

#include <algorithm>

// Visual Studio
#if defined _MSC_VER
// Disable warning for signed/unsigned mismatch.
#pragma warning(disable:4365)
// Disable warning for macro re-definition: Flex conditionally defines 
// INT32_MAX et al. and thus they are set before library headers get to define
// them.
#pragma warning(disable:4005)
#endif

// Conditionally disable unistd header since it does not exist when building on
// Windows. 
#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

// Value inside of statement_list_parser.h.
#define PARSER (*yyextra)

// Sets the type of yystatement_listlval so that it can be used as the stack 
// index.
#define YYSTYPE unsigned

// For access to the stack and the parser itself.
#include "statement_list_parser.h"

 // To get the token types from Bison.
#include "statement_list_y.tab.h"

// Add an empty expression to the stack, set yystatement_listlval to the 
// position of that element and set the source location to the new expression.
#define loc() \
  { newstack(yystatement_listlval); \
    PARSER.set_source_location(parser_stack(yystatement_listlval)); }
%}
%option noyywrap
%option noinput
%option nounput
%option reentrant
%option extra-type="statement_list_parsert *"

%x GRAMMAR
%x TAG_NAME
%x MODULE_NAME
%x TAG_ATTRIBUTES
%x VERSION_ANNOTATION

%%

<INITIAL>.|\n   { BEGIN(GRAMMAR);
                  yyless(0); /* start again with this character */
                }
<GRAMMAR>{
  [\(:\.,;#]          { loc(); return yytext[0]; }
  [\t\r\n ]           ;
  :=                  { loc(); return STOK_ASSIGNMENT; }
  TAG                 { loc(); BEGIN(TAG_NAME); return STOK_TAG; }
  BEGIN               { loc(); return STOK_BEGIN; }
  VERSION             { loc(); BEGIN(VERSION_ANNOTATION); return STOK_VERSION; }
  FUNCTION_BLOCK      { loc(); BEGIN(MODULE_NAME); return STOK_FUNCTION_BLOCK; }
  END_FUNCTION_BLOCK  { loc(); return STOK_END_FUNCTION_BLOCK; }
  FUNCTION            { loc(); BEGIN(MODULE_NAME); return STOK_FUNCTION; }
  END_FUNCTION        { loc(); return STOK_END_FUNCTION; }
  VAR_INPUT           { loc(); return STOK_VAR_INPUT; }
  VAR_OUTPUT          { loc(); return STOK_VAR_OUTPUT; }
  VAR_IN_OUT          { loc(); return STOK_VAR_INOUT; }
  VAR                 { loc(); return STOK_VAR_STATIC; }
  VAR[ ]CONSTANT      { loc(); return STOK_VAR_CONSTANT; }
  VAR_TEMP            { loc(); return STOK_VAR_TEMP; }
  END_VAR             { loc(); return STOK_END_VAR; }
  NETWORK             { loc(); return STOK_NETWORK; }
  TITLE               { loc(); return STOK_TITLE; }
  Int                 { loc(); return STOK_INT; }
  DInt                { loc(); return STOK_DINT; }
  Bool                { loc(); return STOK_BOOL; }
  Real                { loc(); return STOK_REAL; }
  Void                { loc(); return STOK_VOID; }
  L                   { loc(); return STOK_LOAD; }
  T                   { loc(); return STOK_TRANSFER; }
  CALL                { loc(); BEGIN(MODULE_NAME); return STOK_CALL; }
  NOP                 { loc(); return STOK_NOP; }
  SET                 { loc(); return STOK_SET_RLO; }
  CLR                 { loc(); return STOK_CLR_RLO; }
  S                   { loc(); return STOK_SET; }
  R                   { loc(); return STOK_RESET; }
  NOT                 { loc(); return STOK_NOT; }
  A                   { loc(); return STOK_AND; }
  AN                  { loc(); return STOK_AND_NOT; }
  O                   { loc(); return STOK_OR; }
  ON                  { loc(); return STOK_OR_NOT; }
  X                   { loc(); return STOK_XOR; }
  XN                  { loc(); return STOK_XOR_NOT; }
  A\(                 { loc(); return STOK_AND_NESTED; }
  AN\(                { loc(); return STOK_AND_NOT_NESTED; }
  O\(                 { loc(); return STOK_OR_NESTED; }
  ON\(                { loc(); return STOK_OR_NOT_NESTED; }
  X\(                 { loc(); return STOK_XOR_NESTED; }
  XN\(                { loc(); return STOK_XOR_NOT_NESTED; }
  \)                  { loc(); return STOK_NESTING_CLOSED; }
  =                   { loc(); return STOK_ASSIGN; }
  \+                  { loc(); return STOK_CONST_ADD; }
  \+I                 { loc(); return STOK_ACCU_INT_ADD; }
  \-I                 { loc(); return STOK_ACCU_INT_SUB; }
  \*I                 { loc(); return STOK_ACCU_INT_MUL; }
  \/I                 { loc(); return STOK_ACCU_INT_DIV; }
  ==I                 { loc(); return STOK_ACCU_INT_EQ; }
  \<\>I               { loc(); return STOK_ACCU_INT_NEQ; }
  \>I                 { loc(); return STOK_ACCU_INT_GT; }
  \<I                 { loc(); return STOK_ACCU_INT_LT; }
  \>=I                { loc(); return STOK_ACCU_INT_GTE; }
  \<=I                { loc(); return STOK_ACCU_INT_LTE; }
  \+R                 { loc(); return STOK_ACCU_REAL_ADD; }
  \-R                 { loc(); return STOK_ACCU_REAL_SUB; }
  \*R                 { loc(); return STOK_ACCU_REAL_MUL; }
  \/R                 { loc(); return STOK_ACCU_REAL_DIV; }
  ==R                 { loc(); return STOK_ACCU_REAL_EQ; }
  \<\>R               { loc(); return STOK_ACCU_REAL_NEQ; }
  \>R                 { loc(); return STOK_ACCU_REAL_GT; }
  \<R                 { loc(); return STOK_ACCU_REAL_LT; }
  \>=R                { loc(); return STOK_ACCU_REAL_GTE; }
  \<=R                { loc(); return STOK_ACCU_REAL_LTE; }
  \+D                 { loc(); return STOK_ACCU_DINT_ADD; }
  \-D                 { loc(); return STOK_ACCU_DINT_SUB; }
  \*D                 { loc(); return STOK_ACCU_DINT_MUL; }
  \/D                 { loc(); return STOK_ACCU_DINT_DIV; }
  ==D                 { loc(); return STOK_ACCU_DINT_EQ; }
  \<\>D               { loc(); return STOK_ACCU_DINT_NEQ; }
  \>D                 { loc(); return STOK_ACCU_DINT_GT; }
  \<D                 { loc(); return STOK_ACCU_DINT_LT; }
  \>=D                { loc(); return STOK_ACCU_DINT_GTE; }
  \<=D                { loc(); return STOK_ACCU_DINT_LTE; }
  JU                  { loc(); return STOK_JUMP_UNCONDITIONAL; }
  JC                  { loc(); return STOK_JUMP_CONDITIONAL; }
  JCN                 { loc(); return STOK_JUMP_CONDITIONAL_NOT; }

  (10#)?[\+-]?[0-9]+ { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_int_dec_literal(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_INT_LITERAL; 
                      }
  INT#(10#)?[\+-]?[0-9]+ { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_int_dec_literal_value(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_INT_LITERAL; 
                      }
                      
  ((DINT#(10#)?)|(L#))[\+-]?[0-9]+ { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_dint_dec_literal_value(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_INT_LITERAL; 
                      }
                    
  16#[0-9A-Fa-f]+     { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_int_hex_literal(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_INT_LITERAL; 
                      }
  INT#16#[0-9A-Fa-f]+ { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_int_hex_literal_value(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_INT_LITERAL; 
                      }
                      
  DINT#16#[0-9A-Fa-f]+ { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_dint_hex_literal_value(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_INT_LITERAL; 
                      }
                    
  2#[0|1]+            { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_int_bit_literal(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_INT_LITERAL; 
                      }
                        
  INT#2#[0|1]+        {
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_int_bit_literal_value(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_INT_LITERAL; 
                      }
                      
  DINT#2#[0|1]+       {
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_dint_bit_literal_value(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_INT_LITERAL; 
                      }
                      
  ([Tt][Rr][Uu][Ee])|([Ff][Aa][Ll][Ss][Ee]) { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_bool_literal(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_BOOL_LITERAL; 
                      }

  (\+|-)?[0-9]+\.[0-9]+ {
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_real_literal(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_REAL_LITERAL; 
                      }

  (\"[^\"\r\t\n]+\")|([a-zA-Z][a-zA-Z0-9_]*) {
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_identifier(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_IDENTIFIER; 
                      }

  [a-zA-Z_][a-zA-Z0-9_]*: {
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_label(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_LABEL;
                      }
}

<TAG_NAME>{
  [\t\r\n ]           ;
  \"[^\"\r\t\n]+\"    {
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_identifier(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        BEGIN(TAG_ATTRIBUTES);
                        return STOK_IDENTIFIER; 
                      }
  END_TAG             { loc(); BEGIN(GRAMMAR); return STOK_END_TAG; }
}

<MODULE_NAME>{
  [\t\r\n ]           ;
  \"[^\"\r\t\n]+\"    {
                        newstack(yystatement_listlval);
                        std::string str{yytext};
                        str.erase(
                          std::remove(begin(str), end(str), '\"' ), 
                          end(str));
                        parser_stack(yystatement_listlval) = 
                          convert_identifier(str);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        BEGIN(GRAMMAR);
                        return STOK_IDENTIFIER; 
                      }
}

<TAG_ATTRIBUTES>{
  [\t\r," ]           ;
  ([t|T][R|r][u|U][e|E])|([f|F][a|A][l|L][s|S][e|E]) ;
  %[A-Za-z][0-9\.]+   ;
  Int                 { loc(); return STOK_INT; }
  DInt                { loc(); return STOK_DINT; }
  Bool                { loc(); return STOK_BOOL; }
  Real                { loc(); return STOK_REAL; }
  \n                  { BEGIN(TAG_NAME); } 
}

<VERSION_ANNOTATION>{
  [\t\r, ]            ;
  :                   { loc(); return yytext[0]; }
  [0-9][0-9]?[.][0-9][0-9]? {
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) =
                          convert_version(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return STOK_VERSION_VALUE;
                      }
  \n                  { BEGIN(GRAMMAR); }
}
%%
