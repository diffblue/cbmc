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
#include <util/pragma_wsign_compare.def>
#include <util/pragma_wnull_conversion.def>
#include <util/pragma_wdeprecated_register.def>

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
#define PARSER statement_list_parser

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
  
#ifdef STATEMENT_LIST_DEBUG
extern int yystatement_listdebug;
#endif
void statement_list_scanner_init()
{
#ifdef STATEMENT_LIST_DEBUG
  yystatement_listdebug=1;
#endif
  YY_FLUSH_BUFFER;
  BEGIN(0);
}
%}
%option noyywrap
%option noinput
%option nounput

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
  :=                  { loc(); return TOK_ASSIGNMENT; }
  TAG                 { loc(); BEGIN(TAG_NAME); return TOK_TAG; }
  BEGIN               { loc(); return TOK_BEGIN; }
  VERSION             { loc(); BEGIN(VERSION_ANNOTATION); return TOK_VERSION; }
  FUNCTION_BLOCK      { loc(); BEGIN(MODULE_NAME); return TOK_FUNCTION_BLOCK; }
  END_FUNCTION_BLOCK  { loc(); return TOK_END_FUNCTION_BLOCK; }
  FUNCTION            { loc(); BEGIN(MODULE_NAME); return TOK_FUNCTION; }
  END_FUNCTION        { loc(); return TOK_END_FUNCTION; }
  VAR_INPUT           { loc(); return TOK_VAR_INPUT; }
  VAR_OUTPUT          { loc(); return TOK_VAR_OUTPUT; }
  VAR_IN_OUT          { loc(); return TOK_VAR_INOUT; }
  VAR                 { loc(); return TOK_VAR_STATIC; }
  VAR[ ]CONSTANT      { loc(); return TOK_VAR_CONSTANT; }
  VAR_TEMP            { loc(); return TOK_VAR_TEMP; }
  END_VAR             { loc(); return TOK_END_VAR; }
  NETWORK             { loc(); return TOK_NETWORK; }
  TITLE               { loc(); return TOK_TITLE; }
  Int                 { loc(); return TOK_INT; }
  DInt                { loc(); return TOK_DINT; }
  Bool                { loc(); return TOK_BOOL; }
  Real                { loc(); return TOK_REAL; }
  Void                { loc(); return TOK_VOID; }
  L                   { loc(); return TOK_LOAD; }
  T                   { loc(); return TOK_TRANSFER; }
  CALL                { loc(); BEGIN(MODULE_NAME); return TOK_CALL; }
  NOP                 { loc(); return TOK_NOP; }
  SET                 { loc(); return TOK_SET_RLO; }
  CLR                 { loc(); return TOK_CLR_RLO; }
  S                   { loc(); return TOK_SET; }
  R                   { loc(); return TOK_RESET; }
  NOT                 { loc(); return TOK_NOT; }
  A                   { loc(); return TOK_AND; }
  AN                  { loc(); return TOK_AND_NOT; }
  O                   { loc(); return TOK_OR; }
  ON                  { loc(); return TOK_OR_NOT; }
  X                   { loc(); return TOK_XOR; }
  XN                  { loc(); return TOK_XOR_NOT; }
  A\(                 { loc(); return TOK_AND_NESTED; }
  AN\(                { loc(); return TOK_AND_NOT_NESTED; }
  O\(                 { loc(); return TOK_OR_NESTED; }
  ON\(                { loc(); return TOK_OR_NOT_NESTED; }
  X\(                 { loc(); return TOK_XOR_NESTED; }
  XN\(                { loc(); return TOK_XOR_NOT_NESTED; }
  \)                  { loc(); return TOK_NESTING_CLOSED; }
  =                   { loc(); return TOK_ASSIGN; }
  \+                  { loc(); return TOK_CONST_ADD; }
  \+I                 { loc(); return TOK_ACCU_INT_ADD; }
  \-I                 { loc(); return TOK_ACCU_INT_SUB; }
  \*I                 { loc(); return TOK_ACCU_INT_MUL; }
  \/I                 { loc(); return TOK_ACCU_INT_DIV; }
  ==I                 { loc(); return TOK_ACCU_INT_EQ; }
  \<\>I               { loc(); return TOK_ACCU_INT_NEQ; }
  \>I                 { loc(); return TOK_ACCU_INT_GT; }
  \<I                 { loc(); return TOK_ACCU_INT_LT; }
  \>=I                { loc(); return TOK_ACCU_INT_GTE; }
  \<=I                { loc(); return TOK_ACCU_INT_LTE; }
  \+R                 { loc(); return TOK_ACCU_REAL_ADD; }
  \-R                 { loc(); return TOK_ACCU_REAL_SUB; }
  \*R                 { loc(); return TOK_ACCU_REAL_MUL; }
  \/R                 { loc(); return TOK_ACCU_REAL_DIV; }
  ==R                 { loc(); return TOK_ACCU_REAL_EQ; }
  \<\>R               { loc(); return TOK_ACCU_REAL_NEQ; }
  \>R                 { loc(); return TOK_ACCU_REAL_GT; }
  \<R                 { loc(); return TOK_ACCU_REAL_LT; }
  \>=R                { loc(); return TOK_ACCU_REAL_GTE; }
  \<=R                { loc(); return TOK_ACCU_REAL_LTE; }
  \+D                 { loc(); return TOK_ACCU_DINT_ADD; }
  \-D                 { loc(); return TOK_ACCU_DINT_SUB; }
  \*D                 { loc(); return TOK_ACCU_DINT_MUL; }
  \/D                 { loc(); return TOK_ACCU_DINT_DIV; }
  ==D                 { loc(); return TOK_ACCU_DINT_EQ; }
  \<\>D               { loc(); return TOK_ACCU_DINT_NEQ; }
  \>D                 { loc(); return TOK_ACCU_DINT_GT; }
  \<D                 { loc(); return TOK_ACCU_DINT_LT; }
  \>=D                { loc(); return TOK_ACCU_DINT_GTE; }
  \<=D                { loc(); return TOK_ACCU_DINT_LTE; }

  (10#)?[\+-]?[0-9]+ { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_int_dec_literal(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return TOK_INT_LITERAL; 
                      }
  INT#(10#)?[\+-]?[0-9]+ { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_int_dec_literal_value(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return TOK_INT_LITERAL; 
                      }
                      
  ((DINT#(10#)?)|(L#))[\+-]?[0-9]+ { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_dint_dec_literal_value(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return TOK_INT_LITERAL; 
                      }
                    
  16#[0-9A-Fa-f]+     { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_int_hex_literal(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return TOK_INT_LITERAL; 
                      }
  INT#16#[0-9A-Fa-f]+ { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_int_hex_literal_value(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return TOK_INT_LITERAL; 
                      }
                      
  DINT#16#[0-9A-Fa-f]+ { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_dint_hex_literal_value(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return TOK_INT_LITERAL; 
                      }
                    
  2#[0|1]+            { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_int_bit_literal(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return TOK_INT_LITERAL; 
                      }
                        
  INT#2#[0|1]+        {
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_int_bit_literal_value(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return TOK_INT_LITERAL; 
                      }
                      
  DINT#2#[0|1]+       {
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_dint_bit_literal_value(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return TOK_INT_LITERAL; 
                      }
                      
  ([Tt][Rr][Uu][Ee])|([Ff][Aa][Ll][Ss][Ee]) { 
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_bool_literal(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return TOK_BOOL_LITERAL; 
                      }

  (\+|-)?[0-9]+\.[0-9]+ {
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_real_literal(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return TOK_REAL_LITERAL; 
                      }

  (\"[^\"\r\t\n]+\")|([a-zA-Z][a-zA-Z0-9_]*) {
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_identifier(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return TOK_IDENTIFIER; 
                      }

  [a-zA-Z_\.][a-zA-Z0-9_\.]*: {
                        newstack(yystatement_listlval);
                        parser_stack(yystatement_listlval) = 
                          convert_label(yytext);
                        PARSER.set_source_location(
                          parser_stack(yystatement_listlval));
                        return TOK_LABEL;
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
                        return TOK_IDENTIFIER; 
                      }
  END_TAG             { loc(); BEGIN(GRAMMAR); return TOK_END_TAG; }
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
                        return TOK_IDENTIFIER; 
                      }
}

<TAG_ATTRIBUTES>{
  [\t\r," ]           ;
  ([t|T][R|r][u|U][e|E])|([f|F][a|A][l|L][s|S][e|E]) ;
  %[A-Za-z][0-9\.]+   ;
  Int                 { loc(); return TOK_INT; }
  DInt                { loc(); return TOK_DINT; }
  Bool                { loc(); return TOK_BOOL; }
  Real                { loc(); return TOK_REAL; }
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
                        return TOK_VERSION_VALUE;
                      }
  \n                  { BEGIN(GRAMMAR); }
}
%%
