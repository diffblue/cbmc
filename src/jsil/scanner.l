%option nounput
%option noinput
%option nounistd
%option never-interactive
%option stack

%{

#if defined _MSC_VER
// signed/unsigned mismatch
#pragma warning(disable:4365)
// macro re-definition: flex conditonally defines INT32_MAX et al. and thus
// they are set before library headers get to define them
#pragma warning(disable:4005)
#endif

#include <util/expr.h>

#include <ansi-c/literals/convert_float_literal.h>
#include <ansi-c/literals/convert_string_literal.h>

#define PARSER jsil_parser
#define YYSTYPE unsigned

#include "jsil_parser.h"
#include "jsil_y.tab.h"
// extern int yyjsildebug;

#define loc() \
  { newstack(yyjsillval); PARSER.set_source_location(parser_stack(yyjsillval)); }

static int make_identifier()
{
  loc();

  // this hashes the identifier
  irep_idt base_name=yytext;
  
  parser_stack(yyjsillval).id(ID_symbol);
  parser_stack(yyjsillval).set(ID_C_base_name, base_name);
  parser_stack(yyjsillval).set(ID_identifier, base_name);
  return TOK_IDENTIFIER;
}

#include <util/pragma_wsign_compare.def>
#include <util/pragma_wnull_conversion.def>
#include <util/pragma_wdeprecated_register.def>

%}

delimiter       [ \t\b\r]
newline         [\n\f\v]|"\\\n"
whitespace      {delimiter}+
ucletter  [A-Z]
lcletter  [a-z]
letter    ({ucletter}|{lcletter})
digit    [0-9]
identifier  (({letter}|"_")({letter}|{digit}|"_"|".")*)
integer    {digit}+
exponent  [eE][+-]?{integer}
fraction  {integer}
float1    {integer}"."{fraction}?({exponent})?
float2    "."{fraction}({exponent})?
float3    {integer}{exponent}
float    {float1}|{float2}|{float3}
escape_sequence [\\][^\n]
s_char [^"\\\n]|{escape_sequence}
string_lit      ["]{s_char}*["]

%x GRAMMAR
%x COMMENT
%x STRING_LITERAL
%x STRING_LITERAL_COMMENT
%x STATEMENTS

%{
void jsil_scanner_init()
{
  // yyjsildebug=1;
  YY_FLUSH_BUFFER;
  BEGIN(0);
}
%}
 /* %option debug */

%%

<INITIAL>.|\n   { 
                  BEGIN(GRAMMAR);
                  yyless(0);    /* start again with this character */
                }

<GRAMMAR,STATEMENTS>{
  "/*"          {
                  yy_push_state(COMMENT); /* begin comment state */
                  // make the compiler happy
                  (void)yy_top_state();
                }
}

<COMMENT>{
  "*/"          { yy_pop_state(); } /* end comment state, back to GRAMMAR */
  "/*"          { yyjsilerror("Probably nested comments"); }
  <<EOF>>       { yyjsilerror("Unterminated comment"); return TOK_SCANNER_ERROR; }
  [^*/\n]*      { } /* ignore every char except '*' and NL (performance!) */
  .             { } /* all single characters within comments are ignored */
  \n            { }
}

<STRING_LITERAL_COMMENT>{
  "*/"          { yy_pop_state(); } /* end comment state, back to STRING_LITERAL */
  "/*"          { yyjsilerror("Probably nested comments"); }
  <<EOF>>       { yyjsilerror("Unterminated comment"); return TOK_SCANNER_ERROR; }
  [^*/\n]*      { } /* ignore every char except '*' and NL (performance!) */
  .             { } /* all single characters within comments are ignored */
  \n            { }
}

<STATEMENTS>{
  {string_lit}  {
                  PARSER.string_literal.clear();
                  PARSER.string_literal.append(yytext);
                  newstack(yyjsillval);
                  PARSER.set_source_location(parser_stack(yyjsillval));
                  // String literals can be continued
                  yy_push_state(STRING_LITERAL);
                }
}

<STRING_LITERAL>{
  {string_lit}  { PARSER.string_literal.append(yytext); }
  {whitespace}  { } /* ignore */
  "/*"          { yy_push_state(STRING_LITERAL_COMMENT); } /* C comment, ignore */
  {newline}|.   { // anything else: back to normal
                  source_locationt l=parser_stack(yyjsillval).source_location();
                  parser_stack(yyjsillval)=convert_string_literal(PARSER.string_literal);
                  parser_stack(yyjsillval).add_source_location().swap(l);
                  yy_pop_state(); // back to normal
                  yyless(0); // put back
                  return TOK_STRING;
                }
}

<GRAMMAR,STATEMENTS>{
  "#global_is_nan" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#global_is_finite" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#boolean_call" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#boolean_construct" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#boolean_prototype_to_string" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; } 
  "#boolean_prototype_value_of" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#object_call" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#object_construct" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#object_prototype_to_string" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#object_prototype_value_of" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#object_prototype_is_prototype_of" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#object_get_prototype_of" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#number_call" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#number_construct" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#number_prototype_to_string" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#number_prototype_value_of" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#string_call" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#string_construct" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#string_prototype_to_string" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#string_prototype_value_of" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#error_call_construct" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#terror_call_construct" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#rerror_call_construct" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#serror_call_construct" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#evalerror_call_construct" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#rangeerror_call_construct" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#urierror_call_construct" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#function_call" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#function_construct" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#function_protottype_call" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#array_call" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }
  "#array_construct" { make_identifier(); return TOK_BUILTIN_IDENTIFIER; }

  "#[[GetOwnPropertyDefault]]" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#[[GetOwnPropertyString]]" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#GetValue"   { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#PutValue"   { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#[[Get]]"    { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#[[GetDefault]]" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#[[GetFunction]]" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#[[Put]]"    { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#[[HasProperty]]" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#[[DefaultValue]]" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#[[DefineOwnPropery]]" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#[[DefineOwnProperyDefault]]" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#[[DefineOwnProperyArray]]" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#ToPrimitive" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#ToBoolean"  { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#ToNumber"   { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#ToNumberPrim" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#ToUint32"   { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#ToString"   { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#ToStringPrim" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#ToObject"   { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#CheckObjectCoercible" { make_identifier(); return TOK_SPEC_IDENTIFIER; } 
  "#IsCallable" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#AbstractRelation" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#StrictEquality" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
  "#StrictEqualitySameType" { make_identifier(); return TOK_SPEC_IDENTIFIER; }
}

<GRAMMAR>{
  {newline}     { } /* skipped */
  {whitespace}  { } /* skipped */

  /*** keywords ***/

  "procedure"   { loc(); return TOK_PROCEDURE; }
  "returns"     { loc(); return TOK_RETURNS; }
  "to"          { loc(); return TOK_TO; }
  "throws"      { loc(); return TOK_THROWS; }

  /*** scanner parsed tokens (these have a value!) ***/

  {identifier}  { return make_identifier(); }

  "{"           { loc(); BEGIN(STATEMENTS); return '{'; }
  /* This catches all one-character operators */
  .             { loc(); return yytext[0]; }
}

<STATEMENTS>{
  {newline}     { loc(); return TOK_NEWLINE; }
  {whitespace}  { } /* skipped */

  "eval"        { loc(); return TOK_EVAL; }
  "label"       { loc(); return TOK_LABEL; }
  "goto"        { loc(); return TOK_GOTO; }
  "skip"        { loc(); return TOK_SKIP; }
  "with"        { loc(); return TOK_WITH; }
  "new"         { loc(); return TOK_NEW; }
  "hasField"    { loc(); return TOK_HAS_FIELD; }
  "delete"      { loc(); return TOK_DELETE; }
  "protoField"  { loc(); return TOK_PROTO_FIELD; }
  "protoObj"    { loc(); return TOK_PROTO_OBJ; }
  "ref"         { loc(); return TOK_REF; }
  "field"       { loc(); return TOK_FIELD; }
  "base"        { loc(); return TOK_BASE; }
  "typeOf"      { loc(); return TOK_TYPEOF; }
  "null"        { loc(); return TOK_NULL; }
  "#undefined"  { loc(); return TOK_UNDEFINED; }
  "#empty"      { loc(); return TOK_EMPTY; }
  "true"        { loc(); return TOK_TRUE; }
  "false"       { loc(); return TOK_FALSE; }
  "#proto"      { loc(); return TOK_PROTO; }
  "#fid"        { loc(); return TOK_FID; }
  "#scope"      { loc(); return TOK_SCOPE; }
  "#constructid" { loc(); return TOK_CONSTRUCTID; }
  "#primvalue"  { loc(); return TOK_PRIMVALUE; }
  "#targetfunction" { loc(); return TOK_TARGETFUNCTION; }
  "#class"      { loc(); return TOK_CLASS; }
  "num_to_string" { loc(); return TOK_NUM_TO_STRING; }
  "string_to_num" { loc(); return TOK_STRING_TO_NUM; }
  "num_to_int32" { loc(); return TOK_NUM_TO_INT32; }
  "num_to_uint32" { loc(); return TOK_NUM_TO_UINT32; }
  "#MemberReference" { loc(); return TOK_MEMBER_REFERENCE; }
  "#VariableReference" { loc(); return TOK_VARIABLE_REFERENCE; }

  /*** type classes ***/

  "#Null"       { loc(); return TOK_T_NULL; }
  "#Undefined"  { loc(); return TOK_T_UNDEFINED; }
  "#Boolean"    { loc(); return TOK_T_BOOLEAN; }
  "#String"     { loc(); return TOK_T_STRING; }
  "#Number"     { loc(); return TOK_T_NUMBER; }
  "#BuiltinObject" { loc(); return TOK_T_BUILTIN_OBJECT; }
  "#UserObject" { loc(); return TOK_T_USER_OBJECT; }
  "#Object"     { loc(); return TOK_T_OBJECT; }
  "#Reference"  { loc(); return TOK_T_REFERENCE; }

  /*** multi-character operators ***/

  ":="          { loc(); return TOK_DEFEQ; }
  "<="          { loc(); return TOK_LEQ; }
  "and"         { loc(); return TOK_AND; }
  "or"          { loc(); return TOK_OR; }
  "<:"          { loc(); return TOK_SUBTYPE_OF; }
  "<<"          { loc(); return TOK_LEFT_SHIFT; }
  ">>"          { loc(); return TOK_SIGNED_RIGHT_SHIFT; }
  ">>>"         { loc(); return TOK_UNSIGNED_RIGHT_SHIFT; }
  "not"         { loc(); return TOK_NOT; }

  /*** scanner parsed tokens (these have a value!) ***/

  {identifier}  { return make_identifier(); }

  {float}|{integer}  {
                       newstack(yyjsillval); 
                       parser_stack(yyjsillval)=convert_float_literal(yytext);
                       PARSER.set_source_location(parser_stack(yyjsillval));
                       return TOK_FLOATING;
                     }

  "#lg"         { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lg_isNan"   { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lg_isFinite" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lop"        { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lop_toString" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lop_valueOf" { make_identifier(); return TOK_BUILTIN_LOC; } 
  "#lop_isPrototypeOf" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lfunction"  { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lfp"        { make_identifier(); return TOK_BUILTIN_LOC; }
  "#leval"      { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lerror"     { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lep"        { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lrerror"    { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lrep"       { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lterror"    { make_identifier(); return TOK_BUILTIN_LOC; }
  "#ltep"       { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lserror"    { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lsep"       { make_identifier(); return TOK_BUILTIN_LOC; }
  "#levalerror" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#levalerrorp" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lrangeerror" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lrangeerrorp" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lurierror"  { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lurierrorp" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lobject"    { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lobject_get_prototype_of" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lboolean"   { make_identifier(); return TOK_BUILTIN_LOC; } 
  "#lbp"        { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lbp_toString" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lbp_valueOf" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lnumber"    { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lnp"        { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lnp_toString" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lnp_valueOf" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lmath"      { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lstring"    { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lsp"        { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lsp_toString" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lsp_valueOf" { make_identifier(); return TOK_BUILTIN_LOC; }
  "#larray"     { make_identifier(); return TOK_BUILTIN_LOC; }
  "#lap"        { make_identifier(); return TOK_BUILTIN_LOC; }
  "#ljson"      { make_identifier(); return TOK_BUILTIN_LOC; }

  "}"           { loc(); BEGIN(GRAMMAR); return '}'; }
  /* This catches all one-character operators */
  .             { loc(); return yytext[0]; }
}

<<EOF>>    { yyterminate(); /* done! */ }

%%

int yywrap() { return 1; }

