%option nounput

%{

/*
 * This scanner is based on:
 *
 * cpp5.l, a C/C++ scanner written by James A. Roskind.
 * "Portions Copyright (c) 1989, 1990 James A. Roskind".
 * (http://www.idiom.com/free-compilers/,
 * ftp://ftp.infoseek.com/ftp/pub/c++grammar/,
 * ftp://ftp.sra.co.jp/.a/pub/cmd/c++grammar2.0.tar.gz)
 */

#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

#include <expr.h>
#include <arith_tools.h>
#include <config.h>

#include <ansi-c/c_types.h>
#include <ansi-c/preprocessor_line.h>

#include <ansi-c/literals/convert_float_literal.h>
#include <ansi-c/literals/convert_integer_literal.h>
#include <ansi-c/literals/convert_character_literal.h>
#include <ansi-c/literals/convert_string_literal.h>

#define PARSER ansi_c_parser
#define YYSTYPE unsigned
#undef  ECHO
#define ECHO

#include "ansi_c_parser.h"
#include "y.tab.h"

#define loc() \
  { newstack(yyansi_clval); PARSER.set_location(stack(yyansi_clval)); }

int make_identifier()
{
  loc();

  std::string base_name(yytext);
  std::string identifier(base_name);

  // figure out if this is a typedef or something else
  ansi_c_id_classt result=
    PARSER.lookup(identifier, PARSER.tag_following, false);

  PARSER.tag_following=false;

  stack(yyansi_clval).id(ID_symbol);
  stack(yyansi_clval).set(ID_C_base_name, base_name);
  stack(yyansi_clval).set(ID_identifier, identifier);
  stack(yyansi_clval).set(ID_C_id_class, result);

  if(result==ANSI_C_TYPEDEF)
    return TOK_TYPEDEFNAME;
  else
    return TOK_IDENTIFIER;
}

int MSC_Keyword(int token)
{
  if(PARSER.mode==ansi_c_parsert::MSC)
  {
    loc();
    PARSER.tag_following=false;
    return token;
  }
  else
    return make_identifier();
}

int cpp_keyword(int token)
{
  if(PARSER.cpp)
  {
    loc();
    return token;
  }
  else
    return make_identifier();
}

int MSC_cpp_keyword(int token)
{
  if(PARSER.cpp && PARSER.mode==ansi_c_parsert::MSC)
  {
    loc();
    return token;
  }
  else
    return make_identifier();
}

int cpp_operator(int token)
{
  if(PARSER.cpp)
  {
    loc();
    return token;
  }
  else
  {
    yyansi_cerror("C++ operator not allowed in C mode");
    return TOK_SCANNER_ERROR;
  }
}

/*** macros for easier rule definition **********************************/
%}

delimiter       [ \t\b\r]
newline         [\n\f\v]|"\\\n"
whitespace      {delimiter}+
ws              {delimiter}*
ucletter	[A-Z]
lcletter	[a-z]
letter		({ucletter}|{lcletter})
digit		[0-9]
bindigit	[01]
octdigit	[0-7]
hexdigit	[0-9a-fA-F]
identifier	(({letter}|"_"|"$")({letter}|{digit}|"_"|"$")*)
integer		{digit}+
binary		{bindigit}+
msiw_suffix     ("i8"|"i16"|"i32"|"i64"|"i128")
int_suffix      [uUlLiIjJ]*|{msiw_suffix}
decinteger	[1-9]{digit}*{int_suffix}
octinteger	"0"{octdigit}*{int_suffix}
hexinteger	"0"[xX]{hexdigit}+{int_suffix}
integer_s       {decinteger}|{octinteger}|{hexinteger}
octchar		"\\"{octdigit}{1,3}
hexchar		"\\x"{hexdigit}+
exponent	[eE][+-]?{integer}
fraction	{integer}
float1		{integer}"."{fraction}?({exponent})?
float2		"."{fraction}({exponent})?
float3		{integer}{exponent}
hexfloat1       "0"[xX]{hexdigit}+"."{hexdigit}+[pP][+-]?{integer}
hexfloat2       "0"[xX]{hexdigit}+"."[pP][+-]?{integer}
hexfloat3       "0"[xX]{hexdigit}+[pP][+-]?{integer}
float_suffix    [fFlLiIjJ]*
float		{float1}|{float2}|{float3}|{hexfloat1}|{hexfloat2}|{hexfloat3}
float_s         {float}{float_suffix}|{integer}[fF]
bitvector	{binary}[bB]
bitvector_u	{binary}([uU][bB]|[bB][uU])
cppstart	{ws}"#"{ws}
cpplineno	{cppstart}"line"*{ws}{integer}{ws}.*{newline}
cpppragma	{cppstart}"pragma"{ws}.*
cppdirective	{cppstart}.*

escape_sequence [\\][^\n]
c_char [^'\\\n]|{escape_sequence}
s_char [^"\\\n]|{escape_sequence}

%x GRAMMAR
%x COMMENT1
%x COMMENT2
%x ASM_BLOCK
%x MSC_ASM
%x MSC_DECLSPEC
%x MSC_PRAGMA
%x MSC_ANNOTATION
%x GCC_ATTRIBUTE1
%x GCC_ATTRIBUTE2
%x GCC_ATTRIBUTE3
%x GCC_ATTRIBUTE4
%x GCC_ATTRIBUTE5
%x GCC_ASM
%x GCC_ASM_VOLATILE
%x GCC_ASM_PAREN

%{
void ansi_c_scanner_init()
{
  YY_FLUSH_BUFFER;
  BEGIN(0);
}
%}

%%

<INITIAL>.|\n   { BEGIN(GRAMMAR);
		  yyless(0);		/* start again with this character */
		  //yy_current_buffer->yy_at_bol = 1; /* at beginning of line */
		  switch(PARSER.grammar)
		   {
                   case ansi_c_parsert::EXPRESSION: return TOK_PARSE_EXPRESSION;
                   case ansi_c_parsert::LANGUAGE: return TOK_PARSE_LANGUAGE;
		   default: assert(0);
		   }
		 }

<GRAMMAR>"/*"   { BEGIN(COMMENT1); } /* begin C comment state */

<COMMENT1>{
   "*/"	        { BEGIN(GRAMMAR); } /* end comment state, back GRAMMAR */
   "/*"		{ yyansi_cerror("Probably nested comments"); }
   <<EOF>>	{ yyansi_cerror("Unterminated comment"); return TOK_SCANNER_ERROR; }
   [^*/\n]*	{ /* ignore every char except '*' and NL (performance!) */ }
   .		{ } /* all single characters within comments are ignored */
   \n		{ }
	}

<GRAMMAR>"//"	{ BEGIN(COMMENT2); }	/* begin C++ comment state */

<COMMENT2>{
   \n		{ BEGIN(GRAMMAR); }	/* end comment state, back GRAMMAR */
   .*		{ } /* all characters within comments are ignored */
	}

<GRAMMAR>("L"|"u"|"U")?[']{c_char}+['] {
                  newstack(yyansi_clval);
                  stack(yyansi_clval)=convert_character_literal(yytext, true);
                  PARSER.set_location(stack(yyansi_clval));
                  return TOK_CHARACTER;
                }

<GRAMMAR>("L"|"u"|"U"|"u8")?["]{s_char}*["] {
                  newstack(yyansi_clval);
                  stack(yyansi_clval)=convert_string_literal(yytext);
                  PARSER.set_location(stack(yyansi_clval));
                  return TOK_STRING;
                }

<GRAMMAR>{newline}	{ } /* skipped */
<GRAMMAR>{whitespace}	{ } /* skipped */

<GRAMMAR>{cpplineno}	{
                  preprocessor_line(yytext, PARSER.line_no, PARSER.filename);
                  PARSER.line_no--;
		 }
<GRAMMAR>{cpppragma}	{
                  #if 0
		  TmpString.form(
			"'pragma' directive found:" GL_WARN_MSG_NEWLINE
			"%s" GL_WARN_MSG_NEWLINE
			"Directive ignored",
			&PRS_text[0]);
		  PRS_PrintWarning(GL_WARN_INFORMATIVE, TmpString.chars());
		  TmpString = "";
                  #endif
		 }
<GRAMMAR>{cppstart}"ident"{ws}.* { /* ignore */ }
<GRAMMAR>{cppstart}"define"{ws}.* { /* ignore */ }
<GRAMMAR>{cppstart}"undef"{ws}.* { /* ignore */ }
<GRAMMAR>{cppdirective}	{
		  yyansi_cerror("Preprocessor directive found");
		  return TOK_SCANNER_ERROR;
		 }

%{
/*** keywords ***/
%}

<GRAMMAR,GCC_ATTRIBUTE3>{
"auto"		{ loc(); return TOK_AUTO; }
"_Bool"		{ loc(); return TOK_BOOL; }
"break"		{ loc(); return TOK_BREAK; }
"case"		{ loc(); return TOK_CASE; }
"char"		{ loc(); return TOK_CHAR; }
"_Complex"	{ loc(); return TOK_COMPLEX; }
"const"		{ loc(); return TOK_CONST; }
"continue"	{ loc(); return TOK_CONTINUE; }
"default"	{ loc(); return TOK_DEFAULT; }
"do"		{ loc(); return TOK_DO; }
"double"	{ loc(); return TOK_DOUBLE; }
"else"		{ loc(); return TOK_ELSE; }
"enum"		{ loc(); PARSER.tag_following=true; return TOK_ENUM; }
"extern"	{ loc(); return TOK_EXTERN; }
"float"		{ loc(); return TOK_FLOAT; }
"for"		{ loc(); return TOK_FOR; }
"goto"		{ loc(); return TOK_GOTO; }
"if"		{ loc(); return TOK_IF; }
"inline"	{ loc(); return TOK_INLINE; }
"int"		{ loc(); return TOK_INT; }
"long"		{ loc(); return TOK_LONG; }
"register"	{ loc(); return TOK_REGISTER; }
"restrict"      { /* C99, ignore for now */ }
"return"	{ loc(); return TOK_RETURN; }
"short" 	{ loc(); return TOK_SHORT; }
"signed"	{ loc(); return TOK_SIGNED; }
"sizeof"	{ loc(); return TOK_SIZEOF; }
"static"	{ loc(); return TOK_STATIC; }
"struct"	{ loc(); PARSER.tag_following=true; return TOK_STRUCT; }
"switch"	{ loc(); return TOK_SWITCH; }
"typedef"	{ loc(); return TOK_TYPEDEF; }
"union"		{ loc(); PARSER.tag_following=true; return TOK_UNION; }
"unsigned"	{ loc(); return TOK_UNSIGNED; }
"void"		{ loc(); return TOK_VOID; }
"volatile"	{ loc(); return TOK_VOLATILE; }
"while"		{ loc(); return TOK_WHILE; }

"__float128"	{ if(PARSER.mode==ansi_c_parsert::GCC)
                    { loc(); return TOK_GCC_FLOAT128; }
                  else
                    return make_identifier();
                }

"__int128"	{ if(PARSER.mode==ansi_c_parsert::GCC)
                    { loc(); return TOK_GCC_INT128; }
                  else
                    return make_identifier();
                }

"_Decimal32"    { if(PARSER.mode==ansi_c_parsert::GCC)
                    { loc(); return TOK_GCC_DECIMAL32; }
                  else
                    return make_identifier();
                }

"_Decimal64"    { if(PARSER.mode==ansi_c_parsert::GCC)
                    { loc(); return TOK_GCC_DECIMAL64; }
                  else
                    return make_identifier();
                }

"_Decimal128"   { if(PARSER.mode==ansi_c_parsert::GCC)
                    { loc(); return TOK_GCC_DECIMAL128; }
                  else
                    return make_identifier();
                }

"__int8"        { return MSC_Keyword(TOK_INT8); }
"__int16"       { return MSC_Keyword(TOK_INT16); }
"__int32"       { return MSC_Keyword(TOK_INT32); }

"__int64"       { if(PARSER.mode==ansi_c_parsert::MSC ||
                     PARSER.mode==ansi_c_parsert::ARM ||
                     PARSER.mode==ansi_c_parsert::CW)
                    { loc(); return TOK_INT64; }
                  else
                    return make_identifier();
                }
"__ptr32"       { return MSC_Keyword(TOK_PTR32); }
"__ptr64"       { return MSC_Keyword(TOK_PTR64); }

%{
/*
"__stdcall"     { return MSC_Keyword(TOK_STDCALL); }
"__fastcall"    { return MSC_Keyword(TOK_FASTCALL); }
"__clrcall"     { return MSC_Keyword(TOK_CLRCALL); }
*/
%}

"__complex__" |
"__complex"     { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_COMPLEX; }
                  else
                    return make_identifier();
                }

"__real__" |
"__real"	{ if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_REAL; }
                  else
                    return make_identifier();
                }

"__imag__" |
"__imag"	{ if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_IMAG; }
                  else
                    return make_identifier();
                }

%{
/* note: "wchar_t" should be in the list above, but it is left out */
/*       because it is a 'typedef' in some standard header files   */
%}

"_var_arg_typeof" { if(PARSER.mode==ansi_c_parsert::CW)
                    { loc(); return TOK_CW_VAR_ARG_TYPEOF; }
                  else
                    return make_identifier();
                }

"__builtin_va_arg" { if(PARSER.mode==ansi_c_parsert::GCC ||
                        PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_BUILTIN_VA_ARG; }
                  else
                    return make_identifier();
                }

"__builtin_offsetof" |
"__offsetof__" |
"offsetof"      { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_OFFSETOF; }
                  else
                    return make_identifier();
                }

"__builtin_types_compatible_p" {
                  if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_GCC_BUILTIN_TYPES_COMPATIBLE_P; }
                  else
                    return make_identifier();
                }

"__alignof__" |
"__alignof"     { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_ALIGNOF; }
                  else
                    return make_identifier();
                }

"__ALIGNOF__"   { if(PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_ALIGNOF; }
                  else
                    return make_identifier();
                }

"__builtin_alignof" { if(PARSER.mode==ansi_c_parsert::GCC ||
                         PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_ALIGNOF; }
                  else
                    return make_identifier();
                }

"__asm"         { if(PARSER.mode==ansi_c_parsert::MSC)
                  {
                    loc();
                    BEGIN(MSC_ASM);
                    return TOK_MSC_ASM;
                  }
                  else
                    BEGIN(GCC_ASM);
                }

"asm"           { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::CW)
                    BEGIN(GCC_ASM);
                  else
                    return make_identifier();
                }

"__asm__"       { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::CW ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    BEGIN(GCC_ASM);
                  else
                    return make_identifier();
                }

%{
/* C++ Keywords and Operators */
%}

bool                { return cpp_keyword(TOK_BOOL); }
catch               { return cpp_keyword(TOK_CATCH); }
class               { return cpp_keyword(TOK_CLASS); }
constexpr           { return cpp_keyword(TOK_CONSTEXPR); }
delete              { return cpp_keyword(TOK_DELETE); }
decltype            { return cpp_keyword(TOK_DECLTYPE); }
explicit            { return cpp_keyword(TOK_EXPLICIT); }
friend              { return cpp_keyword(TOK_FRIEND); }
mutable             { return cpp_keyword(TOK_MUTABLE); }
namespace           { return cpp_keyword(TOK_NAMESPACE); }
new                 { return cpp_keyword(TOK_NEW); }
nullptr             { return cpp_keyword(TOK_NULLPTR); }
operator            { return cpp_keyword(TOK_OPERATOR); }
private             { return cpp_keyword(TOK_PRIVATE); }
protected           { return cpp_keyword(TOK_PROTECTED); }
public              { return cpp_keyword(TOK_PUBLIC); }
static_assert       { return cpp_keyword(TOK_STATIC_ASSERT); }
template            { return cpp_keyword(TOK_TEMPLATE); }
this                { return cpp_keyword(TOK_THIS); }
thread_local        { return cpp_keyword(TOK_THREAD_LOCAL); }
throw               { return cpp_keyword(TOK_THROW); }
typeid              { return cpp_keyword(TOK_TYPEID); }
typename            { return cpp_keyword(TOK_TYPENAME); }
using               { return cpp_keyword(TOK_USING); }
virtual             { return cpp_keyword(TOK_VIRTUAL); }
wchar_t	            { // CodeWarrior doesn't have wchar_t built in
                      if(PARSER.mode==ansi_c_parsert::CW)
                        return make_identifier();
                      else
                        return cpp_keyword(TOK_WCHAR_T);
                    }
".*"                { return cpp_operator(TOK_DOTPM); }
"->*"               { return cpp_operator(TOK_ARROWPM); }
"::"                { if(PARSER.cpp)
                        return cpp_operator(TOK_SCOPE);
                      else
                      {
                        yyless(1); // puts all but one : back into stream
                        loc();
                        PARSER.tag_following=false;
                        return ':';
                      }
                    }

%{
/* a huge batch of MS C++ extensions
   http://msdn.microsoft.com/en-us/library/ms177194(v=vs.80).aspx */
%}

"__has_assign"      { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_copy"        { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_finalizer"   { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_nothrow_assign" { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_nothrow_constructor" { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_nothrow_copy" { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_trivial_assign" { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_trivial_constructor" { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_trivial_copy" { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_trivial_destructor" { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_user_destructor" { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_virtual_destructor" { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_abstract"     { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_base_of"      { loc(); return MSC_cpp_keyword(TOK_MSC_BINARY_TYPE_PREDICATE); }
"__is_class"        { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_convertible_to" { loc(); return MSC_cpp_keyword(TOK_MSC_BINARY_TYPE_PREDICATE); }
"__is_delegate"     { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_empty"        { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_enum"         { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_interface_class" { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_pod"          { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_polymorphic"  { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_ref_array"    { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_ref_class"    { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_sealed"       { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_simple_value_class" { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_union"        { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_value_class"  { loc(); return MSC_cpp_keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }

"__if_exists"       { loc(); return MSC_cpp_keyword(TOK_MSC_IF_EXISTS); }
"__if_not_exists"   { loc(); return MSC_cpp_keyword(TOK_MSC_IF_NOT_EXISTS); }

"["{ws}"repeatable" |
"["{ws}"source_annotation_attribute" |
"["{ws}"returnvalue" |
"["{ws}"SA_Pre" |
"["{ws}"SA_Post" |
"["{ws}"SA_FormatString" |
"["{ws}"SA_Success" |
"["{ws}"uuid" |
"["{ws}"emitidl" |
"["{ws}"module" |
"["{ws}"export"  { if(PARSER.mode==ansi_c_parsert::MSC)
	             BEGIN(MSC_ANNOTATION);
                   else
	           {
	             yyless(1); // puts all but [ back into stream
	             loc();
	             PARSER.tag_following=false;
	             return yytext[0]; // returns the [
	           }
                 }

"__declspec" |
"_declspec"     { if(PARSER.mode==ansi_c_parsert::MSC ||
                     PARSER.mode==ansi_c_parsert::CW ||
                     PARSER.mode==ansi_c_parsert::ARM)
                  {
                    BEGIN(MSC_DECLSPEC);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__pragma"      { if(PARSER.mode==ansi_c_parsert::MSC)
                  {
                    BEGIN(MSC_PRAGMA);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__attribute__" |
"__attribute"   { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::CW ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    BEGIN(GCC_ATTRIBUTE1);
                  else
                    return make_identifier();
                }

"__aligned"     { /* ignore */ }
"__aligned__"   { /* ignore */ }

"__extension__" { /* ignore */ }

"__restrict"    { /* gcc, ignore */ }
"__restrict__"  { /* gcc, ignore */ }

"_cdecl"        { /* ignore */ }
"__cdecl"       { /* ignore */ }
"__cdecl__"     { /* ignore */ }
"_stdcall"      { /* ignore */ }
"__stdcall"     { /* ignore */ }
"_fastcall"     { /* ignore */ }
"__fastcall"    { /* ignore */ }
"__w64"         { /* ignore */ }

"__const"       { loc(); return TOK_CONST; }
"__const__"     { loc(); return TOK_CONST; }

"__signed"      { loc(); return TOK_SIGNED; }
"__signed__"    { loc(); return TOK_SIGNED; }

"__volatile"    { loc(); return TOK_VOLATILE; }
"__volatile__"  { loc(); return TOK_VOLATILE; }

"__pure"        { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__align"       { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    BEGIN(MSC_DECLSPEC);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__smc"         { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    BEGIN(MSC_DECLSPEC);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__INTADDR__"   { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__irq"         { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__packed"      { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__value_in_regs" { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__weak"        { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__writeonly"   { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__global_reg"  { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    BEGIN(MSC_DECLSPEC);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__svc"         { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    BEGIN(MSC_DECLSPEC);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__svc_indirect" { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    BEGIN(MSC_DECLSPEC);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__svc_indirect_r7" { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    BEGIN(MSC_DECLSPEC);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__softfp"      { /* an ARM extension */
                  if(PARSER.mode==ansi_c_parsert::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"typeof"        { if(PARSER.cpp ||
                     PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ICC ||
                     PARSER.mode==ansi_c_parsert::CW ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_TYPEOF; }
                  else
                    return make_identifier();
                }
"__typeof"      { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ICC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_TYPEOF; }
                  else
                    return make_identifier();
                }

"__typeof__"    { loc(); return TOK_TYPEOF; }

"__forceinline" { if(PARSER.mode==ansi_c_parsert::MSC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_INLINE; }
                  else
                    return make_identifier();
                }
"__inline"	{ loc(); return TOK_INLINE; }
"__inline__"	{ loc(); return TOK_INLINE; }

"__label__"     { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_GCC_LABEL; }
                  else
                    return make_identifier();
                }

"__try"         { if(PARSER.mode==ansi_c_parsert::MSC)
                    { loc(); return TOK_TRY; }
                  else
                    return make_identifier();
                }

"try"           { if(PARSER.cpp) // C++?
                    { loc(); return TOK_TRY; }
                  else if(PARSER.mode==ansi_c_parsert::MSC)
                    { loc(); return TOK_TRY; }                    
                  else
                    return make_identifier();
                }

"__finally" |
"finally"       { if(PARSER.mode==ansi_c_parsert::MSC)
                    { loc(); return TOK_MSC_FINALLY; }
                  else
                    return make_identifier();
                }

"__except" |
"except"        { if(PARSER.mode==ansi_c_parsert::MSC)
                    { loc(); return TOK_MSC_EXCEPT; }
                  else
                    return make_identifier();
                }

"__leave" |
"leave"         { if(PARSER.mode==ansi_c_parsert::MSC)
                    { loc(); return TOK_MSC_LEAVE; }
                  else
                    return make_identifier();
                }

"__CPROVER_atomic" { loc(); return TOK_CPROVER_ATOMIC; }
"__CPROVER_forall" { loc(); return TOK_FORALL; }
"__CPROVER_exists" { loc(); return TOK_EXISTS; }
"__CPROVER_array_of" { loc(); return TOK_ARRAY_OF; }
"__CPROVER_thread_local" { loc(); return TOK_THREAD_LOCAL; }
"__CPROVER_bitvector" { loc(); return TOK_CPROVER_BITVECTOR; }
"__CPROVER_bool" { loc(); return TOK_CPROVER_BOOL; }

"__thread"      { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_THREAD_LOCAL; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Alignas"      { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_ALIGNAS; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Alignof"      { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_ALIGNOF; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Atomic"       { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_ATOMIC; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Generic"      { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_GENERIC; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Imaginary"    { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_IMAGINARY; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Noreturn"     { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_NORETURN; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Static_assert" { if(PARSER.mode==ansi_c_parsert::GCC ||
                      PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_STATIC_ASSERT; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Thread_local" { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_THREAD_LOCAL; }
                  else
                    return make_identifier();
                }

}

  /* operators following */

<GRAMMAR,GCC_ATTRIBUTE3>{
"->"		{ loc(); return TOK_ARROW; }
"++"		{ loc(); return TOK_INCR; }
"--"		{ loc(); return TOK_DECR; }
"<<"		{ loc(); return TOK_SHIFTLEFT; }
">>"		{ loc(); return TOK_SHIFTRIGHT; }
"<="		{ loc(); return TOK_LE; }
">="		{ loc(); return TOK_GE; }
"=="		{ loc(); return TOK_EQ; }
"!="		{ loc(); return TOK_NE; }
"&&"		{ loc(); return TOK_ANDAND; }
"||"		{ loc(); return TOK_OROR; }
"..."		{ loc(); return TOK_ELLIPSIS; }

"*="		{ loc(); return TOK_MULTASSIGN; }
"/="		{ loc(); return TOK_DIVASSIGN; }
"%="		{ loc(); return TOK_MODASSIGN; }
"+="		{ loc(); return TOK_PLUSASSIGN; }
"-="		{ loc(); return TOK_MINUSASSIGN; }
"<<="		{ loc(); return TOK_SHLASSIGN; }
">>="		{ loc(); return TOK_SHRASSIGN; }
"&="		{ loc(); return TOK_ANDASSIGN; }
"^="		{ loc(); return TOK_XORASSIGN; }
"|="		{ loc(); return TOK_ORASSIGN; }
}

<GRAMMAR>{

{identifier}	{ return make_identifier(); }

{integer_s}     { newstack(yyansi_clval);
                  stack(yyansi_clval)=convert_integer_literal(yytext);
                  PARSER.set_location(stack(yyansi_clval));
                  return TOK_INTEGER;
                }

{float_s}	{ newstack(yyansi_clval); 
                  stack(yyansi_clval)=convert_float_literal(yytext);
                  PARSER.set_location(stack(yyansi_clval));
		  return TOK_FLOATING;
		}

"{"             { 
                  PARSER.tag_following=false;
                  if(PARSER.asm_block_following) { BEGIN(ASM_BLOCK); }
                  loc();
                  return yytext[0];
                }

";"             { PARSER.asm_block_following=false;
                  PARSER.tag_following=false;
                  loc();
                  return yytext[0];
                }

  /* This catches all one-character operators */
.		{ loc(); PARSER.tag_following=false; return yytext[0]; }
}

<MSC_ANNOTATION>"]" { BEGIN(GRAMMAR); }
<MSC_ANNOTATION>. { /* ignore */ }

<MSC_ASM>{ws}"{" { BEGIN(ASM_BLOCK); loc(); return '{'; }
<MSC_ASM>[^{^}^\n]* { loc();
                  stack(yyansi_clval).set(ID_value, yytext);
                  stack(yyansi_clval).id(ID_string_constant);
                  BEGIN(GRAMMAR);
                  return TOK_ASM_STRING;
                }

<ASM_BLOCK>[^}]* { loc();
                  stack(yyansi_clval).set(ID_value, yytext);
                  stack(yyansi_clval).id(ID_string_constant);
                  return TOK_ASM_STRING; }
<ASM_BLOCK>"}"  { PARSER.asm_block_following=false;
                  BEGIN(GRAMMAR); loc(); return '}'; }

<MSC_DECLSPEC>")"    { PARSER.parenthesis_counter--;
                        if(PARSER.parenthesis_counter==0)
                          BEGIN(GRAMMAR); }
<MSC_DECLSPEC>"("    { PARSER.parenthesis_counter++; }
<MSC_DECLSPEC>.      { /* Throw away */ }

<MSC_PRAGMA>")"    { PARSER.parenthesis_counter--;
                        if(PARSER.parenthesis_counter==0)
                          BEGIN(GRAMMAR); }
<MSC_PRAGMA>"("    { PARSER.parenthesis_counter++; }
<MSC_PRAGMA>.      { /* Throw away */ }

  /* The following ugly stuff avoids two-token lookahead in the parser;
     e.g., asm void f()  vs.  asm ("xyz") or asm { ... } */
<GCC_ASM>{
{ws}            { /* ignore */ }
{newline}       { /* ignore */ }
"{"             { yyless(0); BEGIN(GRAMMAR); loc(); PARSER.asm_block_following=true; return TOK_GCC_ASM_PAREN; }
"("             { yyless(0); BEGIN(GRAMMAR); loc(); return TOK_GCC_ASM_PAREN; }
"volatile"      { yyless(0); BEGIN(GRAMMAR); loc(); return TOK_GCC_ASM_PAREN; }
"__volatile"    { yyless(0); BEGIN(GRAMMAR); loc(); return TOK_GCC_ASM_PAREN; }
"__volatile__"  { yyless(0); BEGIN(GRAMMAR); loc(); return TOK_GCC_ASM_PAREN; }
"goto"          { yyless(0); BEGIN(GRAMMAR); loc(); return TOK_GCC_ASM_PAREN; }
.               { yyless(0); BEGIN(GRAMMAR); loc(); PARSER.asm_block_following=true; return TOK_GCC_ASM; }
}

<GCC_ATTRIBUTE1>{
"("{ws}"("      { BEGIN(GCC_ATTRIBUTE2); PARSER.parenthesis_counter=0; }
{ws}            { /* ignore */ }
{newline}       { /* ignore */ }
.               { BEGIN(GRAMMAR); loc(); return yytext[0]; }
}

<GCC_ATTRIBUTE2>{ // an attribute is following -- these may be keywords!

"aligned" |
"__aligned__"       { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_ALIGNED; }

"packed" |
"__packed__"        { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_PACKED; }

"transparent_union" |
"__transparent_union__" { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_TRANSPARENT_UNION; }

"vector_size" |
"__vector_size__"   { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_VECTOR_SIZE; }

"mode" |
"__mode__"          { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_MODE; }

{ws}                { /* ignore */ }
{newline}           { /* ignore */ }
{identifier}        { BEGIN(GCC_ATTRIBUTE4); }
")"                 { BEGIN(GCC_ATTRIBUTE5); }
.                   { /* ignore */ }
}

<GCC_ATTRIBUTE3>{ // an attribute we do process
"("             { PARSER.parenthesis_counter++; loc(); return '('; }
")"             { if(PARSER.parenthesis_counter==0)
                  {
                    BEGIN(GCC_ATTRIBUTE5);
                    loc();
                    return TOK_GCC_ATTRIBUTE_END;
                  }
                  else
                  {
                    PARSER.parenthesis_counter--;
                    loc();
                    return ')';
                  }
                }
","             { if(PARSER.parenthesis_counter==0)
                  {
                    BEGIN(GCC_ATTRIBUTE2);
                    loc();
                    return TOK_GCC_ATTRIBUTE_END;
                  }
                  else
                  {
                    loc();
                    return ',';
                  }
                }
{integer_s}     { newstack(yyansi_clval);
                  stack(yyansi_clval)=convert_integer_literal(yytext);
                  PARSER.set_location(stack(yyansi_clval));
                  return TOK_INTEGER;
                }
{ws}            { /* ignore */ }
{newline}       { /* ignore */ }
{identifier}	{ return make_identifier(); }
.               { loc(); return yytext[0]; }
}

<GCC_ATTRIBUTE4>{ // an attribute we just ignore
"("             { PARSER.parenthesis_counter++; }
")"             { if(PARSER.parenthesis_counter==0)
                    BEGIN(GCC_ATTRIBUTE5);
                  else
                    PARSER.parenthesis_counter--;
                }
","             { if(PARSER.parenthesis_counter==0)
                    BEGIN(GCC_ATTRIBUTE2); }
.               { /* Throw away */ }
}

<GCC_ATTRIBUTE5>{ // end bit: the closing parenthesis
")"             { BEGIN(GRAMMAR); }
{ws}            { /* Throw away */ }
{newline}       { /* Throw away */ }
.               { BEGIN(GRAMMAR); loc(); return yytext[0]; }
}

<<EOF>>		{ yyterminate(); /* done! */ }

%%

int yywrap() { return 1; }
