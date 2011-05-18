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

  ansi_c_id_classt result=
    PARSER.lookup(identifier, PARSER.tag_following);
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
identifier	(({letter}|"_")({letter}|{digit}|"_"|"$")*)
integer		{digit}+
binary		{bindigit}+
iw_suffix       ("i8"|"i16"|"i32"|"i64"|"i128")
decinteger	[1-9]{digit}*
decinteger_w    {decinteger}{iw_suffix}
octinteger	"0"{octdigit}*
octinteger_w    {octinteger}{iw_suffix}
hexinteger	"0"[xX]{hexdigit}+
hexinteger_w    {hexinteger}{iw_suffix}
decinteger_u	{decinteger}[uU]
decinteger_uw   {decinteger_u}{iw_suffix}
octinteger_u	{octinteger}[uU]
octinteger_uw   {octinteger_u}{iw_suffix}
hexinteger_u	{hexinteger}[uU]
hexinteger_uw   {hexinteger_u}{iw_suffix}
decinteger_l	{decinteger}[lL]
octinteger_l	{octinteger}[lL]
hexinteger_l	{hexinteger}[lL]
decinteger_ul	{decinteger}([uU][lL]|[lL][uU])
octinteger_ul	{octinteger}([uU][lL]|[lL][uU])
hexinteger_ul	{hexinteger}([uU][lL]|[lL][uU])
decinteger_ll	{decinteger}[lL][lL]
octinteger_ll	{octinteger}[lL][lL]
hexinteger_ll	{hexinteger}[lL][lL]
decinteger_ull	{decinteger}([uU][lL][lL]|[lL][lL][uU])
octinteger_ull	{octinteger}([uU][lL][lL]|[lL][lL][uU])
hexinteger_ull	{hexinteger}([uU][lL][lL]|[lL][lL][uU])
octchar		"\\"{octdigit}{1,3}
hexchar		"\\x"{hexdigit}+
exponent	[eE][+-]?{integer}
fraction	{integer}
float1		{integer}"."{fraction}?({exponent})?
float2		"."{fraction}({exponent})?
float3		{integer}{exponent}
float		{float1}|{float2}|{float3}
float_f		{float}[fF]|{integer}[fF]
float_l		{float}[lL]
bitvector	{binary}[bB]
bitvector_u	{binary}([uU][bB]|[bB][uU])
cppstart	{ws}"#"{ws}
cpplineno	{cppstart}"line"*{ws}{integer}{ws}.*{newline}
cpppragma	{cppstart}"pragma"{ws}.*
cppdirective	{cppstart}.*

simple_escape [abfnrtve'"?\\]
octal_escape  [0-7]{1,3}
hex_escape "x"[0-9a-fA-F]+

escape_sequence [\\]({simple_escape}|{octal_escape}|{hex_escape})
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
%x GCC_ASM_BLOCK1
%x GCC_ASM_BLOCK2
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

<GRAMMAR>"L"?[']{c_char}+['] {
                  newstack(yyansi_clval);
                  stack(yyansi_clval)=convert_character_literal(yytext, true);
                  PARSER.set_location(stack(yyansi_clval));
                  return TOK_CHARACTER;
                }

<GRAMMAR>"L"?["]{s_char}*["] {
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
<GRAMMAR>{cppdirective}	{
		  yyansi_cerror("Preprocessor directive found");
		  return TOK_SCANNER_ERROR;
		 }

%{
/*** keywords ***/
%}

<GRAMMAR>{
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
"restrict"      { /* ignore */ }
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

"__int8"        { if(PARSER.mode==ansi_c_parsert::MSC)
                    { loc(); return TOK_INT8; }
                  else
                    return make_identifier();
                }
"__int16"       { if(PARSER.mode==ansi_c_parsert::MSC)
                    { loc(); return TOK_INT16; }
                  else
                    return make_identifier();
                }
"__int32"       { if(PARSER.mode==ansi_c_parsert::MSC)
                    { loc(); return TOK_INT32; }
                  else
                    return make_identifier();
                }
"__int64"       { if(PARSER.mode==ansi_c_parsert::MSC ||
                     PARSER.mode==ansi_c_parsert::ARM ||
                     PARSER.mode==ansi_c_parsert::CW)
                    { loc(); return TOK_INT64; }
                  else
                    return make_identifier();
                }
"__ptr32"       { if(PARSER.mode==ansi_c_parsert::MSC)
                    { loc(); return TOK_PTR32; }
                  else
                    return make_identifier();
                }
"__ptr64"       { if(PARSER.mode==ansi_c_parsert::MSC)
                    { loc(); return TOK_PTR64; }
                  else
                    return make_identifier();
                }

"__complex__"	{ if(PARSER.mode==ansi_c_parsert::GCC ||
                        PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_COMPLEX; }
                  else
                    return make_identifier();
                }

"__real__"	{ if(PARSER.mode==ansi_c_parsert::GCC ||
                        PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_REAL; }
                  else
                    return make_identifier();
                }

"__imag__"	{ if(PARSER.mode==ansi_c_parsert::GCC ||
                        PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_IMAG; }
                  else
                    return make_identifier();
                }

%{
/* note: "wchar_t" should be in the list above, but it is left out */
/*       because it is a 'typedef' in some standard header files   */
%}

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

"__alignof__"   { if(PARSER.mode==ansi_c_parsert::GCC ||
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

"[repeatable"   { BEGIN(MSC_ANNOTATION); }
"[source_annotation_attribute" { BEGIN(MSC_ANNOTATION); }
"[returnvalue"  { BEGIN(MSC_ANNOTATION); }
"[SA_Pre"       { BEGIN(MSC_ANNOTATION); }
"[SA_Post"      { BEGIN(MSC_ANNOTATION); }
"[SA_FormatString" { BEGIN(MSC_ANNOTATION); }
"[SA_Success"   { BEGIN(MSC_ANNOTATION); }

"__declspec"    { if(PARSER.mode==ansi_c_parsert::MSC ||
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

"__restrict"    { /* ignore */ }

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

"typeof"        { if(PARSER.mode==ansi_c_parsert::GCC ||
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

"__try" |
"try"           { if(PARSER.mode==ansi_c_parsert::MSC)
                    { loc(); return TOK_MSC_TRY; }
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

"__CPROVER_forall" { loc(); return TOK_FORALL; }
"__CPROVER_exists" { loc(); return TOK_EXISTS; }
"__CPROVER_array_of" { loc(); return TOK_ARRAY_OF; }
"__CPROVER_thread_local" { loc(); return TOK_THREAD_LOCAL; }
"__CPROVER_bitvector" { loc(); return TOK_CPROVER_BITVECTOR; }

"__thread"      { if(PARSER.mode==ansi_c_parsert::GCC ||
                     PARSER.mode==ansi_c_parsert::ARM)
                    { loc(); return TOK_THREAD_LOCAL; }
                  else
                    return make_identifier();
                }
}

  /* operands following */

<GRAMMAR>{
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
"<<="		{ loc(); return TOK_SLASSIGN; }
">>="		{ loc(); return TOK_SRASSIGN; }
"&="		{ loc(); return TOK_ANDASSIGN; }
"^="		{ loc(); return TOK_EORASSIGN; }
"|="		{ loc(); return TOK_ORASSIGN; }
}

<GRAMMAR>{

{identifier}	{ return make_identifier(); }

{decinteger} |
{decinteger_l} |
{decinteger_ll} |
{decinteger_u} |
{decinteger_ul} |
{decinteger_ull} |
{decinteger_w} |
{decinteger_uw} { newstack(yyansi_clval);
                  stack(yyansi_clval)=convert_integer_literal(yytext, 10);
                  PARSER.set_location(stack(yyansi_clval));
                  return TOK_INTEGER;
                }

{octinteger} |
{octinteger_l} |
{octinteger_ll} |
{octinteger_u} |
{octinteger_ul} |
{octinteger_ull} |
{octinteger_w} |
{octinteger_uw} { newstack(yyansi_clval);
                  stack(yyansi_clval)=convert_integer_literal(yytext, 8);
                  PARSER.set_location(stack(yyansi_clval));
                  return TOK_INTEGER;
                }

{hexinteger} |
{hexinteger_l} |
{hexinteger_ll} |
{hexinteger_u} |
{hexinteger_ul} |
{hexinteger_ull} |
{hexinteger_w} |
{hexinteger_uw} { newstack(yyansi_clval);
                  stack(yyansi_clval)=convert_integer_literal(yytext, 16);
                  PARSER.set_location(stack(yyansi_clval));
                  return TOK_INTEGER;
                }

{float}		{ newstack(yyansi_clval); 
                  stack(yyansi_clval)=convert_float_literal(yytext);
                  PARSER.set_location(stack(yyansi_clval));
		  return TOK_FLOATING;
		}
{float_f}	{ newstack(yyansi_clval); 
                  stack(yyansi_clval)=convert_float_literal(yytext);
                  PARSER.set_location(stack(yyansi_clval));
		  return TOK_FLOATING;
		}
{float_l}	{ newstack(yyansi_clval); 
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
"__volatile__"  { yyless(0); BEGIN(GRAMMAR); loc(); return TOK_GCC_ASM_PAREN; }
.               { yyless(0); BEGIN(GRAMMAR); loc(); PARSER.asm_block_following=true; return TOK_GCC_ASM; }
}

<GCC_ATTRIBUTE1>{
"("{ws}"("      { BEGIN(GCC_ATTRIBUTE2); PARSER.parenthesis_counter=0; }
{ws}            { /* ignore */ }
{newline}       { /* ignore */ }
.               { BEGIN(GRAMMAR); loc(); return yytext[0]; }
}

<GCC_ATTRIBUTE2>{ // an attribute is following -- these may be keywords!

"vector_size" |
"__vector_size__"   { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_VECTOR_SIZE; }

"packed" |
"__packed__"        { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_PACKED; }

"transparent_union" |
"__transparent_union__" { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_TRANSPARENT_UNION; }

{ws}                { /* ignore */ }
{newline}           { /* ignore */ }
{identifier}        { BEGIN(GCC_ATTRIBUTE4); }
")"                 { BEGIN(GCC_ATTRIBUTE5); }
.                   { /* ignore */ }
}

<GCC_ATTRIBUTE3>{ // an attribute we do process
"("             { PARSER.parenthesis_counter++; loc(); return '('; }
")"             { if(PARSER.parenthesis_counter==0)
                    BEGIN(GCC_ATTRIBUTE5);
                  else
                  {
                    PARSER.parenthesis_counter--;
                    loc();
                    return ')';
                  }
                }
","             { if(PARSER.parenthesis_counter==0)
                    BEGIN(GCC_ATTRIBUTE2);
                  else
                  {
                    loc();
                    return ',';
                  }
                }
{decinteger} |
{decinteger_l} |
{decinteger_ll} |
{decinteger_u} |
{decinteger_ul} |
{decinteger_ull} |
{decinteger_w} |
{decinteger_uw} { newstack(yyansi_clval);
                  stack(yyansi_clval)=convert_integer_literal(yytext, 10);
                  PARSER.set_location(stack(yyansi_clval));
                  return TOK_INTEGER;
                }
{ws}            { /* ignore */ }
{newline}       { /* ignore */ }
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
