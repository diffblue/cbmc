%option nounput
%option noinput
%option stack

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

#include <util/string_constant.h>
#include <util/unicode.h>

#include "preprocessor_line.h"

#include "literals/convert_float_literal.h"
#include "literals/convert_integer_literal.h"
#include "literals/convert_character_literal.h"
#include "literals/convert_string_literal.h"
#include "literals/unescape_string.h"

#define PARSER ansi_c_parser
#define YYSTYPE unsigned
#undef  ECHO
#define ECHO

#include "ansi_c_parser.h"
#include "ansi_c_y.tab.h"
#ifdef ANSI_C_DEBUG
extern int yyansi_cdebug;
#endif

#define loc() \
  { newstack(yyansi_clval); PARSER.set_source_location(stack(yyansi_clval)); }

int make_identifier()
{
  loc();
  
  // deal with universal charater names
  std::string final_base_name;
  final_base_name.reserve(yyleng);
  
  for(const char *p=yytext; *p!=0; p++)
  {
    if(p[0]=='\\' && (p[1]=='u' || p[1]=='U'))
    {
      p++;
      unsigned digits=(*p=='u')?4:8;
      p++;
      unsigned letter=hex_to_unsigned(p, digits);
      for(; *p!=0 && digits>0; digits--, p++);
      p--; // go back for p++ later
      
      std::basic_string<unsigned> utf32;
      utf32+=letter;
      
      // turn into utf-8
      const std::string utf8_value = utf32_native_endian_to_utf8(utf32);
      final_base_name+=utf8_value;
    }
    else
      final_base_name+=*p;
  }
  
  if(PARSER.cpp98)
  {
    stack(yyansi_clval).id(ID_symbol);
    stack(yyansi_clval).set(ID_C_base_name, final_base_name);
    return TOK_IDENTIFIER;
  }
  else
  {
    // this hashes the base name
    irep_idt base_name=final_base_name;

    // figure out if this is a typedef or something else
    irep_idt identifier;
    ansi_c_id_classt result=
      PARSER.lookup(base_name, identifier, PARSER.tag_following, false);

    PARSER.tag_following=false;

    stack(yyansi_clval).set(ID_C_base_name, base_name);
    stack(yyansi_clval).set(ID_identifier, identifier);
    stack(yyansi_clval).set(ID_C_id_class, static_cast<int>(result));

    if(result==ansi_c_id_classt::ANSI_C_TYPEDEF)
    {
      stack(yyansi_clval).id(ID_typedef_type);
      return TOK_TYPEDEFNAME;
    }
    else
    {
      stack(yyansi_clval).id(ID_symbol);
      return TOK_IDENTIFIER;
    }
  }
}

int MSC_Keyword(int token)
{
  if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
  {
    loc();
    PARSER.tag_following=false;
    return token;
  }
  else
    return make_identifier();
}

int cpp98_keyword(int token)
{
  if(PARSER.cpp98)
  {
    loc();
    return token;
  }
  else
    return make_identifier();
}

int cpp11_keyword(int token)
{
  if(PARSER.cpp11)
  {
    loc();
    return token;
  }
  else
    return make_identifier();
}

int MSC_cpp_keyword(int token)
{
  if(PARSER.cpp98 && PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
  {
    loc();
    return token;
  }
  else
    return make_identifier();
}

int cpp_operator(int token)
{
  if(PARSER.cpp98)
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

#include <util/pragma_wsign_compare.def>
#include <util/pragma_wnull_conversion.def>
#include <util/pragma_wdeprecated_register.def>

/*** macros for easier rule definition **********************************/
%}

delimiter       [ \t\b\r]
newline         [\n\f\v]|"\\\n"
whitespace      {delimiter}+
ws              {delimiter}*
ucletter        [A-Z]
lcletter        [a-z]
letter          ({ucletter}|{lcletter})
digit           [0-9]
bindigit        [01]
octdigit        [0-7]
hexdigit        [0-9a-fA-F]
utf8letter      [\x80-\xff]
universal_character	("\\u"{hexdigit}{4})|("\\U"{hexdigit}{8})
identifier      (({letter}|"_"|"$"|{utf8letter}|{universal_character})({letter}|{digit}|"_"|"$"|{utf8letter}|{universal_character})*)
integer         {digit}+
binary          {bindigit}+
msiw_suffix     ([iI]("8"|"16"|"32"|"64"|"128"))
int_suffix      [uUlLiIjJ]*|[uU]?{msiw_suffix}
bininteger      "0"[bB]({bindigit}|"'")+{int_suffix}
decinteger      [1-9]({digit}|"'")*{int_suffix}
octinteger      "0"({octdigit}|"'")*{int_suffix}
hexinteger      "0"[xX]{hexdigit}({hexdigit}|"'")*{int_suffix}
integer_s       {decinteger}|{bininteger}|{octinteger}|{hexinteger}
exponent        [eE][+-]?{integer}
fraction        {integer}
float1          {integer}"."{fraction}?({exponent})?
float2          "."{fraction}({exponent})?
float3          {integer}{exponent}
hexfloat1       "0"[xX]{hexdigit}*"."{hexdigit}+[pP][+-]?{integer}
hexfloat2       "0"[xX]{hexdigit}*"."[pP][+-]?{integer}
hexfloat3       "0"[xX]{hexdigit}*[pP][+-]?{integer}
float_suffix    [fFlLiIjJ]*
gcc_ext_float_suffix    [wWqQ]|[dD][fFdDlL]?|"f16"|"f32"|"f64"|"f128"|"f32x"|"f64x"|"f128x"
float           {float1}|{float2}|{float3}|{hexfloat1}|{hexfloat2}|{hexfloat3}
float_s         {float}{float_suffix}|{integer}[fF]
gcc_ext_float_s {float}{gcc_ext_float_suffix}
cppstart        {ws}"#"{ws}
cpplineno       {cppstart}"line"*{ws}{integer}{ws}.*{newline}
cppdirective    {cppstart}.*

escape_sequence [\\][^\n]
c_char [^'\\\n]|{escape_sequence}
s_char [^"\\\n]|{escape_sequence}

char_lit        ("L"|"u"|"U")?[']{c_char}+[']
string_lit      ("L"|"u"|"U"|"u8")?["]{s_char}*["]

%x GRAMMAR
%x COMMENT1
%x COMMENT2
%x STRING_LITERAL
%x STRING_LITERAL_COMMENT
%x ASM_BLOCK
%x MSC_ASM
%x IGNORE_PARENS
%x MSC_PRAGMA
%x MSC_ANNOTATION
%x GCC_ATTRIBUTE1
%x GCC_ATTRIBUTE1a
%x GCC_ATTRIBUTE2
%x GCC_ATTRIBUTE3
%x GCC_ATTRIBUTE4
%x GCC_ATTRIBUTE5
%x GCC_ASM
%x GCC_ASM_PAREN
%x CPROVER_ID

%{
void ansi_c_scanner_init()
{
#ifdef ANSI_C_DEBUG
  yyansi_cdebug=1;
#endif
  YY_FLUSH_BUFFER;
  BEGIN(0);
}
%}

%%

<INITIAL>.|\n   { BEGIN(GRAMMAR);
                  yyless(0); /* start again with this character */
                }

<GRAMMAR>"/*"   { BEGIN(COMMENT1); } /* begin C comment state */

<COMMENT1>{
   "*/"         { BEGIN(GRAMMAR); } /* end comment state, back to GRAMMAR */
   "/*"         { yyansi_cerror("Probably nested comments"); }
   <<EOF>>      { yyansi_cerror("Unterminated comment"); return TOK_SCANNER_ERROR; }
   [^*/\n]*     { /* ignore every char except '*' and NL (performance!) */ }
   .            { } /* all single characters within comments are ignored */
   \n           { }
}

<STRING_LITERAL_COMMENT>{
   "*/"         { yy_pop_state(); } /* end comment state, back to STRING_LITERAL */
   "/*"         { yyansi_cerror("Probably nested comments"); }
   <<EOF>>      { yyansi_cerror("Unterminated comment"); return TOK_SCANNER_ERROR; }
   [^*/\n]*     { /* ignore every char except '*' and NL (performance!) */ }
   .            { } /* all single characters within comments are ignored */
   \n           { }
}

<GRAMMAR>"//"   { BEGIN(COMMENT2); } /* begin C++ comment state */

<COMMENT2>{
   \n           { BEGIN(GRAMMAR); } /* end comment state, back GRAMMAR */
   .*           { } /* all characters within comments are ignored */
}

<GRAMMAR>{char_lit} {
                  newstack(yyansi_clval);
                  stack(yyansi_clval)=convert_character_literal(yytext, true);
                  PARSER.set_source_location(stack(yyansi_clval));
                  return TOK_CHARACTER;
                }

<GRAMMAR,GCC_ATTRIBUTE3>{string_lit} {
                  PARSER.string_literal.clear();
                  PARSER.string_literal.append(yytext);
                  loc();
                  // String literals can be continued in
                  // the next line
                  yy_push_state(STRING_LITERAL);
                  // use yy_top_state() to keep the compiler happy
                  (void)yy_top_state();
                }

<STRING_LITERAL>{string_lit} { PARSER.string_literal.append(yytext); }
<STRING_LITERAL>{newline} { /* ignore */ }
<STRING_LITERAL>{whitespace} { /* ignore */ }
<STRING_LITERAL>{cpplineno} {
                  preprocessor_line(yytext, PARSER);
                  PARSER.set_line_no(PARSER.get_line_no()-1);
                }
<STRING_LITERAL>{cppdirective} { /* ignore */ }
<STRING_LITERAL>"/*" { yy_push_state(STRING_LITERAL_COMMENT); /* C comment, ignore */ }
<STRING_LITERAL>"//".*\n { /* C++ comment, ignore */ }
<STRING_LITERAL>. { // anything else: back to normal
                  source_locationt l=stack(yyansi_clval).source_location();
                  stack(yyansi_clval)=convert_string_literal(PARSER.string_literal);
                  stack(yyansi_clval).add_source_location().swap(l);
                  yy_pop_state(); // back to normal
                  yyless(0); // put back
                  return TOK_STRING;
                }

<GRAMMAR>{newline} { } /* skipped */
<GRAMMAR>{whitespace} { } /* skipped */

<GRAMMAR>{cpplineno} {
                  preprocessor_line(yytext, PARSER);
                  PARSER.set_line_no(PARSER.get_line_no()-1);
                }

<GRAMMAR>{cppstart}"pragma"{ws}"pack"{ws}"("{ws}"push"{ws}")"{ws}{newline} {
                  // Done by Visual Studio and gcc
                  // http://msdn.microsoft.com/en-us/library/2e70t5y1%28v=vs.80%29.aspx
                  // push, pop could also use identifiers
                  if(PARSER.pragma_pack.empty())
                    PARSER.pragma_pack.push_back(convert_integer_literal("0"));
                  else
                    PARSER.pragma_pack.push_back(PARSER.pragma_pack.back());
                }

<GRAMMAR>{cppstart}"pragma"{ws}"pack"{ws}"("{ws}"push"{ws}","{ws}{integer_s}{ws}")"{ws}{newline} {
                  // Done by Visual Studio and gcc
                  // http://msdn.microsoft.com/en-us/library/2e70t5y1%28v=vs.80%29.aspx
                  // push, pop could also use identifiers
                  std::string tmp(yytext);
                  std::string::size_type p=tmp.find(',')+1;
                  while(tmp[p]==' ' || tmp[p]=='\t') ++p;
                  std::string value=std::string(tmp, p, tmp.find_last_not_of(") \t\n\r")+1-p);
                  exprt n=convert_integer_literal(value);
                  PARSER.pragma_pack.push_back(n);
                }

<GRAMMAR>{cppstart}"pragma"{ws}"pack"{ws}"("{ws}{integer_s}{ws}")"{ws}{newline} {
                  // Done by Visual Studio and gcc
                  // http://msdn.microsoft.com/en-us/library/2e70t5y1%28v=vs.80%29.aspx
                  std::string tmp(yytext);
                  std::string::size_type p=tmp.find('(')+1;
                  while(tmp[p]==' ' || tmp[p]=='\t') ++p;
                  std::string value=std::string(tmp, p, tmp.find_last_not_of(") \t\n\r")+1-p);
                  exprt n=convert_integer_literal(value);
                  PARSER.pragma_pack.push_back(n);
                }

<GRAMMAR>{cppstart}"pragma"{ws}"pack"{ws}"("{ws}"pop"{ws}")"{ws}{newline} {
                  // Done by Visual Studio and gcc
                  // http://msdn.microsoft.com/en-us/library/2e70t5y1%28v=vs.80%29.aspx
                  // push, pop could also use identifiers
                  if(!PARSER.pragma_pack.empty()) PARSER.pragma_pack.pop_back();
                }

<GRAMMAR>{cppstart}"pragma"{ws}"pack"{ws}"("{ws}")"{ws}{newline} {
                  // Done by Visual Studio and gcc
                  // http://msdn.microsoft.com/en-us/library/2e70t5y1%28v=vs.80%29.aspx
                  // should be equivalent to pop-all
                  PARSER.pragma_pack.clear();
                }

<GRAMMAR>{cppstart}"pragma"{ws}.* {
                  // silently ignore other pragmas
                }

<GRAMMAR>{cppstart}"ident"{ws}.* { /* ignore */ }
<GRAMMAR>{cppstart}"define"{ws}.* { /* ignore */ }
<GRAMMAR>{cppstart}"undef"{ws}.* { /* ignore */ }

<GRAMMAR>{cppstart}"asm" {
                  if(PARSER.mode==configt::ansi_ct::flavourt::GCC)  // really, this is BCC
                  {
                    BEGIN(ASM_BLOCK);
                    PARSER.string_literal.clear();
                    loc();
                    return '{';
                  }
                  else
                    return make_identifier();
                }

<GRAMMAR>{cppstart}"endasm" {
                  loc();
                  return '}';
                }

<GRAMMAR>{cppdirective} {
                  yyansi_cerror("Preprocessor directive found");
                  return TOK_SCANNER_ERROR;
                }

%{
/*** keywords ***/
%}

<GRAMMAR,GCC_ATTRIBUTE3>{
"auto"          { loc(); return TOK_AUTO; }
"_Bool"         { if(PARSER.cpp98)
                    return make_identifier();
                  else
                  { loc(); return TOK_BOOL; }
                }
"break"         { loc(); return TOK_BREAK; }
"case"          { loc(); return TOK_CASE; }
"char"          { loc(); return TOK_CHAR; }
"_Complex"      { loc(); return TOK_COMPLEX; }
"const"         { loc(); return TOK_CONST; }
"continue"      { loc(); return TOK_CONTINUE; }
"default"       { loc(); return TOK_DEFAULT; }
"do"            { loc(); return TOK_DO; }
"double"        { loc(); return TOK_DOUBLE; }
"else"          { loc(); return TOK_ELSE; }
"enum"          { loc(); PARSER.tag_following=true; return TOK_ENUM; }
"extern"        { loc(); return TOK_EXTERN; }
"float"         { loc(); return TOK_FLOAT; }
"for"           { loc(); return TOK_FOR; }
"goto"          { loc(); return TOK_GOTO; }
"if"            { loc(); return TOK_IF; }
"inline"        { loc(); return TOK_INLINE; }
"int"           { loc(); return TOK_INT; }
"long"          { loc(); return TOK_LONG; }
"register"      { loc(); return TOK_REGISTER; }
"restrict"      { loc(); return TOK_RESTRICT; }
"return"        { loc(); return TOK_RETURN; }
"short"         { loc(); return TOK_SHORT; }
"signed"        { loc(); return TOK_SIGNED; }
"sizeof"        { loc(); return TOK_SIZEOF; }
"static"        { loc(); return TOK_STATIC; }
"struct"        { loc(); PARSER.tag_following=true; return TOK_STRUCT; }
"switch"        { loc(); return TOK_SWITCH; }
"typedef"       { loc(); return TOK_TYPEDEF; }
"union"         { loc(); PARSER.tag_following=true; return TOK_UNION; }
"unsigned"      { loc(); return TOK_UNSIGNED; }
"void"          { loc(); return TOK_VOID; }
"volatile"      { loc(); return TOK_VOLATILE; }
"while"         { loc(); return TOK_WHILE; }

"__auto_type"   { if((PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                      PARSER.mode==configt::ansi_ct::flavourt::CLANG)
                     && !PARSER.cpp98)
                  { loc(); return TOK_GCC_AUTO_TYPE; }
                  else
                    return make_identifier();
                }

"_Float16"      { if(PARSER.ts_18661_3_Floatn_types)
                  { loc(); return TOK_GCC_FLOAT16; }
                  else
                    return make_identifier();
                }

"_Float32"      { if(PARSER.ts_18661_3_Floatn_types)
                  { loc(); return TOK_GCC_FLOAT32; }
                  else
                    return make_identifier();
                }

"_Float32x"     { if(PARSER.ts_18661_3_Floatn_types)
                  { loc(); return TOK_GCC_FLOAT32X; }
                  else
                    return make_identifier();
                }

"_Float64"      { if(PARSER.ts_18661_3_Floatn_types)
                  { loc(); return TOK_GCC_FLOAT64; }
                  else
                    return make_identifier();
                }

"_Float64x"     { if(PARSER.ts_18661_3_Floatn_types)
                  { loc(); return TOK_GCC_FLOAT64X; }
                  else
                    return make_identifier();
                }

"__CPROVER_Float64x" {
                  loc(); return TOK_GCC_FLOAT64X;
                }

"__CPROVER_Float80" {
                  loc(); return TOK_GCC_FLOAT80;
                }

"__float128"    { // This is a keyword for CLANG,
                  // but a typedef for GCC
                  if(PARSER.mode==configt::ansi_ct::flavourt::CLANG)
                  { loc(); return TOK_GCC_FLOAT128; }
                  else
                    return make_identifier();
                }

"_Float128"     { if(PARSER.Float128_type)
                  { loc(); return TOK_GCC_FLOAT128; }
                  else
                    return make_identifier();
                }

"__CPROVER_Float128" {
                  loc(); return TOK_GCC_FLOAT128;
                }

"_Float128x"    { if(PARSER.ts_18661_3_Floatn_types)
                  { loc(); return TOK_GCC_FLOAT128X; }
                  else
                    return make_identifier();
                }

"__int128"      { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG)
                  { loc(); return TOK_GCC_INT128; }
                  else
                    return make_identifier();
                }

"_Decimal32"    { // clang doesn't have it
                  if(PARSER.mode==configt::ansi_ct::flavourt::GCC)
                    { loc(); return TOK_GCC_DECIMAL32; }
                  else
                    return make_identifier();
                }

"_Decimal64"    { // clang doesn't have it
                  if(PARSER.mode==configt::ansi_ct::flavourt::GCC)
                    { loc(); return TOK_GCC_DECIMAL64; }
                  else
                    return make_identifier();
                }

"_Decimal128"   { // clang doesn't have it
                  if(PARSER.mode==configt::ansi_ct::flavourt::GCC)
                    { loc(); return TOK_GCC_DECIMAL128; }
                  else
                    return make_identifier();
                }

"__int8"        { return MSC_Keyword(TOK_INT8); }
"__int16"       { return MSC_Keyword(TOK_INT16); }
"__int32"       { return MSC_Keyword(TOK_INT32); }

"__int64"       { if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM ||
                     PARSER.mode==configt::ansi_ct::flavourt::CODEWARRIOR)
                    { loc(); return TOK_INT64; }
                  else
                    return make_identifier();
                }
"_int64"        { if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
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
"__complex"     { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_COMPLEX; }
                  else
                    return make_identifier();
                }

"__real__" |
"__real"        { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_REAL; }
                  else
                    return make_identifier();
                }

"__imag__" |
"__imag"        { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_IMAG; }
                  else
                    return make_identifier();
                }

%{
/* note: "wchar_t" should be in the list above, but it is left out */
/*       because it is a 'typedef' in some standard header files   */
%}

"_var_arg_typeof" { if(PARSER.mode==configt::ansi_ct::flavourt::CODEWARRIOR)
                    { loc(); return TOK_CW_VAR_ARG_TYPEOF; }
                  else
                    return make_identifier();
                }

"__builtin_va_arg" { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                        PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                        PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_BUILTIN_VA_ARG; }
                  else
                    return make_identifier();
                }

"__builtin_offsetof" |
"__offsetof__" |
"offsetof"      { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_OFFSETOF; }
                  else
                    return make_identifier();
                }

"__builtin_types_compatible_p" {
                  if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_GCC_BUILTIN_TYPES_COMPATIBLE_P; }
                  else
                    return make_identifier();
                }

"__builtin_convertvector" {
                  if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG)
                    { loc(); return TOK_CLANG_BUILTIN_CONVERTVECTOR; }
                  else
                    return make_identifier();
                }

"__alignof__"   { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_ALIGNOF; }
                  else
                    return make_identifier();
                }

"__alignof"     { // MS supports __alignof:
                  // http://msdn.microsoft.com/en-us/library/45t0s5f4%28v=vs.71%29.aspx
                  if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO ||
                     PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_ALIGNOF; }
                  else
                    return make_identifier();
                }

"__ALIGNOF__"   { if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_ALIGNOF; }
                  else
                    return make_identifier();
                }

"__builtin_alignof" {
                  // interestingly, gcc doesn't support this,
                  // but Visual Studio does!
                  if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_ALIGNOF; }
                  else
                    return make_identifier();
                }

"__asm"         { if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
                  {
                    loc();
                    BEGIN(MSC_ASM);
                    return TOK_MSC_ASM;
                  }
                  else if(PARSER.cpp98)
                  {
                    loc();
                    return TOK_GCC_ASM;
                  }
                  else
                    BEGIN(GCC_ASM);
                }

"asm"           { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::CODEWARRIOR)
                  {
                    if(PARSER.cpp98)
                    {
                      loc();
                      return TOK_GCC_ASM;
                    }
                    else
                      BEGIN(GCC_ASM);
                  }
                  else
                    return make_identifier();
                }

"__asm__"       { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::CODEWARRIOR ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    if(PARSER.cpp98)
                    {
                      loc();
                      return TOK_GCC_ASM;
                    }
                    else
                      BEGIN(GCC_ASM);
                  }
                  else
                    return make_identifier();
                }

"__based"       { if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
                    { loc(); return TOK_MSC_BASED; }
                  else
                    return make_identifier();
                }

"__unaligned"   { if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
                    { /* ignore for now */ }
                  else
                    return make_identifier();
                }

"__wchar_t"     { if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
                    { loc(); return TOK_WCHAR_T; }
                  else
                    return make_identifier();
                }

%{
/* C++ Keywords and Operators */
%}

alignas             { return cpp11_keyword(TOK_ALIGNAS); } // C++11
alignof             { return cpp11_keyword(TOK_ALIGNOF); } // C++11
and                 { return cpp98_keyword(TOK_ANDAND); }
and_eq              { return cpp98_keyword(TOK_ANDASSIGN); }
bool                { return cpp98_keyword(TOK_BOOL); }
catch               { return cpp98_keyword(TOK_CATCH); }
char16_t            { // C++11, but Visual Studio uses typedefs
                      if(PARSER.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO)
                        return make_identifier();
                      else
                        return cpp11_keyword(TOK_CHAR16_T);
                    }
char32_t            { // C++11, but Visual Studio uses typedefs
                      if(PARSER.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO)
                        return make_identifier();
                      else
                        return cpp11_keyword(TOK_CHAR32_T);
                    }
class               { return cpp98_keyword(TOK_CLASS); }
compl               { return cpp98_keyword('~'); }
constexpr           { return cpp11_keyword(TOK_CONSTEXPR); } // C++11
delete              { return cpp98_keyword(TOK_DELETE); }
decltype            { return cpp11_keyword(TOK_DECLTYPE); } // C++11
explicit            { return cpp98_keyword(TOK_EXPLICIT); }
false               { return cpp98_keyword(TOK_FALSE); }
friend              { return cpp98_keyword(TOK_FRIEND); }
mutable             { return cpp98_keyword(TOK_MUTABLE); }
namespace           { return cpp98_keyword(TOK_NAMESPACE); }
new                 { return cpp98_keyword(TOK_NEW); }
noexcept            { return cpp11_keyword(TOK_NOEXCEPT); } // C++11
noreturn            { return cpp11_keyword(TOK_NORETURN); } // C++11
not                 { return cpp98_keyword('!'); }
not_eq              { return cpp98_keyword(TOK_NE); }
nullptr             { return cpp11_keyword(TOK_NULLPTR); } // C++11
operator            { return cpp98_keyword(TOK_OPERATOR); }
or                  { return cpp98_keyword(TOK_OROR); }
or_eq               { return cpp98_keyword(TOK_ORASSIGN); }
private             { return cpp98_keyword(TOK_PRIVATE); }
protected           { return cpp98_keyword(TOK_PROTECTED); }
public              { return cpp98_keyword(TOK_PUBLIC); }
static_assert       { return cpp11_keyword(TOK_STATIC_ASSERT); } // C++11
template            { return cpp98_keyword(TOK_TEMPLATE); }
this                { return cpp98_keyword(TOK_THIS); }
thread_local        { return cpp11_keyword(TOK_THREAD_LOCAL); } // C++11
throw               { return cpp98_keyword(TOK_THROW); }
true                { return cpp98_keyword(TOK_TRUE); }
typeid              { return cpp98_keyword(TOK_TYPEID); }
typename            { return cpp98_keyword(TOK_TYPENAME); }
using               { return cpp98_keyword(TOK_USING); }
virtual             { return cpp98_keyword(TOK_VIRTUAL); }
wchar_t             { // CodeWarrior doesn't have wchar_t built in,
                      // and MSC has a command-line option to turn it off
                      if(PARSER.mode==configt::ansi_ct::flavourt::CODEWARRIOR)
                        return make_identifier();
                      else
                        return cpp98_keyword(TOK_WCHAR_T);
                    }
xor                 { return cpp98_keyword('^'); }
xor_eq              { return cpp98_keyword(TOK_XORASSIGN); }
".*"                { return cpp_operator(TOK_DOTPM); }
"->*"               { return cpp_operator(TOK_ARROWPM); }
"::"                { if(PARSER.cpp98)
                        return cpp_operator(TOK_SCOPE);
                      else
                      {
                        yyless(1); // puts all but one : back into stream
                        loc();
                        PARSER.tag_following=false;
                        return ':';
                      }
                    }

__decltype          { if(PARSER.cpp98 &&
                         (PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                          PARSER.mode==configt::ansi_ct::flavourt::CLANG))
                        return cpp98_keyword(TOK_DECLTYPE);
                      else
                        return make_identifier();
                    }

%{
/* a huge batch of MS C++ extensions
   http://msdn.microsoft.com/en-us/library/ms177194(v=vs.80).aspx
   Clang and GCC support several of them as well:
   http://clang.llvm.org/docs/LanguageExtensions.html#checks-for-type-trait-primitives */
%}

"__has_assign"      { loc(); return MSC_cpp_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__has_copy"        { loc(); return MSC_cpp_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__has_finalizer"   { loc(); return MSC_cpp_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__has_nothrow_assign" { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__has_nothrow_constructor" { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__has_nothrow_copy" { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__has_trivial_assign" { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__has_trivial_constructor" { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__has_trivial_copy" { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__has_trivial_destructor" { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__has_user_destructor" { loc(); return MSC_cpp_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__has_virtual_destructor" { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_abstract"     { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_base_of"      { loc(); return cpp98_keyword(TOK_BINARY_TYPE_PREDICATE); }
"__is_class"        { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_convertible_to" { loc(); return cpp98_keyword(TOK_BINARY_TYPE_PREDICATE); }
"__is_delegate"     { loc(); return MSC_cpp_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_empty"        { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_enum"         { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_interface_class" { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_pod"          { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_polymorphic"  { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_ref_array"    { loc(); return MSC_cpp_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_ref_class"    { loc(); return MSC_cpp_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_sealed"       { loc(); return MSC_cpp_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_simple_value_class" { loc(); return MSC_cpp_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_union"        { loc(); return cpp98_keyword(TOK_UNARY_TYPE_PREDICATE); }
"__is_value_class"  { loc(); return MSC_cpp_keyword(TOK_UNARY_TYPE_PREDICATE); }

"__if_exists"       { loc(); return MSC_cpp_keyword(TOK_MSC_IF_EXISTS); }
"__if_not_exists"   { loc(); return MSC_cpp_keyword(TOK_MSC_IF_NOT_EXISTS); }
"__underlying_type" { loc(); return cpp98_keyword(TOK_UNDERLYING_TYPE); }

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
"["{ws}"export"  { if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
                     BEGIN(MSC_ANNOTATION);
                   else
                   {
                     yyless(1); // puts all but [ back into stream
                     loc();
                     PARSER.tag_following=false;
                     return yytext[0]; // returns the [
                   }
                 }

"__char16_t"     { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                      PARSER.mode==configt::ansi_ct::flavourt::CLANG)
                     return cpp98_keyword(TOK_CHAR16_T); // GNU extension
                   else
                     return make_identifier();
                 }

"__nullptr"     { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                      PARSER.mode==configt::ansi_ct::flavourt::CLANG)
                     return cpp98_keyword(TOK_NULLPTR); // GNU extension
                   else
                     return make_identifier();
                 }

"__null"         { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                      PARSER.mode==configt::ansi_ct::flavourt::CLANG)
                     return cpp98_keyword(TOK_NULLPTR); // GNU extension
                   else
                     return make_identifier();
                 }

"__char32_t"     { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                      PARSER.mode==configt::ansi_ct::flavourt::CLANG)
                     return cpp98_keyword(TOK_CHAR32_T); // GNU extension
                   else
                     return make_identifier();
                 }

"__declspec" |
"_declspec"     { if(PARSER.cpp98)
                  {
                    BEGIN(IGNORE_PARENS);
                  }
                  else if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO ||
                          PARSER.mode==configt::ansi_ct::flavourt::CODEWARRIOR ||
                          PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    loc(); return TOK_MSC_DECLSPEC;
                  }
                  else if(PARSER.mode==configt::ansi_ct::flavourt::GCC)
                  {
                    // GCC supports this on Windows as an exception!
                    // Should likely reject on other targets.
                    loc(); return TOK_MSC_DECLSPEC;
                  }
                  else
                    return make_identifier();
                }

"__pragma"      { if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
                  {
                    BEGIN(MSC_PRAGMA);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__attribute__" |
"__attribute"   { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::CODEWARRIOR ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    BEGIN(GCC_ATTRIBUTE1);
                    loc();
                    return TOK_GCC_ATTRIBUTE;
                  }
                  else
                    return make_identifier();
                }

"__aligned"     { /* ignore */ }
"__aligned__"   { /* ignore */ }

"__extension__" { /* ignore */ }

"__restrict"    { loc(); return TOK_RESTRICT; }
"__restrict__"  { loc(); return TOK_RESTRICT; }

"_cdecl"        { /* ignore */ }
"__cdecl"       { /* ignore */ }
"__cdecl__"     { /* ignore */ }
"_stdcall"      { /* ignore */ }
"__stdcall"     { /* ignore */ }
"_fastcall"     { /* ignore */ }
"__fastcall"    { /* ignore */ }
"__thiscall"    { /* ignore */ }
"__clrcall"     { /* ignore */ }
"__vectorcall"  { /* ignore */ }
"__w64"         { /* ignore */ }

"__const"       { loc(); return TOK_CONST; }
"__const__"     { loc(); return TOK_CONST; }

"__signed"      { loc(); return TOK_SIGNED; }
"__signed__"    { loc(); return TOK_SIGNED; }

"__volatile"    { loc(); return TOK_VOLATILE; }
"__volatile__"  { loc(); return TOK_VOLATILE; }

"__pure"        { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__align"       { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    BEGIN(IGNORE_PARENS);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__smc"         { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    BEGIN(IGNORE_PARENS);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__INTADDR__"   { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__irq"         { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__packed"      { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__value_in_regs" { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__weak"        { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__writeonly"   { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"__global_reg"  { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    BEGIN(IGNORE_PARENS);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__svc"         { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    BEGIN(IGNORE_PARENS);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__svc_indirect" { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    BEGIN(IGNORE_PARENS);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__svc_indirect_r7" { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    BEGIN(IGNORE_PARENS);
                    PARSER.parenthesis_counter=0;
                  }
                  else
                    return make_identifier();
                }

"__softfp"      { /* an ARM extension */
                  if(PARSER.mode==configt::ansi_ct::flavourt::ARM)
                  {
                    // ignore
                  }
                  else
                    return make_identifier();
                }

"typeof"        { if(PARSER.cpp98 ||
                     PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::CODEWARRIOR ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_TYPEOF; }
                  else
                    return make_identifier();
                }
"__typeof"      { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_TYPEOF; }
                  else
                    return make_identifier();
                }

"__typeof__"    { loc(); return TOK_TYPEOF; }

"__forceinline" { if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_MSC_FORCEINLINE; }
                  else
                    return make_identifier();
                }

"_inline"       { // http://msdn.microsoft.com/en-us/library/z8y1yy88.aspx
                  if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
                    { loc(); return TOK_INLINE; }
                  else
                    return make_identifier();
                }

"__inline"      { loc(); return TOK_INLINE; }
"__inline__"    { loc(); return TOK_INLINE; }

"__label__"     { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_GCC_LABEL; }
                  else
                    return make_identifier();
                }

"__try"         { if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
                    { loc(); return TOK_MSC_TRY; }
                  else
                    return make_identifier();
                }

"try"           { if(PARSER.cpp98) // C++?
                    { loc(); return TOK_TRY; }
                  else
                    return make_identifier();
                }

"__finally"     { if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
                    { loc(); return TOK_MSC_FINALLY; }
                  else
                    return make_identifier();
                }

"__except"      { if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
                    { loc(); return TOK_MSC_EXCEPT; }
                  else
                    return make_identifier();
                }

"__leave"       { if(PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
                    { loc(); return TOK_MSC_LEAVE; }
                  else
                    return make_identifier();
                }

"__CPROVER_atomic"       { loc(); return TOK_CPROVER_ATOMIC; }
"__CPROVER_forall"       { loc(); return TOK_FORALL; }
"__CPROVER_exists"       { loc(); return TOK_EXISTS; }
"__CPROVER_array_of"     { loc(); return TOK_ARRAY_OF; }
"__CPROVER_thread_local" { loc(); return TOK_THREAD_LOCAL; }
"__CPROVER_bitvector"    { loc(); return TOK_CPROVER_BITVECTOR; }
"__CPROVER_floatbv"      { loc(); return TOK_CPROVER_FLOATBV; }
"__CPROVER_fixedbv"      { loc(); return TOK_CPROVER_FIXEDBV; }
"__CPROVER_bool"         { loc(); return TOK_CPROVER_BOOL; }
"__CPROVER_throw"        { loc(); return TOK_CPROVER_THROW; }
"__CPROVER_catch"        { loc(); return TOK_CPROVER_CATCH; }
"__CPROVER_try"          { loc(); return TOK_CPROVER_TRY; }
"__CPROVER_finally"      { loc(); return TOK_CPROVER_FINALLY; }
"__CPROVER_ID"           { loc(); return TOK_CPROVER_ID; }
"__CPROVER_loop_invariant" { loc(); return TOK_CPROVER_LOOP_INVARIANT; }
"__CPROVER_requires"     { loc(); return TOK_CPROVER_REQUIRES; }
"__CPROVER_ensures"      { loc(); return TOK_CPROVER_ENSURES; }

"\xe2\x88\x80" |
"\\forall"      { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return TOK_ACSL_FORALL;
                }

"\xe2\x88\x83" |
"\\exists"      { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return TOK_ACSL_EXISTS;
                }

"\\let"         { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return TOK_ACSL_LET;
                }

"\xe2\x87\x92" |
"==>"           { /* Non-standard, obviously. Found in Spec# and ACSL syntax. */
                  loc(); return TOK_IMPLIES;
                }

"\xe2\x87\x94" |
"<==>"          { /* Non-standard, obviously. Found in Spec# and ACSL syntax. */
                  loc(); return TOK_EQUIVALENT;
                }

"\xe2\x89\xa5"  { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return TOK_GE;
                }

"\xe2\x89\xa1"  { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return TOK_EQ;
                }

"\xe2\x89\xa2"  { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return TOK_NE;
                }

"\xe2\x89\xa4"  { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return TOK_LE;
                }

"\xe2\x88\xa7"  { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return TOK_ANDAND;
                }

"\xe2\x88\xa8"  { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return TOK_OROR;
                }

"\xc2\xac"      { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return '!';
                }

"\xe2\x8a\xbb" |
"^^"            { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return TOK_XORXOR;
                }

"\xe2\x88\x92"  { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return '-';
                }

"\\true"        { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return TOK_TRUE;
                }

"\\false"       { /* Non-standard, obviously. Found in ACSL syntax. */
                  loc(); return TOK_FALSE;
                }

"__thread"      { if(PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                     PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                     PARSER.mode==configt::ansi_ct::flavourt::ARM)
                    { loc(); return TOK_THREAD_LOCAL; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Alignas"      { if(!PARSER.cpp98 &&
                     (PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                      PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                      PARSER.mode==configt::ansi_ct::flavourt::ARM))
                    { loc(); return TOK_ALIGNAS; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Alignof"      { if(!PARSER.cpp98 &&
                     (PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                      PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                      PARSER.mode==configt::ansi_ct::flavourt::ARM ||
                      PARSER.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO))
                    { loc(); return TOK_ALIGNOF; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword. It can be used as a type qualifier
     and as a type specifier, which introduces ambiguity into the grammar.
     We thus have two different tokens.

     6.7.2.4 - 4: If the _Atomic keyword is immediately followed by a left
     parenthesis, it is interpreted as a type specifier (with a type name),
     not as a type qualifier.
   */

"_Atomic"{ws}"(" { // put back all but _Atomic
                   yyless(7);

                   if(!PARSER.cpp98 &&
                      (PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                       PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                       PARSER.mode==configt::ansi_ct::flavourt::ARM))
                    { loc(); return TOK_ATOMIC_TYPE_SPECIFIER; }
                  else
                    return make_identifier();
                }

"_Atomic"       { if(!PARSER.cpp98 &&
                     (PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                      PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                      PARSER.mode==configt::ansi_ct::flavourt::ARM))
                    { loc(); return TOK_ATOMIC_TYPE_QUALIFIER; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Generic"      { if(!PARSER.cpp98 &&
                     (PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                      PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                      PARSER.mode==configt::ansi_ct::flavourt::ARM))
                    { loc(); return TOK_GENERIC; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Imaginary"    { if(!PARSER.cpp98 &&
                     (PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                      PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                      PARSER.mode==configt::ansi_ct::flavourt::ARM))
                    { loc(); return TOK_IMAGINARY; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Noreturn"     { if(!PARSER.cpp98 &&
                     (PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                      PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                      PARSER.mode==configt::ansi_ct::flavourt::ARM))
                    { loc(); return TOK_NORETURN; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Static_assert" { if(!PARSER.cpp98 &&
                      (PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                      PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                       PARSER.mode==configt::ansi_ct::flavourt::ARM))
                    { loc(); return TOK_STATIC_ASSERT; }
                  else
                    return make_identifier();
                }

  /* This is a C11 keyword */

"_Thread_local" { if(!PARSER.cpp98 &&
                     (PARSER.mode==configt::ansi_ct::flavourt::GCC ||
                      PARSER.mode==configt::ansi_ct::flavourt::CLANG ||
                      PARSER.mode==configt::ansi_ct::flavourt::ARM))
                    { loc(); return TOK_THREAD_LOCAL; }
                  else
                    return make_identifier();
                }

  /* This is a clang extension */

"_Nullable" { if(PARSER.mode==configt::ansi_ct::flavourt::CLANG)
                { /* ignore */ }
              else
                return make_identifier();
            }

  /* This is a clang extension */

"_Nonnull" { if(PARSER.mode==configt::ansi_ct::flavourt::CLANG)
                { /* ignore */ }
              else
                return make_identifier();
            }

  /* This is a clang extension */

"_Null_unspecified" { if(PARSER.mode==configt::ansi_ct::flavourt::CLANG)
                { /* ignore */ }
              else
                return make_identifier();
            }

}

  /* operators following */

<GRAMMAR,GCC_ATTRIBUTE3>{
"->"            { loc(); return TOK_ARROW; }
"++"            { loc(); return TOK_INCR; }
"--"            { loc(); return TOK_DECR; }
"<<"            { loc(); return TOK_SHIFTLEFT; }
">>"            { loc(); return TOK_SHIFTRIGHT; }
"<="            { loc(); return TOK_LE; }
">="            { loc(); return TOK_GE; }
"=="            { loc(); return TOK_EQ; }
"!="            { loc(); return TOK_NE; }
"&&"            { loc(); return TOK_ANDAND; }
"||"            { loc(); return TOK_OROR; }
"..."           { loc(); return TOK_ELLIPSIS; }

"*="            { loc(); return TOK_MULTASSIGN; }
"/="            { loc(); return TOK_DIVASSIGN; }
"%="            { loc(); return TOK_MODASSIGN; }
"+="            { loc(); return TOK_PLUSASSIGN; }
"-="            { loc(); return TOK_MINUSASSIGN; }
"<<="           { loc(); return TOK_SHLASSIGN; }
">>="           { loc(); return TOK_SHRASSIGN; }
"&="            { loc(); return TOK_ANDASSIGN; }
"^="            { loc(); return TOK_XORASSIGN; }
"|="            { loc(); return TOK_ORASSIGN; }

  /* digraphs */
"<:"            { loc(); return '['; }
":>"            { loc(); return ']'; }
"<%"            { loc(); return '{'; }
"%>"            { loc(); return '}'; }
}

<GRAMMAR>{

{identifier}    { return make_identifier(); }

{integer_s}     { newstack(yyansi_clval);
                  stack(yyansi_clval)=convert_integer_literal(yytext);
                  PARSER.set_source_location(stack(yyansi_clval));
                  return TOK_INTEGER;
                }

{gcc_ext_float_s} { if(PARSER.mode!=configt::ansi_ct::flavourt::GCC)
                    {
                      yyansi_cerror("Preprocessor directive found");
                      return TOK_SCANNER_ERROR;
                    }
                    newstack(yyansi_clval);
                    stack(yyansi_clval)=convert_float_literal(yytext);
                    PARSER.set_source_location(stack(yyansi_clval));
                    return TOK_FLOATING;
                  }

{float_s}       { newstack(yyansi_clval);
                  stack(yyansi_clval)=convert_float_literal(yytext);
                  PARSER.set_source_location(stack(yyansi_clval));
                  return TOK_FLOATING;
                }

"{"             {
                  PARSER.tag_following=false;
                  if(PARSER.asm_block_following)
                  {
                    BEGIN(ASM_BLOCK);
                    PARSER.string_literal.clear();
                  }
                  loc();
                  return yytext[0];
                }

";"             { PARSER.asm_block_following=false;
                  PARSER.tag_following=false;
                  loc();
                  return yytext[0];
                }

  /* This catches all one-character operators */
.               { loc(); PARSER.tag_following=false; return yytext[0]; }
}

<MSC_ANNOTATION>"]" { BEGIN(GRAMMAR); }
<MSC_ANNOTATION>. { /* ignore */ }

<MSC_ASM>{ws}"{" {
                  BEGIN(ASM_BLOCK);
                  PARSER.string_literal.clear();
                  loc();
                  return '{';
                }
<MSC_ASM>[^{^}^\n]* { loc();
                  source_locationt l=stack(yyansi_clval).source_location();
                  stack(yyansi_clval)=string_constantt(yytext);
                  stack(yyansi_clval).add_source_location()=l;
                  BEGIN(GRAMMAR);
                  return TOK_ASM_STRING;
                }

<ASM_BLOCK>{
{ws}            { /* ignore */ }
{newline}       { /* ignore */ }
[^#}\n][^\n}]*[\n] { PARSER.string_literal.append(yytext); }
[^#}\n][^\n}]*  { PARSER.string_literal.append(yytext); }
.               { // anything else: back to normal
                  PARSER.asm_block_following=false;
                  loc();
                  stack(yyansi_clval)=string_constantt(PARSER.string_literal);
                  BEGIN(GRAMMAR);
                  yyless(0); // put back
                  return TOK_ASM_STRING;
                }
}

<IGNORE_PARENS>")"    { PARSER.parenthesis_counter--;
                        if(PARSER.parenthesis_counter==0)
                          BEGIN(GRAMMAR); }
<IGNORE_PARENS>"("    { PARSER.parenthesis_counter++; }
<IGNORE_PARENS>.      { /* Throw away */ }

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
{cpplineno}     {
                  preprocessor_line(yytext, PARSER);
                  PARSER.set_line_no(PARSER.get_line_no()-1);
                }
{ws}            { /* ignore */ }
{newline}       { /* ignore */ }
"("             { BEGIN(GCC_ATTRIBUTE1a); return yytext[0]; }
.               { BEGIN(GRAMMAR); loc(); return yytext[0]; }
}

<GCC_ATTRIBUTE1a>{
{cpplineno}     {
                  preprocessor_line(yytext, PARSER);
                  PARSER.set_line_no(PARSER.get_line_no()-1);
                }
"("             { BEGIN(GCC_ATTRIBUTE2); PARSER.parenthesis_counter=0; return yytext[0]; }
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

"__gnu_inline__"    { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_GNU_INLINE; }

"weak" |
"__weak__"          { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_WEAK; }

"alias" |
"__alias__"          { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_ALIAS; }

"section" |
"__section__"       { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_SECTION; }

"noreturn" |
"__noreturn__"      { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_NORETURN; }

"constructor" |
"__constructor__"   { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_CONSTRUCTOR; }

"destructor" |
"__destructor__"   { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_DESTRUCTOR; }

"fallthrough"       { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_FALLTHROUGH; }

"used" |
"__used__"          { BEGIN(GCC_ATTRIBUTE3); loc(); return TOK_GCC_ATTRIBUTE_USED; }

{ws}                { /* ignore */ }
{newline}           { /* ignore */ }
{identifier}        { BEGIN(GCC_ATTRIBUTE4); }
")"                 { BEGIN(GCC_ATTRIBUTE5); return yytext[0]; }
.                   { /* ignore */ }
}

<GCC_ATTRIBUTE3>{ // an attribute we do process
{cpplineno}     {
                  preprocessor_line(yytext, PARSER);
                  PARSER.set_line_no(PARSER.get_line_no()-1);
                }
"("             { PARSER.parenthesis_counter++; loc(); return '('; }
")"             { if(PARSER.parenthesis_counter==0)
                  {
                    BEGIN(GCC_ATTRIBUTE5);
                    loc();
                    return yytext[0];
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
                    return yytext[0];
                  }
                  else
                  {
                    loc();
                    return ',';
                  }
                }
{integer_s}     { newstack(yyansi_clval);
                  stack(yyansi_clval)=convert_integer_literal(yytext);
                  PARSER.set_source_location(stack(yyansi_clval));
                  return TOK_INTEGER;
                }
{ws}            { /* ignore */ }
{newline}       { /* ignore */ }
{identifier}    { return make_identifier(); }
.               { loc(); return yytext[0]; }
}

<GCC_ATTRIBUTE4>{ // an attribute we just ignore
"("             { PARSER.parenthesis_counter++; }
")"             { if(PARSER.parenthesis_counter==0)
                  {
                    BEGIN(GCC_ATTRIBUTE5);
                    loc();
                    return yytext[0];
                  }
                  else
                    PARSER.parenthesis_counter--;
                }
","             { if(PARSER.parenthesis_counter==0)
                  {
                    BEGIN(GCC_ATTRIBUTE2);
                    loc();
                    return yytext[0];
                  }
                }
.               { /* Throw away */ }
}

<GCC_ATTRIBUTE5>{ // end bit: the closing parenthesis
{cpplineno}     {
                  preprocessor_line(yytext, PARSER);
                  PARSER.set_line_no(PARSER.get_line_no()-1);
                }
")"             { BEGIN(GRAMMAR); loc(); return yytext[0]; }
{ws}            { /* Throw away */ }
{newline}       { /* Throw away */ }
.               { BEGIN(GRAMMAR); loc(); return yytext[0]; }
}

<<EOF>>         { yyterminate(); /* done! */ }

%%

int yywrap() { return 1; }
