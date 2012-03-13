%option nounput

%{

/*************** Includes and Defines *****************************/

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
#include <ansi-c/literals/unescape_string.h>
#include <ansi-c/literals/convert_character_literal.h>
#include <ansi-c/literals/convert_string_literal.h>

#define PARSER cpp_parser
#define YYSTYPE unsigned
#undef  ECHO
#define ECHO

#include "cpp_parser.h"
#include "tokens.h"

void set_line_no();

%}

%x COMMENT1
%x COMMENT2
%x GCC_ATTRIBUTE
%x ASM_BLOCK
%x MSC_ASM
%x MSC_DECLSPEC
%x MSC_PRAGMA
%x MSC_ANNOTATION

%{
void cpp_scanner_init()
{
  YY_FLUSH_BUFFER;
  BEGIN(0); // this is INITIAL, hopefully
}
%}

identifier [a-zA-Z_$][0-9a-zA-Z_$]*

exponent_part [eE][-+]?[0-9]+
fractional_constant ([0-9]*"."[0-9]+)|([0-9]+".")
floating_constant (({fractional_constant}{exponent_part}?)|([0-9]+{exponent_part}))[FfLl]?

integer_suffix [uUlL]
iw_suffix       ("i8"|"i16"|"i32"|"i64"|"i128")
integer_suffix_opt {integer_suffix}*{iw_suffix}?
decimal_constant [1-9][0-9]*{integer_suffix_opt}
octal_constant "0"[0-7]*{integer_suffix_opt}
hex_constant "0"[xX][0-9a-fA-F]+{integer_suffix_opt}

simple_escape [abfnrtv'"?\\]
octal_escape  [0-7]{1,3}
hex_escape "x"[0-9a-fA-F]+

escape_sequence [\\]({simple_escape}|{octal_escape}|{hex_escape})
c_char [^'\\\n]|{escape_sequence}
s_char [^"\\\n]|{escape_sequence}

h_tab [\011]
form_feed [\014]
v_tab [\013]
c_return [\015]

horizontal_white [ ]|{h_tab}
ws {horizontal_white}*

integer         [0-9]+
cppfile         "\""[ !#-~]*"\""
cpplineno       "#"{horizontal_white}*"line"*{horizontal_white}*{integer}.*"\n"
pragma          "#"{horizontal_white}*pragma{horizontal_white}.*"\n"

%%

%{
#define loc() (PARSER.current_token().text=yytext,PARSER.set_location())
#define MSC_Keyword(x) (PARSER.mode==cpp_parsert::MSC?x:TOK_IDENTIFIER)
%}

<INITIAL>"/*"	{ BEGIN(COMMENT1); }	/* begin C comment state */

<COMMENT1>{
   "*/"		{ BEGIN(INITIAL); }	/* end comment state, back to INITIAL */
   "/*"		{ yycpperror("Probably nested comments"); }
   <<EOF>>	{ yycpperror("Unterminated comment"); }
   [^*/\n]*	{ /* ignore every char except '*' and NL (performance!) */ }
   .		{ } /* all single characters within comments are ignored */
   \n		{ } 
	}

<INITIAL>"//"	{ BEGIN(COMMENT2); }	/* begin C++ comment state */

<COMMENT2>{
   \n		{ BEGIN(INITIAL); }	/* end comment state, back to INITIAL */
   .*		{ } /* all characters within comments are ignored */
	}

<GCC_ATTRIBUTE>{
")"    { PARSER.parenthesis_counter--;
         if(PARSER.parenthesis_counter==0)
         BEGIN(INITIAL); }
"("    { PARSER.parenthesis_counter++; }
.      { /* Throw away */ }
}

"["{ws}"repeatable"   { BEGIN(MSC_ANNOTATION); }
"["{ws}"source_annotation_attribute" { BEGIN(MSC_ANNOTATION); }
"["{ws}"returnvalue"  { BEGIN(MSC_ANNOTATION); }
"["{ws}"SA_Pre"       { BEGIN(MSC_ANNOTATION); }
"["{ws}"SA_Post"      { BEGIN(MSC_ANNOTATION); }
"["{ws}"SA_FormatString" { BEGIN(MSC_ANNOTATION); }
"["{ws}"SA_Success"   { BEGIN(MSC_ANNOTATION); }
"["{ws}"uuid"         { BEGIN(MSC_ANNOTATION); }
"["{ws}"emitidl"      { BEGIN(MSC_ANNOTATION); }
"["{ws}"module"       { BEGIN(MSC_ANNOTATION); }
"["{ws}"export"       { BEGIN(MSC_ANNOTATION); }

"__pragma"      { BEGIN(MSC_PRAGMA); PARSER.parenthesis_counter=0; }

<MSC_ANNOTATION>"]" { BEGIN(INITIAL); }
<MSC_ANNOTATION>. { /* ignore */ }

<MSC_ASM>{ws}"{" { BEGIN(ASM_BLOCK); loc(); return '{'; }
<MSC_ASM>[^{^}^\n]* { loc();
                    PARSER.current_token().data=exprt(yytext);
                    BEGIN(INITIAL);
                    return TOK_STRING; }

<ASM_BLOCK>[^}]* { loc();
                  PARSER.current_token().data=exprt(yytext);
                  return TOK_STRING; }
<ASM_BLOCK>"}"  { PARSER.asm_block_following=false;
                  BEGIN(INITIAL); loc(); return '}'; }

<MSC_DECLSPEC>")"    { PARSER.parenthesis_counter--;
                        if(PARSER.parenthesis_counter==0)
                          BEGIN(INITIAL); }
<MSC_DECLSPEC>"("    { PARSER.parenthesis_counter++; }
<MSC_DECLSPEC>.      { /* Throw away */ }

<MSC_PRAGMA>")"    { PARSER.parenthesis_counter--;
                        if(PARSER.parenthesis_counter==0)
                          BEGIN(INITIAL); }
<MSC_PRAGMA>"("    { PARSER.parenthesis_counter++; }
<MSC_PRAGMA>.      { /* Throw away */ }

<INITIAL>{
{horizontal_white}+
({v_tab}|{c_return}|{form_feed})+
({horizontal_white}|{v_tab}|{c_return}|{form_feed})*"\n"

__alignof__         { loc(); return TOK_SIZEOF; }

"__asm"         { if(PARSER.mode==cpp_parsert::MSC)
                  {
                    loc();
                    BEGIN(MSC_ASM);
                    return TOK_MSC_ASM;
                  }
                  else
                  {
                    loc();
                    PARSER.asm_block_following=true;
                    return TOK_GCC_ASM;
                  }
                }

"asm"           { if(PARSER.mode==cpp_parsert::GCC ||
                     PARSER.mode==cpp_parsert::CW)
                  {
                    loc();
                    PARSER.asm_block_following=true;
                    return TOK_GCC_ASM;
                  }
                  else
                  {
                    loc();
                    return TOK_IDENTIFIER;
                  }
                }

"__asm__"       { if(PARSER.mode==cpp_parsert::GCC ||
                     PARSER.mode==cpp_parsert::CW ||
                     PARSER.mode==cpp_parsert::ARM)
                  {
                    loc();
                    PARSER.asm_block_following=true;
                    return TOK_GCC_ASM;
                  }
                  else
                  {
                    loc();
                    return TOK_IDENTIFIER;
                  }
                }

__attribute         { BEGIN(GCC_ATTRIBUTE); PARSER.parenthesis_counter=0; }
__attribute__       { BEGIN(GCC_ATTRIBUTE); PARSER.parenthesis_counter=0; }
_cdecl|__cdecl 	    { loc(); return MSC_Keyword(TOK_CDECL); }
__const             { loc(); return TOK_CONST; }
_declspec|__declspec { BEGIN(MSC_DECLSPEC); PARSER.parenthesis_counter=0; }
__extension__       { /* ignore */ }
__if_exists         { loc(); return MSC_Keyword(TOK_MSC_IF_EXISTS); }
__if_not_exists     { loc(); return MSC_Keyword(TOK_MSC_IF_NOT_EXISTS); }
_inline             { loc(); return TOK_INLINE; }
__inline            { loc(); return TOK_INLINE; }
__inline__          { loc(); return TOK_INLINE; }
__interface         { loc(); return MSC_Keyword(TOK_INTERFACE); }
__forceinline       { loc(); return MSC_Keyword(TOK_INLINE); }
__noreturn__        { /* ignore */ }
restrict            { /* ignore */ }
__restrict__        { /* ignroe */ }
__restrict          { /* ignore */ }
__stdcall           { loc(); return MSC_Keyword(TOK_STDCALL); }
__fastcall          { loc(); return MSC_Keyword(TOK_FASTCALL); }
__clrcall           { loc(); return MSC_Keyword(TOK_CLRCALL); }
__signed            { loc(); return TOK_SIGNED; }
__signed__          { loc(); return TOK_SIGNED; }
__vector            { /* ignore */ }
__volatile__        { loc(); return TOK_VOLATILE; }
typeof              { loc(); return TOK_TYPEOF; }
__typeof            { loc(); return TOK_TYPEOF; }
__typeof__          { loc(); return TOK_TYPEOF; }
__int8              { loc(); return MSC_Keyword(TOK_INT8); }
__int16             { loc(); return MSC_Keyword(TOK_INT16); }
__int32             { loc(); return MSC_Keyword(TOK_INT32); }
__int64             { loc(); return MSC_Keyword(TOK_INT64); }
__ptr32             { loc(); return MSC_Keyword(TOK_PTR32); }
__ptr64             { loc(); return MSC_Keyword(TOK_PTR64); }
__thiscall          { /* ignore */ }
__w64               { /* ignore */ }
_Complex            { loc(); return TOK_COMPLEX; }
__complex__         { loc(); return TOK_COMPLEX; }
__real__            { loc(); return TOK_REAL; }
__imag__            { loc(); return TOK_IMAG; }
__try               { loc(); return MSC_Keyword(TOK_MSC_TRY); }
__except            { loc(); return MSC_Keyword(TOK_MSC_EXCEPT); }
__leave             { loc(); return MSC_Keyword(TOK_MSC_LEAVE); }
__finally           { loc(); return MSC_Keyword(TOK_MSC_FINALLY); }
__uuidof 	    { loc(); return MSC_Keyword(TOK_MSC_UUIDOF); }
auto                { loc(); return TOK_AUTO; }
bool                { loc(); return TOK_BOOL; }
break               { loc(); return TOK_BREAK; }
case                { loc(); return TOK_CASE; }
catch               { loc(); return TOK_CATCH; }
char                { loc(); return TOK_CHAR; }
class               { loc(); return TOK_CLASS; }
const               { loc(); return TOK_CONST; }
continue            { loc(); return TOK_CONTINUE; }
default             { loc(); return TOK_DEFAULT; }
delete              { loc(); return TOK_DELETE; }
decltype            { loc(); return TOK_DECLTYPE; } // C++11
do                  { loc(); return TOK_DO; }
double              { loc(); return TOK_DOUBLE; }
else                { loc(); return TOK_ELSE; }
enum                { loc(); return TOK_ENUM; }
explicit            { loc(); return TOK_EXPLICIT; }
extern              { loc(); return TOK_EXTERN; }
float               { loc(); return TOK_FLOAT; }
for                 { loc(); return TOK_FOR; }
friend              { loc(); return TOK_FRIEND; }
goto                { loc(); return TOK_GOTO; }
if                  { loc(); return TOK_IF; }
inline              { loc(); return TOK_INLINE; }
int                 { loc(); return TOK_INT; }
long                { loc(); return TOK_LONG; }
mutable             { loc(); return TOK_MUTABLE; }
namespace           { loc(); return TOK_NAMESPACE; }
new                 { loc(); return TOK_NEW; }
noreturn            { /* ignore */ }
nullptr             { loc(); return TOK_NULLPTR; } // C++11
operator            { loc(); return TOK_OPERATOR; }
private             { loc(); return TOK_PRIVATE; }
protected           { loc(); return TOK_PROTECTED; }
public              { loc(); return TOK_PUBLIC; }
register            { loc(); return TOK_REGISTER; }
return              { loc(); return TOK_RETURN; }
short               { loc(); return TOK_SHORT; }
signed              { loc(); return TOK_SIGNED; }
sizeof              { loc(); return TOK_SIZEOF; }
static              { loc(); return TOK_STATIC; }
static_assert       { loc(); return TOK_STATIC_ASSERT; } // C++11
struct              { loc(); return TOK_STRUCT; }
switch              { loc(); return TOK_SWITCH; }
template            { loc(); return TOK_TEMPLATE; }
this                { loc(); return TOK_THIS; }
thread_local        { loc(); return TOK_THREAD_LOCAL; } // C++11
throw               { loc(); return TOK_THROW; }
try                 { loc(); return TOK_TRY; }
typedef             { loc(); return TOK_TYPEDEF; }
typeid              { loc(); return TOK_TYPEID; }
typename            { loc(); return TOK_TYPENAME; }
union               { loc(); return TOK_UNION; }
unsigned            { loc(); return TOK_UNSIGNED; }
using               { loc(); return TOK_USING; }
virtual             { loc(); return TOK_VIRTUAL; }
void                { loc(); return TOK_VOID; }
volatile            { loc(); return TOK_VOLATILE; }
wchar_t	            { // CodeWarrior doesn't have wchar_t built in
                      loc();
                      if(PARSER.mode==cpp_parsert::CW)
                        return TOK_IDENTIFIER;
                      else
                        return TOK_WCHAR_T;
                    }
while               { loc(); return TOK_WHILE; }
__CPROVER_thread_local { loc(); return TOK_THREAD_LOCAL; }

%{
/* a huge batch of MS extensions
   http://msdn.microsoft.com/en-us/library/ms177194(v=vs.80).aspx */
%}

"__has_assign"      { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_copy"        { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_finalizer"   { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_nothrow_assign" { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_nothrow_constructor" { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_nothrow_copy" { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_trivial_assign" { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_trivial_constructor" { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_trivial_copy" { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_trivial_destructor" { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_user_destructor" { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_virtual_destructor" { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_abstract"     { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_base_of"      { loc(); return MSC_Keyword(TOK_MSC_BINARY_TYPE_PREDICATE); }
"__is_class"        { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_convertible_to" { loc(); return MSC_Keyword(TOK_MSC_BINARY_TYPE_PREDICATE); }
"__is_delegate"     { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_empty"        { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_enum"         { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_interface_class" { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_pod"          { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_polymorphic"  { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_ref_array"    { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_ref_class"    { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_sealed"       { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_simple_value_class" { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_union"        { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_value_class"  { loc(); return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }

{identifier}        { loc();
                      return TOK_IDENTIFIER; // or TYPDEFname
                    }

{decimal_constant}  { loc();
                      PARSER.current_token().data=convert_integer_literal(yytext, 10);
                      return TOK_INTEGER;
                    }

{octal_constant}    { loc();
                      PARSER.current_token().data=convert_integer_literal(yytext, 8);
                      return TOK_INTEGER;
                    }

{hex_constant}      { loc();
                      PARSER.current_token().data=convert_integer_literal(yytext, 16);
                      return TOK_INTEGER;
                    }

{floating_constant} {
                      loc();
                      PARSER.current_token().data=convert_float_literal(yytext);
                      return TOK_FLOATING;
                    }

"L"?[']{c_char}+['] { 
                      loc();
                      PARSER.current_token().data=convert_character_literal(yytext, false);
                      return TOK_CHARACTER;
                    }

"L"?["]{s_char}*["] {
                      loc();
                      PARSER.current_token().data=convert_string_literal(yytext);
                      return TOK_STRING;
                    }

"("                 { loc(); return yytext[0]; }
")"                 { loc(); return yytext[0]; }
","                 { loc(); return yytext[0]; }

{cpplineno}         { set_line_no(); }
{pragma}            { /* ignore it */ }

"#"

"#".*"\n"           { yycpperror("unknown preprocessor directive"); }

"##"                { }

"}"                 { loc(); return '}'; }
"["                 { loc(); return '['; }
"]"                 { loc(); return ']'; }
"."                 { loc(); return '.'; }
"&"                 { loc(); return '&'; }
"*"                 { loc(); return '*'; }
"+"                 { loc(); return '+'; }
"-"                 { loc(); return '-'; }
"~"                 { loc(); return '~'; }
"!"                 { loc(); return '!'; }
"/"                 { loc(); return '/'; }
"%"                 { loc(); return '%'; }
"<"                 { loc(); return '<'; }
">"                 { loc(); return '>'; }
"^"                 { loc(); return '^'; }
"|"                 { loc(); return '|'; }
"?"                 { loc(); return '?'; }
":"                 { loc(); return ':'; }
"="                 { loc(); return '='; }

"{"                 { 
                      if(PARSER.asm_block_following) { BEGIN(ASM_BLOCK); }
                      loc();
                      return '{';
                    }

";"                 { PARSER.asm_block_following=false;
                      loc();
                      return ';';
                    }

".*"                { loc(); return TOK_DOTPM; }
"->*"               { loc(); return TOK_ARROWPM; }
"::"                { loc(); return TOK_SCOPE; }
"->"                { loc(); return TOK_ARROW; }
"++"                { loc(); return TOK_INCR; }
"--"                { loc(); return TOK_DECR; }
"<<"                { loc(); return TOK_SHIFTLEFT; }
">>"                { loc(); return TOK_SHIFTRIGHT; }
"<="                { loc(); return TOK_LE; }
">="                { loc(); return TOK_GE; }
"=="                { loc(); return TOK_EQ; }
"!="                { loc(); return TOK_NE; }
"&&"                { loc(); return TOK_ANDAND; }
"||"                { loc(); return TOK_OROR; }
"*="                { loc(); return TOK_MULTASSIGN; }
"/="                { loc(); return TOK_DIVASSIGN; }
"%="                { loc(); return TOK_MODASSIGN; }
"+="                { loc(); return TOK_PLUSASSIGN; }
"-="                { loc(); return TOK_MINUSASSIGN; }
"<<="               { loc(); return TOK_SHLASSIGN; }
">>="               { loc(); return TOK_SHRASSIGN; }
"&="                { loc(); return TOK_ANDASSIGN; }
"^="                { loc(); return TOK_XORASSIGN; }
"|="                { loc(); return TOK_ORASSIGN; }
"..."               { loc(); return TOK_ELLIPSIS; }

.                   { yycpperror("unknown character"); }
}

%%

int yywrap() { return 1; }

void set_line_no()
{
  preprocessor_line(yytext, PARSER.line_no, PARSER.filename);
}
