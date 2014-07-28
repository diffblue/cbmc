%option nounput
%option noinput

%{

/*************** Includes and Defines *****************************/

#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

#include <util/expr.h>
#include <util/arith_tools.h>
#include <util/config.h>

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
int yycpperror(const std::string &error);

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

#define loc() (PARSER.current_token().text=yytext,PARSER.set_location())

static inline int make_identifier()
{
  loc();
  irep_idt base_name=yytext;
  PARSER.current_token().data.id(ID_symbol);
  PARSER.current_token().data.set(ID_C_base_name, base_name);
  return TOK_IDENTIFIER;
}

static inline int token(int x)
{
  loc();
  return x;
}

static inline int MSC_Keyword(int x)
{
  if(PARSER.mode==cpp_parsert::MSC)
    return token(x);
  else
    return make_identifier();
}

%}

identifier [a-zA-Z_$][0-9a-zA-Z_$]*


digit		[0-9]
bindigit	[01]
octdigit	[0-7]
hexdigit	[0-9a-fA-F]
integer		{digit}+
exponent	[eE][+-]?{integer}
fraction	{integer}

float1		{integer}"."{fraction}?({exponent})?
float2		"."{fraction}({exponent})?
float3		{integer}{exponent}
hexfloat1       "0"[xX]{hexdigit}+"."{hexdigit}+[pP][+-]?{integer}
hexfloat2       "0"[xX]{hexdigit}+"."[pP][+-]?{integer}
hexfloat3       "0"[xX]{hexdigit}+[pP][+-]?{integer}
float		{float1}|{float2}|{float3}|{hexfloat1}|{hexfloat2}|{hexfloat3}
float_f		{float}[fF]|{integer}[fF]
float_l		{float}[lL]

floating_constant {float}|{float_f}|{float_l}

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

char_lit    "L"?[']{c_char}+[']
string_lit  "L"?["]{s_char}*["]

h_tab [\011]
form_feed [\014]
v_tab [\013]
c_return [\015]

horizontal_white [ ]|{h_tab}
ws {horizontal_white}*
newline         [\n\f\v]|"\\\n"
ws_or_newline ({horizontal_white}|{newline})*

cppfile         "\""[ !#-~]*"\""
cpplineno       "#"{horizontal_white}*"line"*{horizontal_white}*{integer}.*"\n"
pragma          "#"{horizontal_white}*pragma{horizontal_white}.*"\n"

%%

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

<MSC_ASM>{ws}"{" { BEGIN(ASM_BLOCK); return token('{'); }
<MSC_ASM>[^{^}^\n]* { loc();
                    PARSER.current_token().data=exprt(yytext);
                    BEGIN(INITIAL);
                    return TOK_ASM_STRING; }

<ASM_BLOCK>[^}]* { loc();
                  PARSER.current_token().data=exprt(yytext);
                  return TOK_ASM_STRING; }
<ASM_BLOCK>"}"  { PARSER.asm_block_following=false;
                  BEGIN(INITIAL); return token('}'); }

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

__alignof__         { return token(TOK_ALIGNOF); }

"__asm"         { if(PARSER.mode==cpp_parsert::MSC)
                  {
                    BEGIN(MSC_ASM);
                    return token(TOK_MSC_ASM);
                  }
                  else
                  {
                    PARSER.asm_block_following=true;
                    return token(TOK_GCC_ASM);
                  }
                }

"asm"           { if(PARSER.mode==cpp_parsert::GCC ||
                     PARSER.mode==cpp_parsert::CW)
                  {
                    PARSER.asm_block_following=true;
                    return token(TOK_GCC_ASM);
                  }
                  else
                    return make_identifier();
                }

"__asm__"       { if(PARSER.mode==cpp_parsert::GCC ||
                     PARSER.mode==cpp_parsert::CW ||
                     PARSER.mode==cpp_parsert::ARM)
                  {
                    PARSER.asm_block_following=true;
                    return token(TOK_GCC_ASM);
                  }
                  else
                    return make_identifier();
                }

__attribute         { BEGIN(GCC_ATTRIBUTE); PARSER.parenthesis_counter=0; }
__attribute__       { BEGIN(GCC_ATTRIBUTE); PARSER.parenthesis_counter=0; }
_cdecl|__cdecl 	    { return MSC_Keyword(TOK_CDECL); }
__const             { return token(TOK_CONST); }
_declspec|__declspec { BEGIN(MSC_DECLSPEC); PARSER.parenthesis_counter=0; }
__extension__       { /* ignore */ }
__if_exists         { return MSC_Keyword(TOK_MSC_IF_EXISTS); }
__if_not_exists     { return MSC_Keyword(TOK_MSC_IF_NOT_EXISTS); }
_inline             { return token(TOK_INLINE); }
__inline            { return token(TOK_INLINE); }
__inline__          { return token(TOK_INLINE); }
__interface         { return MSC_Keyword(TOK_INTERFACE); }
__forceinline       { return MSC_Keyword(TOK_INLINE); }
__noreturn__        { /* ignore */ }
restrict            { /* ignore */ }
__restrict__        { /* ignroe */ }
__restrict          { /* ignore */ }
__stdcall           { return MSC_Keyword(TOK_STDCALL); }
__fastcall          { return MSC_Keyword(TOK_FASTCALL); }
__clrcall           { return MSC_Keyword(TOK_CLRCALL); }
__signed            { return token(TOK_SIGNED); }
__signed__          { return token(TOK_SIGNED); }
__vector            { /* ignore */ }
__volatile__        { return token(TOK_VOLATILE); }
alignof             { return token(TOK_ALIGNOF); }
typeof              { return token(TOK_TYPEOF); }
__typeof            { return token(TOK_TYPEOF); }
__typeof__          { return token(TOK_TYPEOF); }
__int8              { return MSC_Keyword(TOK_INT8); }
__int16             { return MSC_Keyword(TOK_INT16); }
__int32             { return MSC_Keyword(TOK_INT32); }
__int64             { return MSC_Keyword(TOK_INT64); }
__ptr32             { return MSC_Keyword(TOK_PTR32); }
__ptr64             { return MSC_Keyword(TOK_PTR64); }
__thiscall          { /* ignore */ }
__w64               { /* ignore */ }
_Complex            { return token(TOK_COMPLEX); }
__complex__         { return token(TOK_COMPLEX); }
__real__            { return token(TOK_REAL); }
__imag__            { return token(TOK_IMAG); }
__try               { return MSC_Keyword(TOK_MSC_TRY); }
__except            { return MSC_Keyword(TOK_MSC_EXCEPT); }
__leave             { return MSC_Keyword(TOK_MSC_LEAVE); }
__finally           { return MSC_Keyword(TOK_MSC_FINALLY); }
__uuidof 	    { return MSC_Keyword(TOK_MSC_UUIDOF); }
auto                { return token(TOK_AUTO); }
bool                { return token(TOK_BOOL); }
break               { return token(TOK_BREAK); }
case                { return token(TOK_CASE); }
catch               { return token(TOK_CATCH); }
char                { return token(TOK_CHAR); }
class               { return token(TOK_CLASS); }
const               { return token(TOK_CONST); }
continue            { return token(TOK_CONTINUE); }
default             { return token(TOK_DEFAULT); }
delete              { return token(TOK_DELETE); }
decltype            { return token(TOK_DECLTYPE); } // C++11
__decltype          { return token(TOK_DECLTYPE); } // gcc
do                  { return token(TOK_DO); }
double              { return token(TOK_DOUBLE); }
else                { return token(TOK_ELSE); }
enum                { return token(TOK_ENUM); }
explicit            { return token(TOK_EXPLICIT); }
extern              { return token(TOK_EXTERN); }
float               { return token(TOK_FLOAT); }
for                 { return token(TOK_FOR); }
friend              { return token(TOK_FRIEND); }
goto                { return token(TOK_GOTO); }
if                  { return token(TOK_IF); }
inline              { return token(TOK_INLINE); }
int                 { return token(TOK_INT); }
long                { return token(TOK_LONG); }
mutable             { return token(TOK_MUTABLE); }
namespace           { return token(TOK_NAMESPACE); }
new                 { return token(TOK_NEW); }
noreturn            { /* ignore */ }
operator            { return token(TOK_OPERATOR); }
private             { return token(TOK_PRIVATE); }
protected           { return token(TOK_PROTECTED); }
public              { return token(TOK_PUBLIC); }
register            { return token(TOK_REGISTER); }
return              { return token(TOK_RETURN); }
short               { return token(TOK_SHORT); }
signed              { return token(TOK_SIGNED); }
sizeof              { return token(TOK_SIZEOF); }
static              { return token(TOK_STATIC); }
static_assert       { return token(TOK_STATIC_ASSERT); } // C++11
struct              { return token(TOK_STRUCT); }
switch              { return token(TOK_SWITCH); }
template            { return token(TOK_TEMPLATE); }
this                { return token(TOK_THIS); }
thread_local        { return token(TOK_THREAD_LOCAL); } // C++11
throw               { return token(TOK_THROW); }
try                 { return token(TOK_TRY); }
typedef             { return token(TOK_TYPEDEF); }
typeid              { return token(TOK_TYPEID); }
typename            { return token(TOK_TYPENAME); }
union               { return token(TOK_UNION); }
unsigned            { return token(TOK_UNSIGNED); }
using               { return token(TOK_USING); }
virtual             { return token(TOK_VIRTUAL); }
void                { return token(TOK_VOID); }
volatile            { return token(TOK_VOLATILE); }
wchar_t	            { // CodeWarrior has an option to
                      // enable/disable wchar_t
                      if(PARSER.mode==cpp_parsert::CW &&
                         !PARSER.recognize_wchar_t)
                        return make_identifier();
                      else
                        return token(TOK_WCHAR_T);
                    }
__float128	    {
                      if(PARSER.mode==cpp_parsert::GCC)
                        return token(TOK_GCC_FLOAT128);
                      else
                        return make_identifier();
                    }
__int128	    {
                      if(PARSER.mode==cpp_parsert::GCC)
                        return token(TOK_GCC_INT128);
                      else
                        return make_identifier();
                    }
while               { return token(TOK_WHILE); }
__CPROVER_thread_local { return token(TOK_THREAD_LOCAL); }
__CPROVER_bool      { return token(TOK_CPROVER_BOOL); }

%{
/* a huge batch of MS extensions
   http://msdn.microsoft.com/en-us/library/ms177194(v=vs.80).aspx */
%}

"__has_assign"      { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_copy"        { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_finalizer"   { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_nothrow_assign" { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_nothrow_constructor" { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_nothrow_copy" { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_trivial_assign" { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_trivial_constructor" { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_trivial_copy" { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_trivial_destructor" { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_user_destructor" { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__has_virtual_destructor" { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_abstract"     { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_base_of"      { return MSC_Keyword(TOK_MSC_BINARY_TYPE_PREDICATE); }
"__is_class"        { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_convertible_to" { return MSC_Keyword(TOK_MSC_BINARY_TYPE_PREDICATE); }
"__is_delegate"     { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_empty"        { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_enum"         { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_interface_class" { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_pod"          { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_polymorphic"  { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_ref_array"    { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_ref_class"    { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_sealed"       { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_simple_value_class" { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_union"        { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }
"__is_value_class"  { return MSC_Keyword(TOK_MSC_UNARY_TYPE_PREDICATE); }

"and"               { return token(TOK_ANDAND); }
"bitand"            { return token('&'); }
"and_eq"            { return token(TOK_ANDASSIGN); }
"or"                { return token(TOK_OROR); }
"bitor"             { return token('|'); }
"or_eq"             { return token(TOK_ORASSIGN); }
"xor"               { return token('^'); }
"xor_eq"            { return token(TOK_XORASSIGN); }
"not"               { return token('!'); }
"not_eq"            { return token(TOK_NE); }
"compl"             { return token('~'); }

{identifier}        { return make_identifier(); }

{decimal_constant}  { loc();
                      PARSER.current_token().data=convert_integer_literal(yytext);
                      return TOK_INTEGER;
                    }

{octal_constant}    { loc();
                      PARSER.current_token().data=convert_integer_literal(yytext);
                      return TOK_INTEGER;
                    }

{hex_constant}      { loc();
                      PARSER.current_token().data=convert_integer_literal(yytext);
                      return TOK_INTEGER;
                    }

{floating_constant} { loc();
                      PARSER.current_token().data=convert_float_literal(yytext);
                      return TOK_FLOATING;
                    }

{char_lit}          { loc();
                      PARSER.current_token().data=convert_character_literal(yytext, false);
                      return TOK_CHARACTER;
                    }

({string_lit}{ws_or_newline})+ {
                      loc();
                      PARSER.current_token().data=convert_string_literal(yytext);
                      return TOK_STRING;
                    }

{cpplineno}         { set_line_no(); }
{pragma}            { /* ignore it */ }

"#"

"#".*"\n"           { yycpperror("unknown preprocessor directive"); }

"##"                { }

"{"                 { if(PARSER.asm_block_following) { BEGIN(ASM_BLOCK); }
                      return token('{');
                    }

";"                 { PARSER.asm_block_following=false;
                      return token(';');
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

.                   { return token(yytext[0]); }
}

%%

int yywrap() { return 1; }

void set_line_no()
{
  preprocessor_line(yytext, PARSER);
}

int yycpperror(const std::string &error)
{
  cpp_parser.parse_error(error, yycpptext);
  return error.size()+1;
}
