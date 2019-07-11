%{
/*
Copied and modified from the Rust Github:
https://github.com/rust-lang/rust

Copyright:
The Rust Project is dual-licensed under Apache 2.0 and MIT
terms.
*/

#include <stdio.h>
#include <ctype.h>
#include <iostream>
#include "rust_y.tab.h"
using namespace yyrust;

// Make sure this matches the #define for YY_DECL in parser.y
#define YY_DECL    int yyFlexLexer::yylex()
// Old definition from c somewhere: #define YY_DECL    int yylex(YYSTYPE *yylval)

yyFlexLexer defaultScanner;
yyFlexLexer* currentScanner = &defaultScanner;
char const* yyrusttext = nullptr;

std::vector<yyFlexLexer*> pastScanners;

int yyrustlex(unsigned int*)
{
  int result = currentScanner->yylex();
  yyrusttext = currentScanner->YYText();
  return result;
}

void UseDifferentScanner(yyFlexLexer* newScanner, std::istream& newInStream)
{
  pastScanners.push_back(currentScanner);
  currentScanner = newScanner;

  yy_buffer_state* newBuffer = currentScanner->yy_create_buffer(&newInStream, YY_BUF_SIZE);
  currentScanner->yy_switch_to_buffer(newBuffer);
}

void PopToPreviousScanner()
{
  currentScanner = pastScanners.back();
  pastScanners.pop_back();
}

#define PARSER rust_parser
#include "rust_parser.h"

extern int rustdebug;

#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

static int num_hashes;
static int end_hashes;
static int saw_non_hash;

#include <util/pragma_wsign_compare.def>
#include <util/pragma_wdeprecated_register.def>
#include <util/pragma_wnull_conversion.def>
%}

%option c++
%option stack
%option yylineno
%option noyywrap
%option nounput
%option noinput
%option never-interactive

%x str
%x rawstr
%x rawstr_esc_begin
%x rawstr_esc_body
%x rawstr_esc_end
%x byte
%x bytestr
%x rawbytestr
%x rawbytestr_nohash
%x pound
%x shebang_or_attr
%x ltorchar
%x linecomment
%x doc_line
%x blockcomment
%x doc_block
%x suffix

ident [a-zA-Z\x80-\xff_][a-zA-Z0-9\x80-\xff_]*

%%

<suffix>{ident}            { BEGIN(INITIAL); }
<suffix>(.|\n)  { yyless(0); BEGIN(INITIAL); }

[ \n\t\r]             { }

\xef\xbb\xbf {
  // UTF-8 byte order mark (BOM), ignore if in line 1, error otherwise
  if (yylineno/*()*/ != 1) {
    return -1;
  }
}

\/\/(\/|\!)           { BEGIN(doc_line); yymore(); }
<doc_line>\n          { BEGIN(INITIAL);
                        yyleng--;
                        yytext[yyleng] = 0;
                        return ((yytext[2] == '!') ? parser::token::yytokentype::INNER_DOC_COMMENT : parser::token::yytokentype::OUTER_DOC_COMMENT);
                      }
<doc_line>[^\n]*      { yymore(); }

\/\/|\/\/\/\/         { BEGIN(linecomment); }
<linecomment>\n       { BEGIN(INITIAL); }
<linecomment>[^\n]*   { }

\/\*(\*|\!)[^*]       { yy_push_state(INITIAL); yy_push_state(doc_block); yymore(); }
<doc_block>\/\*       { yy_push_state(doc_block); yymore(); }
<doc_block>\*\/       {
    yy_pop_state();
    if (yy_top_state() == doc_block) {
        yymore();
    } else {
        return ((yytext[2] == '!') ? parser::token::yytokentype::INNER_DOC_COMMENT : parser::token::yytokentype::OUTER_DOC_COMMENT);
    }
}
<doc_block>(.|\n)     { yymore(); }

\/\*                  { yy_push_state(blockcomment); }
<blockcomment>\/\*    { yy_push_state(blockcomment); }
<blockcomment>\*\/    { yy_pop_state(); }
<blockcomment>(.|\n)   { }

_        { return parser::token::yytokentype::UNDERSCORE; }
abstract { return parser::token::yytokentype::ABSTRACT; }
alignof  { return parser::token::yytokentype::ALIGNOF; }
as       { return parser::token::yytokentype::AS; }
become   { return parser::token::yytokentype::BECOME; }
box      { return parser::token::yytokentype::BOX; }
break    { return parser::token::yytokentype::BREAK; }
catch    { return parser::token::yytokentype::CATCH; }
const    { return parser::token::yytokentype::CONST; }
continue { return parser::token::yytokentype::CONTINUE; }
crate    { return parser::token::yytokentype::CRATE; }
default  { return parser::token::yytokentype::DEFAULT; }
do       { return parser::token::yytokentype::DO; }
else     { return parser::token::yytokentype::ELSE; }
enum     { return parser::token::yytokentype::ENUM; }
extern   { return parser::token::yytokentype::EXTERN; }
false    { return parser::token::yytokentype::FALSE; }
final    { return parser::token::yytokentype::FINAL; }
fn       { return parser::token::yytokentype::FN; }
for      { return parser::token::yytokentype::FOR; }
if       { return parser::token::yytokentype::IF; }
impl     { return parser::token::yytokentype::IMPL; }
in       { return parser::token::yytokentype::IN; }
let      { return parser::token::yytokentype::LET; }
loop     { return parser::token::yytokentype::LOOP; }
macro    { return parser::token::yytokentype::MACRO; }
match    { return parser::token::yytokentype::MATCH; }
mod      { return parser::token::yytokentype::MOD; }
move     { return parser::token::yytokentype::MOVE; }
mut      { return parser::token::yytokentype::MUT; }
offsetof { return parser::token::yytokentype::OFFSETOF; }
override { return parser::token::yytokentype::OVERRIDE; }
priv     { return parser::token::yytokentype::PRIV; }
proc     { return parser::token::yytokentype::PROC; }
pure     { return parser::token::yytokentype::PURE; }
pub      { return parser::token::yytokentype::PUB; }
ref      { return parser::token::yytokentype::REF; }
return   { return parser::token::yytokentype::RETURN; }
self     { return parser::token::yytokentype::SELF; }
sizeof   { return parser::token::yytokentype::SIZEOF; }
static   { return parser::token::yytokentype::STATIC; }
struct   { return parser::token::yytokentype::STRUCT; }
super    { return parser::token::yytokentype::SUPER; }
trait    { return parser::token::yytokentype::TRAIT; }
true     { return parser::token::yytokentype::TRUE; }
type     { return parser::token::yytokentype::TYPE; }
typeof   { return parser::token::yytokentype::TYPEOF; }
union    { return parser::token::yytokentype::UNION; }
unsafe   { return parser::token::yytokentype::UNSAFE; }
unsized  { return parser::token::yytokentype::UNSIZED; }
use      { return parser::token::yytokentype::USE; }
virtual  { return parser::token::yytokentype::VIRTUAL; }
where    { return parser::token::yytokentype::WHERE; }
while    { return parser::token::yytokentype::WHILE; }
yield    { return parser::token::yytokentype::YIELD; }

{ident}  { return parser::token::yytokentype::IDENT; }

0x[0-9a-fA-F_]+                                    { BEGIN(suffix); return parser::token::yytokentype::LIT_INTEGER; }
0o[0-7_]+                                          { BEGIN(suffix); return parser::token::yytokentype::LIT_INTEGER; }
0b[01_]+                                           { BEGIN(suffix); return parser::token::yytokentype::LIT_INTEGER; }
[0-9][0-9_]*                                       { BEGIN(suffix); return parser::token::yytokentype::LIT_INTEGER; }
[0-9][0-9_]*\.(\.|[a-zA-Z])    { yyless(yyleng - 2); BEGIN(suffix); return parser::token::yytokentype::LIT_INTEGER; }

[0-9][0-9_]*\.[0-9_]*([eE][-\+]?[0-9_]+)?          { BEGIN(suffix); return parser::token::yytokentype::LIT_FLOAT; }
[0-9][0-9_]*(\.[0-9_]*)?[eE][-\+]?[0-9_]+          { BEGIN(suffix); return parser::token::yytokentype::LIT_FLOAT; }

;      { return ';'; }
,      { return ','; }
\.\.\. { return parser::token::yytokentype::DOTDOTDOT; }
\.\.   { return parser::token::yytokentype::DOTDOT; }
\.     { return '.'; }
\(     { return '('; }
\)     { return ')'; }
\{     { return '{'; }
\}     { return '}'; }
\[     { return '['; }
\]     { return ']'; }
@      { return '@'; }
#      { BEGIN(pound); yymore(); }
<pound>\! { BEGIN(shebang_or_attr); yymore(); }
<shebang_or_attr>\[ {
  BEGIN(INITIAL);
  yyless(2);
  return parser::token::yytokentype::SHEBANG;
}
<shebang_or_attr>[^\[\n]*\n {
  // Since the \n was eaten as part of the token, yylineno will have
  // been incremented to the value 2 if the shebang was on the first
  // line. This yyless undoes that, setting yylineno back to 1.
  yyless(yyleng - 1);
  if (yylineno/*()*/ == 1) {
    BEGIN(INITIAL);
    return parser::token::yytokentype::SHEBANG_LINE;
  } else {
    BEGIN(INITIAL);
    yyless(2);
    return parser::token::yytokentype::SHEBANG;
  }
}
<pound>. { BEGIN(INITIAL); yyless(1); return '#'; }

\~     { return '~'; }
::     { return parser::token::yytokentype::MOD_SEP; }
:      { return ':'; }
\$     { return '$'; }
\?     { return '?'; }

==    { return parser::token::yytokentype::EQEQ; }
=>    { return parser::token::yytokentype::FAT_ARROW; }
=     { return '='; }
\!=   { return parser::token::yytokentype::NE; }
\!    { return '!'; }
\<=   { return parser::token::yytokentype::LE; }
\<\<  { return parser::token::yytokentype::SHL; }
\<\<= { return parser::token::yytokentype::SHLEQ; }
\<    { return '<'; }
\>=   { return parser::token::yytokentype::GE; }
\>\>  { return parser::token::yytokentype::SHR; }
\>\>= { return parser::token::yytokentype::SHREQ; }
\>    { return '>'; }

\x27                                      { BEGIN(ltorchar); yymore(); }
<ltorchar>static                          { BEGIN(INITIAL); return parser::token::yytokentype::STATIC_LIFETIME; }
<ltorchar>{ident}                         { BEGIN(INITIAL); return parser::token::yytokentype::LIFETIME; }
<ltorchar>\\[nrt\\\x27\x220]\x27          { BEGIN(suffix); return parser::token::yytokentype::LIT_CHAR; }
<ltorchar>\\x[0-9a-fA-F]{2}\x27           { BEGIN(suffix); return parser::token::yytokentype::LIT_CHAR; }
<ltorchar>\\u\{([0-9a-fA-F]_*){1,6}\}\x27 { BEGIN(suffix); return parser::token::yytokentype::LIT_CHAR; }
<ltorchar>.\x27                           { BEGIN(suffix); return parser::token::yytokentype::LIT_CHAR; }
<ltorchar>[\x80-\xff]{2,4}\x27            { BEGIN(suffix); return parser::token::yytokentype::LIT_CHAR; }
<ltorchar><<EOF>>                         { BEGIN(INITIAL); return -1; }

b\x22              { BEGIN(bytestr); yymore(); }
<bytestr>\x22      { BEGIN(suffix); return parser::token::yytokentype::LIT_BYTE_STR; }

<bytestr><<EOF>>                     { return -1; }
<bytestr>\\[n\nrt\\\x27\x220]        { yymore(); }
<bytestr>\\x[0-9a-fA-F]{2}           { yymore(); }
<bytestr>\\u\{([0-9a-fA-F]_*){1,6}\} { yymore(); }
<bytestr>\\[^n\nrt\\\x27\x220]       { return -1; }
<bytestr>(.|\n)                      { yymore(); }

br\x22                      { BEGIN(rawbytestr_nohash); yymore(); }
<rawbytestr_nohash>\x22     { std::cout << "YYText [" <<yytext << "]" << std::endl; BEGIN(suffix); return parser::token::yytokentype::LIT_BYTE_STR_RAW; }
<rawbytestr_nohash>(.|\n)   { yymore(); }
<rawbytestr_nohash><<EOF>>  { return -1; }

br/# {
    BEGIN(rawbytestr);
    yymore();
    num_hashes = 0;
    saw_non_hash = 0;
    end_hashes = 0;
}
<rawbytestr># {
    if (!saw_non_hash) {
        num_hashes++;
    } else if (end_hashes != 0) {
        end_hashes++;
        if (end_hashes == num_hashes) {
            BEGIN(INITIAL);
            std::cout << "YYText [" <<yytext << "]" << std::endl;
            return parser::token::yytokentype::LIT_BYTE_STR_RAW;
        }
    }
    yymore();
}
<rawbytestr>\x22# {
    end_hashes = 1;
    if (end_hashes == num_hashes) {
        BEGIN(INITIAL);
        std::cout << "YYText [" <<yytext << "]" << std::endl;
        return parser::token::yytokentype::LIT_BYTE_STR_RAW;
    }
    yymore();
}
<rawbytestr>(.|\n) {
    if (!saw_non_hash) {
        saw_non_hash = 1;
    }
    if (end_hashes != 0) {
        end_hashes = 0;
    }
    yymore();
}
<rawbytestr><<EOF>> { return -1; }

b\x27                           { BEGIN(byte); yymore(); }
<byte>\\[nrt\\\x27\x220]\x27    { BEGIN(INITIAL); return parser::token::yytokentype::LIT_BYTE; }
<byte>\\x[0-9a-fA-F]{2}\x27     { BEGIN(INITIAL); return parser::token::yytokentype::LIT_BYTE; }
<byte>\\u([0-9a-fA-F]_*){4}\x27 { BEGIN(INITIAL); return parser::token::yytokentype::LIT_BYTE; }
<byte>\\U([0-9a-fA-F]_*){8}\x27 { BEGIN(INITIAL); return parser::token::yytokentype::LIT_BYTE; }
<byte>.\x27                     { BEGIN(INITIAL); return parser::token::yytokentype::LIT_BYTE; }
<byte><<EOF>>                   { BEGIN(INITIAL); return -1; }

r\x22           { BEGIN(rawstr); yymore(); }
<rawstr>\x22    { BEGIN(suffix); return parser::token::yytokentype::LIT_STR_RAW; }
<rawstr>(.|\n)  { yymore(); }
<rawstr><<EOF>> { return -1; }

r/#             {
    BEGIN(rawstr_esc_begin);
    yymore();
    num_hashes = 0;
    saw_non_hash = 0;
    end_hashes = 0;
}

<rawstr_esc_begin># {
    num_hashes++;
    yymore();
}
<rawstr_esc_begin>\x22 {
    BEGIN(rawstr_esc_body);
    yymore();
}
<rawstr_esc_begin>(.|\n) { return -1; }

<rawstr_esc_body>\x22/# {
  BEGIN(rawstr_esc_end);
  yymore();
 }
<rawstr_esc_body>(.|\n) {
  yymore();
 }

<rawstr_esc_end># {
  end_hashes++;
  if (end_hashes == num_hashes) {
    BEGIN(INITIAL);
    return parser::token::yytokentype::LIT_STR_RAW;
  }
  yymore();
 }
<rawstr_esc_end>[^#] {
  end_hashes = 0;
  BEGIN(rawstr_esc_body);
  yymore();
 }

<rawstr_esc_begin,rawstr_esc_body,rawstr_esc_end><<EOF>> { return -1; }

\x22                     { BEGIN(str); yymore(); }
<str>\x22                { BEGIN(suffix); return parser::token::yytokentype::LIT_STR; }

<str><<EOF>>                     { return -1; }
<str>\\[n\nr\rt\\\x27\x220]      { yymore(); }
<str>\\x[0-9a-fA-F]{2}           { yymore(); }
<str>\\u\{([0-9a-fA-F]_*){1,6}\} { yymore(); }
<str>\\[^n\nrt\\\x27\x220]       { return -1; }
<str>(.|\n)                      { yymore(); }

\<-  { return parser::token::yytokentype::LARROW; }
-\>  { return parser::token::yytokentype::RARROW; }
-    { return '-'; }
-=   { return parser::token::yytokentype::MINUSEQ; }
&&   { return parser::token::yytokentype::ANDAND; }
&    { return '&'; }
&=   { return parser::token::yytokentype::ANDEQ; }
\|\| { return parser::token::yytokentype::OROR; }
\|   { return '|'; }
\|=  { return parser::token::yytokentype::OREQ; }
\+   { return '+'; }
\+=  { return parser::token::yytokentype::PLUSEQ; }
\*   { return '*'; }
\*=  { return parser::token::yytokentype::STAREQ; }
\/   { return '/'; }
\/=  { return parser::token::yytokentype::SLASHEQ; }
\^   { return '^'; }
\^=  { return parser::token::yytokentype::CARETEQ; }
%    { return '%'; }
%=   { return parser::token::yytokentype::PERCENTEQ; }

<<EOF>> { return 0; }

%%
