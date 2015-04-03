%{

#define PARSER mm_parser

#include "mm_parser.h"

int yymmlex();
extern char *yymmtext;
int yymmerror(const std::string &error);

#include "mm_y.tab.h"

/*** token declaration **************************************************/
%}

%token TOK_INVERSE     "^-1"
%token TOK_MAPS_TO     "->"
%token TOK_PLUSPLUS    "++"
%token TOK_OROR        "||"
%token TOK_LET         "let"
%token TOK_IN          "in"
%token TOK_MATCH       "match"
%token TOK_WITH        "with"
%token TOK_ACYCLIC     "acyclic"
%token TOK_IRRELFEXIVE "irreflexive"
%token TOK_EMPTY       "empty"
%token TOK_FUN         "fun"
%token TOK_REC         "rec"
%token TOK_BEGIN       "begin"
%token TOK_END         "end"
%token TOK_IDENTIFIER
%token TOK_NUMBER

%start grammar

%{
/************************************************************************/
/*** rules **************************************************************/
/************************************************************************/
%}
%%

grammar : instruction
        ;

expr    : TOK_NUMBER
        | TOK_IDENTIFIER
        | expr '*'
        | expr '+'
        | expr '?'
        | expr "^-1"
        | expr '|' expr
        | expr ';' expr
        | expr '\\' expr
        | expr '&' expr
        | expr "++" expr
        | expr expr
        | "fun" pat "->" expr  
        | "let" binding_list "in" expr  
        | "let" "rec" binding_list "in" expr  
        | '(' expr ')'
        | "begin" expr "end"
        | '\'' TOK_IDENTIFIER
        | '#' TOK_IDENTIFIER
        | '{' expr_list '}'
        | '(' expr_list ')'
        | "match" expr "with" '{' '}' "->" expr "||" TOK_IDENTIFIER "++" TOK_IDENTIFIER "->" expr "end"
        | "match" expr "with" tag_match_list 
        ;

tag_match: '\'' TOK_IDENTIFIER "->" expr
        | '_' "->" expr
        ;

tag_match_list:
          tag_match
        | tag_match_list "||" tag_match
        ;

binding_list:
          binding
        | binding_list "and" binding
        ;

expr_list: /* nothing */
        | expr_list expr
        ;

pat     : TOK_IDENTIFIER
        | '(' identifier_list ')'
        ;

identifier_list: /* nothing */
        | identifier_list TOK_IDENTIFIER
        ;

binding : valbinding
        | funbinding  
        ;
 
valbinding: pat '=' expr  
        ;
 
funbinding: TOK_IDENTIFIER pat '=' expr  
        ;

instruction:
          "let" binding_list
        | "let" "rec" binding_list
        | check expr as_opt
        | "procedure" TOK_IDENTIFIER '(' identifier_list ')' '=' instruction_list "end"
        | "call" TOK_IDENTIFIER expr as_opt
        | "show" expr as_opt
        | "show" identifier_list
        | "unshow" identifier_list
        | "with" TOK_IDENTIFIER "from" expr
        | "forall" TOK_IDENTIFIER "in" expr "do" instruction_list "end"
        | "enum" TOK_IDENTIFIER '=' enum_constant_list
        ;

instruction_list:
          /* nothing */
        | instruction_list instruction
        ;

enum_constant_list:
          '\'' TOK_IDENTIFIER
        | enum_constant_list '\'' TOK_IDENTIFIER
        ;

as_opt  : /* nothing */
        | "as" TOK_IDENTIFIER
        ;

check   : "acyclic"
        | "irreflexive"
        | "empty"
        | '~' "acyclic"
        | '~' "irreflexive"
        | '~' "empty"
        ;

%%
