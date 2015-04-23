%{

#define PARSER mm_parser
#define YYSTYPE unsigned
#define YYSTYPE_IS_TRIVIAL 1

#include "mm_parser.h"

int yymmlex();
extern char *yymmtext;
int yymmerror(const std::string &error);

#include "mm_y.tab.h"

#define mto(x, y) stack(x).move_to_operands(stack(y))

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
%token TOK_FLAG        "flag"
%token TOK_SHOW        "show"
%token TOK_UNSHOW      "unshow"
%token TOK_PROCEDURE   "procedure"
%token TOK_ENUM        "enum"
%token TOK_FORALL      "forall"
%token TOK_AS          "as"

%token TOK_IDENTIFIER
%token TOK_TAG_IDENTIFIER
%token TOK_NUMBER
%token TOK_STRING

%right ','
%left prec_let
%left prec_fun
%left prec_app
%right '|'
%right "++"
%right ';'
%left '\\'
%right '&'
%nonassoc '*' '+' '?'
%nonassoc "^-1"

%start grammar

%{
/************************************************************************/
/*** rules **************************************************************/
/************************************************************************/
%}
%%

grammar : model_name instruction_list
        {
          PARSER.model_name=stack($1).id();
          PARSER.instruction=stack($2);
        }
        ;

model_name:
          TOK_IDENTIFIER
        {
          $$=$1;
          stack($$).id(yymmtext);
        }
        | TOK_STRING
        {
          $$=$1;
          std::string s;
          const char *p=yymmtext+1;
          while(*p!=0 && *p!='"') { s+=*p; p++; }
          stack($$).id(s);
        }
        ;

simple_expr: TOK_NUMBER
        {
          $$=$1;
          stack($$).id(ID_constant);
          stack($$).set(ID_value, yymmtext);
        }
        | identifier
        | tag_identifier
        | "begin" expr "end"
        {
          $$=$2;
        }
        | '{' expr_list '}'
        {
          $$=$1;
          stack($$).id(ID_set);
          mto($$, $2);
        }
        | '(' expr ')'
        {
          $$=$2;
        }
        | '(' expr_list ')'
        {
          $$=$1;
          stack($$).id("tuple");
          mto($$, $2);
        }
        ;

expr:     simple_expr
        | expr '*'
        {
          $$=$2;
          stack($$).id("reflexive_transitive_closure");
          mto($$, $1);
        }
        | expr '+'
        {
          $$=$2;
          stack($$).id("transitive_closure");
          mto($$, $1);
        }
        | expr '?'
        {
          $$=$2;
          stack($$).id("question_mark");
          mto($$, $1);
        }
        | expr "^-1"
        {
          $$=$2;
          stack($$).id("inverse");
          mto($$, $1);
        }
        | expr '|' expr
        {
          $$=$2;
          stack($$).id("union");
          mto($$, $1);
          mto($$, $3);
        }
        | expr ';' expr
        {
          $$=$2;
          stack($$).id("sequence");
          mto($$, $1);
          mto($$, $3);
        }
        | expr '\\' expr
        {
          $$=$2;
          stack($$).id("set_minus");
          mto($$, $1);
          mto($$, $3);
        }
        | expr '&' expr
        {
          $$=$2;
          stack($$).id("intersection");
          mto($$, $1);
          mto($$, $3);
        }
        | expr "++" expr
        {
          $$=$2;
          stack($$).id("plusplus");
          mto($$, $1);
          mto($$, $3);
        }
        | identifier simple_expr %prec prec_app
        {
          newstack($$);
          stack($$).id(ID_function_call);
          mto($$, $1);
          mto($$, $2);
        }
        | "fun" pat "->" expr %prec prec_fun
        {
          $$=$1;
          stack($$).id(ID_function);
          mto($$, $2);
          mto($$, $4);
        }
        | "let" binding_list "in" expr %prec prec_let
        {
          $$=$1;
          stack($$).id(ID_let);
          mto($$, $2);
          mto($$, $4);
        }
        | "let" "rec" binding_list "in" expr %prec prec_let
        {
          $$=$1;
          stack($$).id(ID_let);
          mto($$, $3);
          mto($$, $5);
        }
        | "match" expr "with" tag_match_list "end"
        {
          $$=$1;
          stack($$).id("match");
          mto($$, $2);
          mto($$, $4);
        }
        ;

flag_opt: /* nothing */
        {
          newstack($$);
          stack($$)=exprt(ID_nil);
        }
        | "flag"
        {
          $$=$1;
          stack($$).id("flag");
        }
        ;

tag_match: expr "->" expr
        {
          $$=$2;
          mto($$, $1);
          mto($$, $3);
        }
        | '_' "->" expr
        {
          $$=$2;
          stack($1).id(ID_default);
          mto($$, $1);
          mto($$, $3);
        }
        ;

tag_match_list:
          tag_match
        {
          newstack($$);
          mto($$, $1);
        }
        | tag_match_list "||" tag_match
        {
          $$=$1;
          mto($$, $3);
        }
        ;

binding_list:
          binding
        {
          newstack($$);
          mto($$, $1);
        }
        | binding_list "and" binding
        {
          $$=$1;
          mto($$, $3);
        }
        ;

expr_list: /* nothing */
        {
          newstack($$);
        }
        | expr_list ',' expr
        {
          $$=$1;
          mto($$, $1);
        }
        ;

pat     : identifier
        | '(' identifier_list ')'
        {
          $$=$2;
        }
        ;

identifier_list: /* nothing */
        {
          newstack($$);
        }
        | identifier_list ',' identifier
        {
          $$=$1;
          mto($$, $2);
        }
        ;

binding : valbinding
        | funbinding  
        ;
 
valbinding: pat '=' expr  
        {
          $$=$2;
          stack($$).id("valbinding");
          mto($$, $1);
          mto($$, $3);
        }
        ;
 
funbinding: identifier pat '=' expr  
        {
          $$=$3;
          stack($$).id("funbinding");
          mto($$, $1);
          mto($$, $2);
          mto($$, $3);
        }
        ;

instruction:
          "let" binding_list
        {
          $$=$1;
          stack($$).id(ID_code);
          stack($$).set(ID_statement, ID_let);
          mto($$, $2);
        }
        | "let" "rec" binding_list
        {
          $$=$1;
          stack($$).id(ID_code);
          stack($$).set(ID_statement, ID_let);
          mto($$, $3);
        }
        | flag_opt check expr as_opt
        {
          newstack($$);
          stack($$).id(ID_code);
          stack($$).set(ID_statement, "check");
          mto($$, $2);
          mto($$, $3);
          mto($$, $4);
        }
        | "procedure" identifier '(' identifier_list ')' '=' instruction_list "end"
        {
          $$=$1;
          stack($$).id(ID_code);
          stack($$).set(ID_statement, "procedure");
          mto($$, $2);
          mto($$, $4);
          mto($$, $7);
        }
        | "call" identifier expr as_opt
        {
          $$=$1;
          stack($$).id(ID_code);
          stack($$).set(ID_statement, "call");
          mto($$, $2);
          mto($$, $3);
        }
        | "show" identifier_list
        {
          $$=$1;
          stack($$).id(ID_code);
          stack($$).set(ID_statement, "show");
          mto($$, $2);
        }
        | "unshow" identifier_list
        {
          $$=$1;
          stack($$).id(ID_code);
          stack($$).set(ID_statement, "unshow");
          mto($$, $2);
        }
        | "with" identifier "from" expr
        {
          $$=$1;
          stack($$).id(ID_code);
          stack($$).set(ID_statement, ID_with);
          mto($$, $2);
          mto($$, $4);
        }
        | "forall" identifier "in" expr "do" instruction_list "end"
        {
          $$=$1;
          stack($$).id(ID_code);
          stack($$).set(ID_statement, ID_forall);
          mto($$, $2);
          mto($$, $4);
          mto($$, $6);
        }
        | "enum" identifier '=' enum_constant_list
        {
          $$=$1;
          stack($$).id(ID_code);
          stack($$).set(ID_statement, ID_enum);
          mto($$, $2);
          mto($$, $4);
        }
        ;

instruction_list:
          /* nothing */
        {
          newstack($$);
          stack($$).id(ID_code);
          stack($$).set(ID_statement, ID_block);
        }
        | instruction_list instruction
        {
          $$=$1;
          mto($$, $2);
        }
        ;

enum_constant_list:
          tag_identifier
        {
          newstack($$);
          mto($$, $1);
        }
        | enum_constant_list "||" tag_identifier
        {
          $$=$1;
          mto($$, $3);
        }
        ;

as_opt  : /* nothing */
        {
          newstack($$);
        }
        | "as" identifier
        {
          newstack($$);
          stack($$).id("as");
          mto($$, $2);
        }
        ;

identifier:
          TOK_IDENTIFIER
        {
          $$=$1;
          stack($$).set(ID_identifier, yymmtext);
          stack($$).id(ID_symbol);
        }
        ;

tag_identifier:
          TOK_TAG_IDENTIFIER
        {
          $$=$1;
          stack($$).set(ID_identifier, yymmtext);
          stack($$).id(ID_symbol);
        }
        ;

check   : "acyclic"
        {
          $$=$1;
          stack($$).id("acyclic");
        }
        | "irreflexive"
        {
          $$=$1;
          stack($$).id("irreflexive");
        }
        | "empty"
        {
          $$=$1;
          stack($$).id("empty");
        }
        | '~' "acyclic"
        {
          $$=$1;
          stack($$).id("not_acyclic");
        }
        | '~' "irreflexive"
        {
          $$=$1;
          stack($$).id("not_irreflexive");
        }
        | '~' "empty"
        {
          $$=$1;
          stack($$).id("not_empty");
        }
        ;

%%
