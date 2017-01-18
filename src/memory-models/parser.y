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
%token TOK_AND         "and"
%token TOK_IN          "in"
%token TOK_DO          "do"
%token TOK_MATCH       "match"
%token TOK_WITH        "with"
%token TOK_FROM        "from"
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
%token TOK_CALL        "call"
%token TOK_INCLUDE     "include"
%token TOK_SET_INTERSECTION "∩"
%token TOK_SET_UNION   "∪"
%token TOK_CROSS_PRODUCT "⨯"
%token TOK_EMPTY_SET   "∅"

%token TOK_IDENTIFIER
%token TOK_TAG_IDENTIFIER
%token TOK_NUMBER
%token TOK_STRING

%left '*' "⨯"
%right ','
%left prec_let
%left prec_fun
%left prec_app
%right '|' "∪"
%right "++"
%right ';'
%left '\\'
%right '&' "∩"
%nonassoc '~' '+' '?'
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

simple_expr: 
          TOK_NUMBER
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
        | '{' expr_list_opt '}'
        {
          $$=$1;
          stack($$).id(ID_set);
          mto($$, $2);
        }
        | '(' expr ')'
        {
          $$=$2;
        }
        | '(' tuple ')'
        {
          $$=$1;
          stack($$).id("tuple");
          mto($$, $2);
        }
        | '(' ')'
        {
          // only used for procedure calls
          $$=$1;
          stack($$).id("empty_tuple");
        }
        | '_'
        {
          $$=$1;
          stack($$).id("universe");
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
        | expr '*' simple_expr
        {
          // The simple_expr in the rule above is to avoid a conflict
          // between a*b and a*, say followed by LET
          $$=$2;
          stack($$).id("cartesian_product");
          mto($$, $1);
          mto($$, $3);
        }
        | expr "⨯" simple_expr
        {
          // The simple_expr in the rule above could be expr,
          // as there is no ambiguity with the reflexive transitive closure.
          $$=$2;
          stack($$).id("cartesian_product");
          mto($$, $1);
          mto($$, $3);
        }
        | expr '?'
        {
          $$=$2;
          stack($$).id("reflexive_closure");
          mto($$, $1);
        }
        | '~' expr
        {
          $$=$1;
          stack($$).id("complement");
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
        | expr "∪" expr
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
        | expr "∩" expr
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
        | identifier simple_expr_sequence %prec prec_app
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
        | "let" pat_bind_list "in" expr %prec prec_let
        {
          $$=$1;
          stack($$).id(ID_let);
          mto($$, $2);
          mto($$, $4);
        }
        | "let" "rec" pat_bind_list "in" expr %prec prec_let
        {
          $$=$1;
          stack($$).id(ID_let);
          mto($$, $3);
          mto($$, $5);
        }
        | "match" expr "with" alt_opt tag_match_list "end"
        {
          $$=$1;
          stack($$).id("match");
          mto($$, $2);
          mto($$, $5);
        }
        ;

alt_opt : /* nothing */
        | "||";
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

pat_bind_list:
          pat_bind
        {
          newstack($$);
          mto($$, $1);
        }
        | pat_bind_list "and" pat_bind
        {
          $$=$1;
          mto($$, $3);
        }
        ;

simple_expr_sequence:
          simple_expr
        {
          newstack($$);
          mto($$, $1);
        }
        | simple_expr_sequence simple_expr
        {
          $$=$1;
          mto($$, $1);
        }
        ;

tuple:
          expr ',' expr
        {
          newstack($$);
          mto($$, $1);
        }
        | tuple ',' expr
        {
          $$=$1;
          mto($$, $1);
        }
        ;

expr_list:
          expr
        {
          newstack($$);
          mto($$, $1);
        }
        | expr_list ',' expr
        {
          $$=$1;
          mto($$, $1);
        }
        ;

expr_list_opt: /* nothing */
        {
          newstack($$);
        }
        | expr_list
        ;

pat     : identifier
        | '(' identifier_list_opt ')'
        {
          $$=$2;
        }
        ;

identifier_list:
          identifier
        {
          newstack($$);
          mto($$, $1);
        }
        | identifier_list ',' identifier
        {
          $$=$1;
          mto($$, $2);
        }
        ;

identifier_list_opt: /* nothing */
        {
          newstack($$);
        }
        | identifier_list
        ;

pat_bind: identifier '=' expr
        {
          $$=$2;
          stack($$).id("valbinding");
          mto($$, $1);
          mto($$, $3);
        }
        | identifier '(' identifier_list_opt ')' '=' expr
        {
          $$=$2;
          stack($$).id("funbinding");
          mto($$, $1);
          mto($$, $3);
          mto($$, $6);
        }
        | identifier identifier '=' expr
        {
          $$=$3;
          stack($$).id("funbinding");
          mto($$, $1);
          mto($$, $2);
          mto($$, $4);
        }
        ;

instruction:
          "let" pat_bind_list
        {
          $$=$1;
          stack($$).id(ID_code);
          stack($$).set(ID_statement, ID_let);
          mto($$, $2);
        }
        | "let" "rec" pat_bind_list
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
        | "procedure" identifier '(' identifier_list_opt ')' '=' instruction_list "end"
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
        | "show" expr_list as_opt
        {
          $$=$1;
          stack($$).id(ID_code);
          stack($$).set(ID_statement, "show");
          mto($$, $2);
          mto($$, $3);
        }
        | "unshow" expr_list
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
          stack($$).set(ID_statement, ID_c_enum);
          mto($$, $2);
          mto($$, $4);
        }
        | "include" TOK_STRING
        {
          $$=$1;
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
