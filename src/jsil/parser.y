%{

// #define YYDEBUG 1
#define PARSER jsil_parser

#include "jsil_parser.h"

int yyjsillex();
extern char *yyjsiltext;

#define YYJSILSTYPE unsigned
#define YYJSILSTYPE_IS_TRIVIAL 1

#include <goto-programs/goto_instruction_code.h>

#include <util/string_constant.h>

#include "jsil_y.tab.h"

#ifdef _MSC_VER
// possible loss of data
#pragma warning(disable:4242)
// possible loss of data
#pragma warning(disable:4244)
// signed/unsigned mismatch
#pragma warning(disable:4365)
// switch with default but no case labels
#pragma warning(disable:4065)
// unreachable code
#pragma warning(disable:4702)
#endif

/*** token declaration **************************************************/
%}

/*** special scanner reports ***/

%token TOK_SCANNER_ERROR /* used by scanner to report errors */
%token TOK_NEWLINE "<newline>"

/*** keywords ***/

%token TOK_PROCEDURE "procedure"
%token TOK_RETURNS "returns"
%token TOK_TO "to"
%token TOK_THROWS "throws"
%token TOK_EVAL "eval"
%token TOK_LABEL "label"
%token TOK_GOTO "goto"
%token TOK_SKIP "skip"
%token TOK_WITH "with"
%token TOK_NEW "new"
%token TOK_HAS_FIELD "hasField"
%token TOK_DELETE "delete"
%token TOK_PROTO_FIELD "protoField"
%token TOK_PROTO_OBJ "protoObj"
%token TOK_REF "ref"
%token TOK_FIELD "field"
%token TOK_BASE "base"
%token TOK_TYPEOF "typeOf"
%token TOK_NULL "null"
%token TOK_UNDEFINED "#undefined"
%token TOK_EMPTY "#empty"
%token TOK_TRUE "true"
%token TOK_FALSE "false"
%token TOK_PROTO "#proto"
%token TOK_FID "#fid"
%token TOK_SCOPE "#scope"
%token TOK_CONSTRUCTID "#constructid"
%token TOK_PRIMVALUE "#primvalue"
%token TOK_TARGETFUNCTION "#targetfunction"
%token TOK_CLASS "#class"
%token TOK_NUM_TO_STRING "num_to_string"
%token TOK_STRING_TO_NUM "string_to_num"
%token TOK_NUM_TO_INT32 "num_to_int32"
%token TOK_NUM_TO_UINT32 "num_to_uint32"
%token TOK_MEMBER_REFERENCE "#MemberReference"
%token TOK_VARIABLE_REFERENCE "#VariableReference"

/*** type classes ***/

%token TOK_T_NULL "#Null"
%token TOK_T_UNDEFINED "#Undefined"
%token TOK_T_BOOLEAN "#Boolean"
%token TOK_T_STRING "#String"
%token TOK_T_NUMBER "#Number"
%token TOK_T_BUILTIN_OBJECT "#BuiltinObject"
%token TOK_T_USER_OBJECT "#UserObject"
%token TOK_T_OBJECT "#Object"
%token TOK_T_REFERENCE "#Reference"

/*** multi-character operators ***/

%token TOK_DEFEQ ":="
%token TOK_LEQ "<="
%token TOK_AND "and"
%token TOK_OR "or"
%token TOK_SUBTYPE_OF "<:"
%token TOK_LEFT_SHIFT "<<"
%token TOK_SIGNED_RIGHT_SHIFT ">>"
%token TOK_UNSIGNED_RIGHT_SHIFT ">>>"
%token TOK_NOT "not"

/*** scanner parsed tokens (these have a value!) ***/

%token TOK_IDENTIFIER
%token TOK_FLOATING
%token TOK_STRING
%token TOK_BUILTIN_LOC
%token TOK_BUILTIN_IDENTIFIER
%token TOK_SPEC_IDENTIFIER

/*** priority, associativity, etc. definitions **************************/

%start program

%expect 0

%%

program: procedure_decls
       ;

procedure_decls: procedure_decl
               | procedure_decls procedure_decl
               ;

procedure_decl: TOK_PROCEDURE proc_ident '(' parameters_opt ')'
                  TOK_RETURNS TOK_IDENTIFIER TOK_TO TOK_IDENTIFIER
                  TOK_THROWS TOK_IDENTIFIER TOK_TO TOK_IDENTIFIER
                  '{' statements_opt '}'
              {
                symbol_exprt proc(to_symbol_expr(parser_stack($2)));
                code_typet::parameterst parameters;
                forall_operands(it, parser_stack($4))
                {
                  symbol_exprt s(to_symbol_expr(*it));
                  code_typet::parametert p(typet{});
                  p.set_identifier(s.get_identifier());
                  parameters.push_back(p);
                }
                proc.type() = code_typet(std::move(parameters), typet());

                symbol_exprt rv(to_symbol_expr(parser_stack($7)));
                symbol_exprt rl(to_symbol_expr(parser_stack($9)));

                symbol_exprt tv(to_symbol_expr(parser_stack($11)));
                symbol_exprt tl(to_symbol_expr(parser_stack($13)));

                jsil_declarationt decl;
                decl.add_declarator(proc);
                decl.add_returns(rv.get_identifier(), rl.get_identifier());
                decl.add_throws(tv.get_identifier(), tl.get_identifier());
                if(parser_stack($15).is_not_nil())
                  decl.add_value(to_code_block(to_code(parser_stack($15))));

                PARSER.parse_tree.items.push_back(decl);
              }
              ;

proc_ident: TOK_IDENTIFIER
          | TOK_EVAL
          {
            symbol_exprt e = symbol_exprt::typeless("eval");
            newstack($$).swap(e);
          }
          | TOK_BUILTIN_IDENTIFIER
          {
            parser_stack($$).set("proc_type", "builtin");
          }
          | TOK_SPEC_IDENTIFIER
          {
            parser_stack($$).set("proc_type", "spec");
          }
          ;

proc_ident_expr: proc_ident
               | TOK_STRING
               {
                 symbol_exprt s = symbol_exprt::typeless(
                   to_string_constant(parser_stack($$)).get_value());
                 parser_stack($$).swap(s);
               }
               ;

parameters_opt: /* empty */
              {
                newstack($$);
              }
              | parameters
              ;

parameters: TOK_IDENTIFIER
          {
            newstack($$).id(ID_parameters);
            parser_stack($$).add_to_operands(std::move(parser_stack($1)));
          }
          | parameters ',' TOK_IDENTIFIER
          {
            $$=$1;
            parser_stack($$).add_to_operands(std::move(parser_stack($3)));
          }
          ;

statements_opt: /* empty */
              {
                newstack($$);
              }
              | statements
              ;

statements: statement
          {
            code_blockt b({static_cast<codet &>(parser_stack($1))});
            newstack($$).swap(b);
          }
          | statements statement
          {
            $$=$1;
            parser_stack($$).add_to_operands(std::move(parser_stack($2)));
          }
          ;

statement: TOK_NEWLINE
         {
           newstack($$)=code_skipt();
         }
         | instruction TOK_NEWLINE
         {
           $$=$1;
         }
         ;

instruction: TOK_LABEL TOK_IDENTIFIER
           {
             code_labelt l(
               to_symbol_expr(parser_stack($2)).get_identifier(),
               code_skipt());
             newstack($$).swap(l);
           }
           | TOK_GOTO TOK_IDENTIFIER
           {
             code_gotot g(to_symbol_expr(parser_stack($2)).get_identifier());
             newstack($$).swap(g);
           }
           | TOK_GOTO '[' expression ']' TOK_IDENTIFIER ',' TOK_IDENTIFIER
           {
             code_gotot lt(to_symbol_expr(parser_stack($5)).get_identifier());
             code_gotot lf(to_symbol_expr(parser_stack($7)).get_identifier());

             code_ifthenelset ite(parser_stack($3), std::move(lt), std::move(lf));

             newstack($$).swap(ite);
           }
           | TOK_SKIP
           {
             newstack($$)=code_skipt();
           }
           | TOK_IDENTIFIER TOK_DEFEQ rhs
           {
             code_assignt a(parser_stack($1), parser_stack($3));
             newstack($$).swap(a);
           }
           | '[' expression ',' expression ']' TOK_DEFEQ expression
           {
             index_exprt i(parser_stack($2), parser_stack($4));
             code_assignt a(i, parser_stack($7));
             newstack($$).swap(a);
           }
           ;

rhs: expression
   | proc_ident_expr '(' expressions_opt ')' with_opt
   {
     side_effect_expr_function_callt f(parser_stack($1), {}, typet{}, {});
     if(parser_stack($3).is_not_nil())
       f.arguments().swap(parser_stack($3).operands());

     newstack($$).swap(f);

     if(parser_stack($5).is_not_nil())
     {
       with_exprt w(parser_stack($$), parser_stack($5), nil_exprt());
       parser_stack($$).swap(w);
     }
   }
   | TOK_NEW '(' ')'
   {
     exprt n("new");
     newstack($$).swap(n);
   }
   | TOK_HAS_FIELD '(' expression ',' expression ')'
   {
     exprt has_field("hasField");
     has_field.add_to_operands(std::move(parser_stack($3)), std::move(parser_stack($5)));

     newstack($$).swap(has_field);
   }
   | '[' expression ',' expression ']'
   {
     index_exprt i(parser_stack($2), parser_stack($4));
     newstack($$).swap(i);
   }
   | TOK_DELETE '(' expression ',' expression ')'
   {
     exprt d("delete");
     d.add_to_operands(std::move(parser_stack($3)), std::move(parser_stack($5)));

     newstack($$).swap(d);
   }
   | TOK_PROTO_FIELD '(' expression ',' expression ')'
   {
     exprt proto_field("protoField");
     proto_field.add_to_operands(std::move(parser_stack($3)), std::move(parser_stack($5)));

     newstack($$).swap(proto_field);
   }
   | TOK_PROTO_OBJ '(' expression ',' expression ')'
   {
     exprt proto_obj("protoObj");
     proto_obj.add_to_operands(std::move(parser_stack($3)), std::move(parser_stack($5)));

     newstack($$).swap(proto_obj);
   }
   ;

with_opt: /* empty */
        {
          newstack($$);
        }
        | TOK_WITH TOK_IDENTIFIER
        {
          $$=$2;
        }
        ;

expressions_opt: /* empty */
               {
                 newstack($$);
               }
               | expressions
               ;

expressions: expression
           {
             newstack($$).id(ID_expression_list);
             parser_stack($$).add_to_operands(std::move(parser_stack($1)));
           }
           | expressions ',' expression
           {
             $$=$1;
             parser_stack($$).add_to_operands(std::move(parser_stack($3)));
           }
           ;

expression: atom_expression
          | expression binary_op atom_expression
          {
            $$=$2;
            parser_stack($$).add_to_operands(std::move(parser_stack($1)), std::move(parser_stack($3)));
          }
          ;

atom_expression: literal
               | unary_op atom_expression
               {
                 $$=$1;
                 parser_stack($$).add_to_operands(std::move(parser_stack($2)));
               }
               | '(' expression ')'
               {
                 $$=$2;
               }
               | TOK_REF '(' expression ',' expression ',' ref_type ')'
               {
                 exprt ref("ref");
                 ref.add_to_operands(
                   std::move(parser_stack($3)),
                   std::move(parser_stack($5)),
                   std::move(parser_stack($7)));

                 newstack($$).swap(ref);
               }
               | TOK_FIELD '(' expression ')'
               {
                 exprt field("field");
                 field.add_to_operands(std::move(parser_stack($3)));

                 newstack($$).swap(field);
               }
               | TOK_BASE '(' expression ')'
               {
                 exprt base(ID_base);
                 base.add_to_operands(std::move(parser_stack($3)));

                 newstack($$).swap(base);
               }
               | TOK_TYPEOF '(' expression ')'
               {
                 exprt typeof_expr(ID_typeof);
                 typeof_expr.add_to_operands(std::move(parser_stack($3)));

                 newstack($$).swap(typeof_expr);
               }
               ;

literal: TOK_IDENTIFIER
       | TOK_NULL
       {
         newstack($$).id(ID_null);
       }
       | TOK_UNDEFINED
       {
         newstack($$).id("undefined");
       }
       | TOK_EMPTY
       {
         newstack($$).id(ID_empty);
       }
       | TOK_TRUE
       {
         newstack($$) = true_exprt();
       }
       | TOK_FALSE
       {
         newstack($$) = false_exprt();
       }
       | TOK_FLOATING
       | TOK_STRING
       {
         constant_exprt c(to_string_constant(parser_stack($$))
           .get_value(), string_typet());
         parser_stack($$).swap(c);
       }
       | TOK_BUILTIN_LOC
       | jsil_type
       | builtin_field
       ;

builtin_field: TOK_PROTO
             {
               newstack($$).id("proto");
             }
             | TOK_FID
             {
               newstack($$).id("fid");
             }
             | TOK_SCOPE
             {
               newstack($$).id("scope");
             }
             | TOK_CONSTRUCTID
             {
               newstack($$).id("constructid");
             }
             | TOK_PRIMVALUE
             {
               newstack($$).id("primvalue");
             }
             | TOK_TARGETFUNCTION
             {
               newstack($$).id("targetfunction");
             }
             | TOK_CLASS
             {
               newstack($$).id(ID_class);
             }
             ;

binary_op: compare_op
         | arithmetic_op
         | boolean_op
         | bitwise_op
         ;

compare_op: '='
          {
            newstack($$).id(ID_equal);
          }
          | '<'
          {
            newstack($$).id(ID_lt);
          }
          | TOK_LEQ
          {
            newstack($$).id(ID_le);
          }
          ;

arithmetic_op: '+'
             {
               newstack($$).id(ID_plus);
             }
             | '-'
             {
               newstack($$).id(ID_minus);
             }
             | '*'
             {
               newstack($$).id(ID_mult);
             }
             | '/'
             {
               newstack($$).id(ID_div);
             }
             | '%'
             {
               newstack($$).id(ID_mod);
             }
             ;

boolean_op: TOK_AND
          {
            newstack($$).id(ID_and);
          }
          | TOK_OR
          {
            newstack($$).id(ID_or);
          }
          | TOK_SUBTYPE_OF
          {
            newstack($$).id("subtype_of");
          }
          | ':'
          {
            newstack($$).id(ID_concatenation);
          }
          ;

bitwise_op: '&'
          {
            newstack($$).id(ID_bitand);
          }
          | '|'
          {
            newstack($$).id(ID_bitor);
          }
          | '^'
          {
            newstack($$).id(ID_bitxor);
          }
          | TOK_LEFT_SHIFT
          {
            newstack($$).id(ID_shl);
          }
          | TOK_SIGNED_RIGHT_SHIFT
          {
            newstack($$).id(ID_shr);
          }
          | TOK_UNSIGNED_RIGHT_SHIFT
          {
            newstack($$).id(ID_lshr);
          }
          ;

unary_op: TOK_NOT
        {
          newstack($$).id(ID_not);
        }
        | '-'
        {
          newstack($$).id(ID_unary_minus);
        }
        | TOK_NUM_TO_STRING
        {
          newstack($$).id("num_to_string");
        }
        | TOK_STRING_TO_NUM
        {
          newstack($$).id("string_to_num");
        }
        | TOK_NUM_TO_INT32
        {
          newstack($$).id("num_to_int32");
        }
        | TOK_NUM_TO_UINT32
        {
          newstack($$).id("num_to_uint32");
        }
        | '!'
        {
          newstack($$).id(ID_bitnot);
        }
        ;

jsil_type: TOK_T_NULL
         {
           newstack($$).id("null_type");
         }
         | TOK_T_UNDEFINED
         {
           newstack($$).id("undefined_type");
         }
         | TOK_T_BOOLEAN
         {
           newstack($$).id(ID_boolean);
         }
         | TOK_T_STRING
         {
           newstack($$).id(ID_string);
         }
         | TOK_T_NUMBER
         {
           newstack($$).id("number");
         }
         | TOK_T_BUILTIN_OBJECT
         {
           newstack($$).id("builtin_object");
         }
         | TOK_T_USER_OBJECT
         {
           newstack($$).id("user_object");
         }
         | TOK_T_OBJECT
         {
           newstack($$).id("object");
         }
         | ref_type
         | TOK_T_REFERENCE
         {
           newstack($$).id(ID_pointer);
           newstack($$).set(ID_C_reference, true);
         }
         ;

ref_type: TOK_MEMBER_REFERENCE
        {
          newstack($$).id(ID_member);
        }
        | TOK_VARIABLE_REFERENCE
        {
          newstack($$).id("variable");
        }
        ;

%%
