%{

// This parser is based on the IEC standard 61131-3 which, among other things,
// includes a BNF grammar for the Instruction List (IL) language. The
// Statement List language (STL) by Siemens complies with the standards 
// defined by the IEC, although some modifications were made for compatibility
// reasons. As a consequence, the general language structure specified by the 
// IEC is similar to the structure of STL, but there are differences between
// their syntax and some language features (In general, Siemens implements more
// language features in STL than described in the standard).

#ifdef STATEMENT_LIST_DEBUG
#define YYDEBUG 1
#endif
#define PARSER statement_list_parser

#include "statement_list_parser.h"
#include "converters/convert_string_value.h"
#include "converters/statement_list_types.h"

#include <util/bitvector_types.h>
#include <util/std_code.h>

#include <iterator>

int yystatement_listlex(void *);
char *yystatement_listget_text(void *);

int yystatement_listerror(
  statement_list_parsert &statement_list_parser,
  void *scanner,
  const std::string &error)
{
  statement_list_parser.parse_error(error, yystatement_listget_text(scanner));
  return 0;
}

#define YYSTYPE unsigned
#define YYSTYPE_IS_TRIVIAL 1

/* To avoid LTO -Wodr clashes with ansi-c */
#define YYTOKENTYPE 1
#define YYEMPTY -2
#define YYEOF    0                 /* "end of file"  */
#define YYerror 256                /* error  */
#define YYUNDEF 257                /* "invalid token"  */
#include "statement_list_y.tab.h"

// Visual Studio
#ifdef _MSC_VER
// Disable warnings for possible loss of data.
#pragma warning(disable:4242)
#pragma warning(disable:4244)
// Disable warning for signed/unsigned mismatch.
#pragma warning(disable:4365)
// Disable warning for switch with default but no case labels.
#pragma warning(disable:4065)
// Disable warning for unreachable code.
#pragma warning(disable:4702)
#endif
%}

%parse-param {statement_list_parsert &statement_list_parser}
%parse-param {void *scanner}
%lex-param {void *scanner}

/*** Token declaration *******************************************************/

/*** STL file structure keywords *********************************************/
%token STOK_VERSION              "VERSION"
%token STOK_BEGIN                "BEGIN"
%token STOK_FUNCTION_BLOCK       "FUNCTION_BLOCK"
%token STOK_END_FUNCTION_BLOCK   "END_FUNCTION_BLOCK"
%token STOK_FUNCTION             "FUNCTION"
%token STOK_END_FUNCTION         "END_FUNCTION"
%token STOK_VAR_INPUT            "VAR_INPUT"
%token STOK_VAR_INOUT            "VAR_IN_OUT"
%token STOK_VAR_OUTPUT           "VAR_OUTPUT"
%token STOK_VAR_STATIC           "VAR"
%token STOK_VAR_TEMP             "VAR_TEMP"
%token STOK_VAR_CONSTANT         "VAR CONSTANT"
%token STOK_END_VAR              "END_VAR"
%token STOK_NETWORK              "NETWORK"
%token STOK_TITLE                "TITLE"
%token STOK_TAG                  "TAG"
%token STOK_END_TAG              "END_TAG"

/*** Siemens types ***********************************************************/
%token STOK_INT                  "Int"
%token STOK_DINT                 "DInt"
%token STOK_REAL                 "Real"
%token STOK_BOOL                 "Bool"
%token STOK_VOID                 "Void"

/*** Operators ***************************************************************/
%token STOK_LOAD                 "L"
%token STOK_TRANSFER             "T"
%token STOK_CALL                 "CALL"
%token STOK_NOP                  "NOP"
%token STOK_SET_RLO              "SET"
%token STOK_CLR_RLO              "CLR"
%token STOK_SET                  "S"
%token STOK_RESET                "R"
%token STOK_NOT                  "NOT"
%token STOK_AND                  "A"
%token STOK_AND_NOT              "AN"
%token STOK_OR                   "O"
%token STOK_OR_NOT               "ON"
%token STOK_XOR                  "X"
%token STOK_XOR_NOT              "XN"
%token STOK_AND_NESTED           "A("
%token STOK_AND_NOT_NESTED       "AN("
%token STOK_OR_NESTED            "O("
%token STOK_OR_NOT_NESTED        "ON("
%token STOK_XOR_NESTED           "X("
%token STOK_XOR_NOT_NESTED       "XN("
%token STOK_NESTING_CLOSED       ")"
%token STOK_ASSIGN               "="
%token STOK_CONST_ADD            "+"
%token STOK_ACCU_INT_ADD         "+I"
%token STOK_ACCU_INT_SUB         "-I"
%token STOK_ACCU_INT_MUL         "*I"
%token STOK_ACCU_INT_DIV         "/I"
%token STOK_ACCU_INT_EQ          "==I"
%token STOK_ACCU_INT_NEQ         "<>I"
%token STOK_ACCU_INT_GT          ">I"
%token STOK_ACCU_INT_LT          "<I"
%token STOK_ACCU_INT_GTE         ">=I"
%token STOK_ACCU_INT_LTE         "<=I"
%token STOK_ACCU_REAL_ADD        "+R"
%token STOK_ACCU_REAL_SUB        "-R"
%token STOK_ACCU_REAL_MUL        "*R"
%token STOK_ACCU_REAL_DIV        "/R"
%token STOK_ACCU_REAL_EQ         "==R"
%token STOK_ACCU_REAL_NEQ        "<>R"
%token STOK_ACCU_REAL_GT         ">R"
%token STOK_ACCU_REAL_LT         "<R"
%token STOK_ACCU_REAL_GTE        ">=R"
%token STOK_ACCU_REAL_LTE        "<=R"
%token STOK_ACCU_DINT_ADD        "+D"
%token STOK_ACCU_DINT_SUB        "-D"
%token STOK_ACCU_DINT_MUL        "*D"
%token STOK_ACCU_DINT_DIV        "/D"
%token STOK_ACCU_DINT_EQ         "==D"
%token STOK_ACCU_DINT_NEQ        "<>D"
%token STOK_ACCU_DINT_GT         ">D"
%token STOK_ACCU_DINT_LT         "<D"
%token STOK_ACCU_DINT_GTE        ">=D"
%token STOK_ACCU_DINT_LTE        "<=D"
%token STOK_ASSIGNMENT           ":="
%token STOK_JUMP_UNCONDITIONAL   "JU"
%token STOK_JUMP_CONDITIONAL     "JC"
%token STOK_JUMP_CONDITIONAL_NOT "JCN"

/*** Value tokens ***/
%token STOK_INT_LITERAL
%token STOK_BOOL_LITERAL
%token STOK_REAL_LITERAL
%token STOK_IDENTIFIER
%token STOK_TITLE_VALUE
%token STOK_VERSION_VALUE
%token STOK_LABEL

/*** Priority, associativity, etc. definitions *******************************/

%start init

%{
/*** Grammar rules ***********************************************************/

// The follwing abbreviations will be used:
//   Zom: "Zero or more", eqivalent to the '*' quantifier
//   Opt: "Optional", equivalent to the '?' quantifier
//   Oom: "One or more", equivalent to the '+' quantifier
%}
%%

init:
    init FB_Decl
    | init Func_Decl
    | init Tag_Decl
    | /* nothing */
    ;

// Variable and type declarations
Var_Decl_Init:
    Variable_List ':' Simple_Spec_Init
    {
      $$ = $1;
      for(auto &sym : parser_stack($$).operands())
        sym = symbol_exprt(sym.get(ID_identifier), parser_stack($3).type());
    }
    ;

Variable_List:
    Variable_Name Zom_Separated_Variable_Name
    {
      $$ = $2;
      parser_stack($$).add_to_operands(std::move(parser_stack($1)));
    }
    ;

Zom_Separated_Variable_Name:
    Zom_Separated_Variable_Name ',' Variable_Name
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($3)));
    }
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_var_entry);
      
    }
    ;

Variable_Name:
    STOK_IDENTIFIER
    {
      newstack($$);
      parser_stack($$) = 
      symbol_exprt::typeless(parser_stack($1).get(ID_value));
    }
    ;

Simple_Spec_Init:
    Simple_Spec
    ;
    
Simple_Spec:
    Elem_Type_Name
    ;

Elem_Type_Name:
    Numeric_Type_Name
    ;

Numeric_Type_Name:
    Int_Type_Name
    | DInt_Type_Name 
    | Real_Type_Name 
    | Bool_Type_Name
    ;

Int_Type_Name:
    Sign_Int_Type_Name
    ;

Sign_Int_Type_Name:
    STOK_INT
    {
      $$ = $1;
      parser_stack($$).type() = get_int_type();
    }
    ;

DInt_Type_Name:
    Sign_DInt_Type_Name
    ;

Sign_DInt_Type_Name:
    STOK_DINT
    {
      $$ = $1;
      parser_stack($$).type() = get_dint_type();
    }
    ;

Real_Type_Name:
    STOK_REAL
    {
      $$ = $1;
      parser_stack($$).type() = get_real_type();
    }
    ;
    
Bool_Type_Name:
    STOK_BOOL
    {
      $$ = $1;
      parser_stack($$).type() = get_bool_type();
    }
    
Opt_Assignment:
    STOK_ASSIGNMENT Constant
    {
      $$ = $2;
    }
    | /* nothing */
    {
      newstack($$);
    }

// Function Block declaration
Derived_FB_Name:
    STOK_IDENTIFIER
    ;

FB_Decl:
    STOK_FUNCTION_BLOCK Derived_FB_Name Version_Label Zom_FB_General_Var_Decls 
    FB_Body STOK_END_FUNCTION_BLOCK
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_function_block);
      parser_stack($$).add_to_operands(std::move(parser_stack($2)), 
        std::move(parser_stack($3)));
      parser_stack($$).add_to_operands(std::move(parser_stack($4)),
        std::move(parser_stack($5)));
      PARSER.add_function_block(parser_stack($$));
    }
    ;

Version_Label:
    STOK_VERSION ':' STOK_VERSION_VALUE
    {
      $$ = $3;
    }
    ;

Zom_FB_General_Var_Decls:
    Zom_FB_General_Var_Decls FB_General_Var_Decl 
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_var_decls);
    }
    ;

FB_General_Var_Decl:
    FB_IO_Var_Decls
    | FB_Static_Decls
    | Temp_Decls
    | Constant_Decls
    ;

FB_IO_Var_Decls:
    FB_Input_Decls 
    | FB_Output_Decls
    | FB_Inout_Decls
    ;

FB_Input_Decls:
    STOK_VAR_INPUT Zom_FB_Input_Decl STOK_END_VAR
    {
      $$ = $2;
    }
    ;

Zom_FB_Input_Decl:
    Zom_FB_Input_Decl FB_Input_Decl ';'
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_var_input);
    } 
    ;

FB_Input_Decl:
    Var_Decl_Init Opt_Assignment
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    ;

FB_Output_Decls:
    STOK_VAR_OUTPUT Zom_FB_Output_Decl STOK_END_VAR
    {
      $$ = $2;
    }
    ;

Zom_FB_Output_Decl:
    Zom_FB_Output_Decl FB_Output_Decl ';'
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_var_output);
    } 
    ;

FB_Output_Decl:
    Var_Decl_Init Opt_Assignment
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    ;
    
FB_Inout_Decls:
    STOK_VAR_INOUT Zom_FB_Inout_Decl STOK_END_VAR
    {
      $$ = $2;
    }
    ;

Zom_FB_Inout_Decl:
    Zom_FB_Inout_Decl FB_Inout_Decl ';'
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_var_inout);
    } 
    ;

FB_Inout_Decl:
    Var_Decl_Init Opt_Assignment
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    ;
    
FB_Static_Decls:
    STOK_VAR_STATIC Zom_FB_Static_Decl STOK_END_VAR
    {
      $$ = $2;
    }
    ;

Zom_FB_Static_Decl:
    Zom_FB_Static_Decl FB_Static_Decl ';'
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_var_static);
    } 
    ;

FB_Static_Decl:
    Var_Decl_Init Opt_Assignment
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    ;

FB_Body:
    STOK_BEGIN Zom_IL_Network
    {
      $$ = $2;
    }
    ;

// Function declaration 
Func_Decl:
    STOK_FUNCTION Derived_Func_Name ':' Func_Return_Value Version_Label 
    Zom_Func_General_Var_Decls Func_Body STOK_END_FUNCTION
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_function);
      parser_stack($$).add_to_operands(std::move(parser_stack($2)),
      std::move(parser_stack($4)), std::move(parser_stack($5)));
      parser_stack($$).add_to_operands(std::move(parser_stack($6)), 
        std::move(parser_stack($7)));
      PARSER.add_function(parser_stack($$));
    }
    ;
    
Derived_Func_Name:
    STOK_IDENTIFIER
    ;
    
Func_Return_Value:
    STOK_VOID
    {
      parser_stack($$).set(ID_statement_list_type, ID_statement_list_return);
    }
    | Simple_Spec
    {
      parser_stack($$).set(ID_statement_list_type, ID_statement_list_return);
    }
    ;
    
Zom_Func_General_Var_Decls:
    Zom_Func_General_Var_Decls Func_General_Var_Decl 
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_var_decls);
    }
    ;

Func_General_Var_Decl:
    IO_Var_Decls
    | Temp_Decls
    | Constant_Decls
    ;

IO_Var_Decls:
    Input_Decls 
    | Output_Decls
    | Inout_Decls
    ;

Input_Decls:
    STOK_VAR_INPUT Zom_Input_Decl STOK_END_VAR
    {
      $$ = $2;
    }
    ;

Zom_Input_Decl:
    Zom_Input_Decl Input_Decl ';'
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_var_input);
    } 
    ;

Input_Decl:
    Var_Decl_Init
    ;
    
Inout_Decls:
    STOK_VAR_INOUT Zom_Inout_Decl STOK_END_VAR
    {
      $$ = $2;
    }
    ;

Zom_Inout_Decl:
    Zom_Inout_Decl Inout_Decl ';'
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_var_inout);
    } 
    ;

Inout_Decl:
    Var_Decl_Init
    ;

Output_Decls:
    STOK_VAR_OUTPUT Zom_Output_Decl STOK_END_VAR
    {
      $$ = $2;
    }
    ;

Zom_Output_Decl:
    Zom_Output_Decl Output_Decl ';'
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_var_output);
    } 
    ;

Output_Decl:
    Var_Decl_Init
    ;
    
Temp_Decls:
    STOK_VAR_TEMP Zom_Temp_Decl STOK_END_VAR
    {
      $$ = $2;
    }
    ;

Zom_Temp_Decl:
    Zom_Temp_Decl Temp_Decl ';'
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_var_temp);
    } 
    ;

Temp_Decl:
    Var_Decl_Init
    ;
    
Constant_Decls:
    STOK_VAR_CONSTANT Zom_Constant_Decl STOK_END_VAR
    {
      $$ = $2;
    }
    ;

Zom_Constant_Decl:
    Zom_Constant_Decl Constant_Decl ';'
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_var_constant);
    } 
    ;

Constant_Decl:
    Var_Decl_Init Opt_Assignment
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    ;
    
Func_Body:
    STOK_BEGIN Zom_IL_Network
    {
      $$ = $2;
    }
    ;
    
// Network declaration
Zom_IL_Network:
    Zom_IL_Network IL_Network
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_networks);
    }
    ;

IL_Network:
    STOK_NETWORK STOK_TITLE STOK_ASSIGN Opt_TITLE_VALUE Opt_Instruction_List
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_network);
      parser_stack($$).add_to_operands(std::move(parser_stack($4)), 
        std::move(parser_stack($5)));
    }
    ;
    
    
Opt_TITLE_VALUE:
    STOK_TITLE_VALUE
    | /* nothing */
    {
      newstack($$);
      parser_stack($$) = convert_title("");
    }
    ;

Opt_Instruction_List:
    Instruction_List
    | 
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_instructions);
    }
    ;
    
// Statement List grammar
Instruction_List: 
    Oom_IL_Instruction
    ;

Oom_IL_Instruction: 
    Oom_IL_Instruction IL_Instruction
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | IL_Instruction
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_instructions);
      parser_stack($$).add_to_operands(std::move(parser_stack($1)));
    }
    ;

IL_Instruction: 
    Opt_Label Instruction ';'
    {
      $$ = $2;
      parser_stack($$).add_to_operands(std::move(parser_stack($1)));
    }
    ;

Opt_Label:
    IL_Label
    | /* nothing */
    {
      newstack($$);
       // ID of expression is nil to indicate that there is no label
    } 
    ;

IL_Label:
    STOK_LABEL
    ;

Instruction:
    IL_Simple_Operation
    | IL_Invocation
    ;

IL_Simple_Operation: 
    IL_Simple_Operator Opt_Operand
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_instruction);
      parser_stack($$).add_to_operands(std::move(parser_stack($1)), 
        std::move(parser_stack($2)));
    }
    ;

Opt_Operand:
    IL_Operand
    | 
    {
      newstack($$);
      // ID of expression is nil to indicate that there is no operand
    }
    ;

IL_Simple_Operator:
    STOK_LOAD 
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_load);
    }
    | STOK_TRANSFER
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_transfer);
    }
    | STOK_NOP
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_nop);
    }
    | STOK_CONST_ADD
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_const_add);
    }
    | STOK_ACCU_INT_ADD
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_add);
    }
    | STOK_ACCU_INT_SUB
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_sub);
    }
    | STOK_ACCU_INT_MUL
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_mul);
    }
    | STOK_ACCU_INT_DIV
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_div);
    }
    | STOK_ACCU_INT_EQ
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_eq);
    }
    | STOK_ACCU_INT_NEQ
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_neq);
    }
    | STOK_ACCU_INT_GT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_gt);
    }
    | STOK_ACCU_INT_LT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_lt);
    }
    | STOK_ACCU_INT_GTE
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_gte);
    }
    | STOK_ACCU_INT_LTE
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_lte);
    }
    | STOK_ACCU_REAL_ADD
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_add);
    }
    | STOK_ACCU_REAL_SUB
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_sub);
    }
    | STOK_ACCU_REAL_MUL
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_mul);
    }
    | STOK_ACCU_REAL_DIV
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_div);
    }
    | STOK_ACCU_REAL_EQ
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_eq);
    }
    | STOK_ACCU_REAL_NEQ
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_neq);
    }
    | STOK_ACCU_REAL_GT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_gt);
    }
    | STOK_ACCU_REAL_LT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_lt);
    }
    | STOK_ACCU_REAL_GTE
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_gte);
    }
    | STOK_ACCU_REAL_LTE
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_lte);
    }
    | STOK_ACCU_DINT_ADD
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_add);
    }
    | STOK_ACCU_DINT_SUB
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_sub);
    }
    | STOK_ACCU_DINT_MUL
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_mul);
    }
    | STOK_ACCU_DINT_DIV
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_div);
    }
    | STOK_ACCU_DINT_EQ
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_eq);
    }
    | STOK_ACCU_DINT_NEQ
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_neq);
    }
    | STOK_ACCU_DINT_GT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_gt);
    }
    | STOK_ACCU_DINT_LT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_lt);
    }
    | STOK_ACCU_DINT_GTE
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_gte);
    }
    | STOK_ACCU_DINT_LTE
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_lte);
    }
    | STOK_AND 
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_and);
    }
    | STOK_AND_NOT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_and_not);
    } 
    | STOK_OR
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_or);
    } 
    | STOK_OR_NOT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_or_not);
    }  
    | STOK_XOR 
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_xor);
    }
    | STOK_XOR_NOT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_xor_not);
    }
    | STOK_AND_NESTED 
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_and_nested);
    }
    | STOK_AND_NOT_NESTED
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_and_not_nested);
    }
    | STOK_OR_NESTED
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_or_nested);
    }
    | STOK_OR_NOT_NESTED
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_or_not_nested);
    }
    | STOK_XOR_NESTED 
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_xor_nested);
    }
    | STOK_XOR_NOT_NESTED
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_xor_not_nested);
    }
    | STOK_NESTING_CLOSED
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_nesting_closed);
    }
    | STOK_ASSIGN
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_assign);
    }
    | STOK_SET_RLO
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_set_rlo);
    }
    | STOK_CLR_RLO
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_clr_rlo);
    }
    | STOK_SET
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_set);
    }
    | STOK_RESET
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_reset);
    }
    | STOK_NOT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_not);
    }
    | STOK_JUMP_UNCONDITIONAL
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_jump_unconditional);
    }
    | STOK_JUMP_CONDITIONAL
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_jump_conditional);
    }
    | STOK_JUMP_CONDITIONAL_NOT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_jump_conditional_not);
    }
    ;

IL_Operand:
    Constant
    | Variable_Access
    ;

Variable_Access:
    '#' Variable_Name
    {
      $$ = $2;
    }
    | Variable_Name
    {
      $$ = $1;
    }
    ;
    
Constant:
    STOK_INT_LITERAL
    | STOK_BOOL_LITERAL
    | STOK_REAL_LITERAL
    ;
    
IL_Invocation:
    Call Callee_Name Opt_Data_Block Opt_Param_List
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_instruction);
      parser_stack($$).add_to_operands(std::move(parser_stack($1)), 
        std::move(parser_stack($2)), std::move(parser_stack($3)));    
      std::move(parser_stack($4).operands().begin(), 
        parser_stack($4).operands().end(), 
        std::back_inserter(parser_stack($$).operands()));
    }
    ;
    
Call:
    STOK_CALL
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_call);
    }
    ;

Callee_Name:
    Derived_Func_Name
    {
      newstack($$);
      parser_stack($$) = 
        symbol_exprt::typeless(parser_stack($1).get(ID_value));
    }
    ;
    
Opt_Param_List:
    '(' Oom_Param_Assignment STOK_NESTING_CLOSED
    {
      $$ = $2;
    }
    | /* nothing */
    {
      newstack($$);
    }
    ;
    
Oom_Param_Assignment:
    Oom_Param_Assignment ',' Param_Assignment
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($3)));
    }
    | Param_Assignment
    {
      newstack($$);
      parser_stack($$).add_to_operands(std::move(parser_stack($1)));
    }
    ;
    
Param_Assignment:
    Variable_Name STOK_ASSIGNMENT IL_Operand
    {
      newstack($$);
      parser_stack($$) = code_frontend_assignt(std::move(parser_stack($1)),
        std::move(parser_stack($3)));
    }
    ;
Opt_Data_Block:
    ',' Variable_Name
    {
      $$ = $2;
      parser_stack($$).set(
        ID_statement_list_type, ID_statement_list_data_block);
    }
    | /* nothing */
    {
      newstack($$);
    }
    ;

// Tag declaration
Tag_Decl:
    STOK_TAG Opt_Tag_List STOK_END_TAG
    {
      PARSER.add_tag_list(parser_stack($2));
    }
    ;
    
Opt_Tag_List:
    Tag_List
    | /* nothing */
    {
      newstack($$);
    }
    ;
    
Tag_List:
    Tag_List Variable_Name Simple_Spec_Init
    {
      $$ = $1;
      symbol_exprt sym{parser_stack($2).get(ID_identifier), parser_stack($3).type()};
      parser_stack($$).add_to_operands(std::move(sym));
    }
    | Variable_Name Simple_Spec_Init
    {
      newstack($$);
      symbol_exprt sym{parser_stack($1).get(ID_identifier), parser_stack($2).type()};
      parser_stack($$).add_to_operands(std::move(sym));
    }
    ;
%%
