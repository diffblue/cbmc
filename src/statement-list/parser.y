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
#include <util/std_expr.h>
#include <iterator>

int yystatement_listlex();
extern char *yystatement_listtext;

#define YYSTYPE unsigned
#define YYSTYPE_IS_TRIVIAL 1

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

/*** Token declaration *******************************************************/
%}

/*** STL file structure keywords *********************************************/
%token TOK_VERSION              "VERSION"
%token TOK_BEGIN                "BEGIN"
%token TOK_FUNCTION_BLOCK       "FUNCTION_BLOCK"
%token TOK_END_FUNCTION_BLOCK   "END_FUNCTION_BLOCK"
%token TOK_FUNCTION             "FUNCTION"
%token TOK_END_FUNCTION         "END_FUNCTION"
%token TOK_VAR_INPUT            "VAR_INPUT"
%token TOK_VAR_INOUT            "VAR_IN_OUT"
%token TOK_VAR_OUTPUT           "VAR_OUTPUT"
%token TOK_VAR_STATIC           "VAR"
%token TOK_VAR_TEMP             "VAR_TEMP"
%token TOK_VAR_CONSTANT         "VAR CONSTANT"
%token TOK_END_VAR              "END_VAR"
%token TOK_NETWORK              "NETWORK"
%token TOK_TITLE                "TITLE"
%token TOK_TAG                  "TAG"
%token TOK_END_TAG              "END_TAG"

/*** Siemens types ***********************************************************/
%token TOK_INT                  "Int"
%token TOK_DINT                 "DInt"
%token TOK_REAL                 "Real"
%token TOK_BOOL                 "Bool"
%token TOK_VOID                 "Void"

/*** Operators ***************************************************************/
%token TOK_LOAD                 "L"
%token TOK_TRANSFER             "T"
%token TOK_CALL                 "CALL"
%token TOK_NOP                  "NOP"
%token TOK_SET_RLO              "SET"
%token TOK_CLR_RLO              "CLR"
%token TOK_SET                  "S"
%token TOK_RESET                "R"
%token TOK_NOT                  "NOT"
%token TOK_AND                  "A"
%token TOK_AND_NOT              "AN"
%token TOK_OR                   "O"
%token TOK_OR_NOT               "ON"
%token TOK_XOR                  "X"
%token TOK_XOR_NOT              "XN"
%token TOK_AND_NESTED           "A("
%token TOK_AND_NOT_NESTED       "AN("
%token TOK_OR_NESTED            "O("
%token TOK_OR_NOT_NESTED        "ON("
%token TOK_XOR_NESTED           "X("
%token TOK_XOR_NOT_NESTED       "XN("
%token TOK_NESTING_CLOSED       ")"
%token TOK_ASSIGN               "="
%token TOK_CONST_ADD            "+"
%token TOK_ACCU_INT_ADD         "+I"
%token TOK_ACCU_INT_SUB         "-I"
%token TOK_ACCU_INT_MUL         "*I"
%token TOK_ACCU_INT_DIV         "/I"
%token TOK_ACCU_INT_EQ          "==I"
%token TOK_ACCU_INT_NEQ         "<>I"
%token TOK_ACCU_INT_GT          ">I"
%token TOK_ACCU_INT_LT          "<I"
%token TOK_ACCU_INT_GTE         ">=I"
%token TOK_ACCU_INT_LTE         "<=I"
%token TOK_ACCU_REAL_ADD        "+R"
%token TOK_ACCU_REAL_SUB        "-R"
%token TOK_ACCU_REAL_MUL        "*R"
%token TOK_ACCU_REAL_DIV        "/R"
%token TOK_ACCU_REAL_EQ         "==R"
%token TOK_ACCU_REAL_NEQ        "<>R"
%token TOK_ACCU_REAL_GT         ">R"
%token TOK_ACCU_REAL_LT         "<R"
%token TOK_ACCU_REAL_GTE        ">=R"
%token TOK_ACCU_REAL_LTE        "<=R"
%token TOK_ACCU_DINT_ADD        "+D"
%token TOK_ACCU_DINT_SUB        "-D"
%token TOK_ACCU_DINT_MUL        "*D"
%token TOK_ACCU_DINT_DIV        "/D"
%token TOK_ACCU_DINT_EQ         "==D"
%token TOK_ACCU_DINT_NEQ        "<>D"
%token TOK_ACCU_DINT_GT         ">D"
%token TOK_ACCU_DINT_LT         "<D"
%token TOK_ACCU_DINT_GTE        ">=D"
%token TOK_ACCU_DINT_LTE        "<=D"
%token TOK_ASSIGNMENT           ":="

/*** Value tokens ***/
%token TOK_INT_LITERAL
%token TOK_BOOL_LITERAL
%token TOK_REAL_LITERAL
%token TOK_IDENTIFIER
%token TOK_TITLE_VALUE
%token TOK_VERSION_VALUE
%token TOK_LABEL

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
    TOK_IDENTIFIER
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
    TOK_INT
    {
      $$ = $1;
      parser_stack($$).type() = get_int_type();
    }
    ;

DInt_Type_Name:
    Sign_DInt_Type_Name
    ;

Sign_DInt_Type_Name:
    TOK_DINT
    {
      $$ = $1;
      parser_stack($$).type() = get_dint_type();
    }
    ;

Real_Type_Name:
    TOK_REAL
    {
      $$ = $1;
      parser_stack($$).type() = get_real_type();
    }
    ;
    
Bool_Type_Name:
    TOK_BOOL
    {
      $$ = $1;
      parser_stack($$).type() = get_bool_type();
    }
    
Opt_Assignment:
    TOK_ASSIGNMENT Constant
    {
      $$ = $2;
    }
    | /* nothing */
    {
      newstack($$);
    }

// Function Block declaration
Derived_FB_Name:
    TOK_IDENTIFIER
    ;

FB_Decl:
    TOK_FUNCTION_BLOCK Derived_FB_Name Version_Label Zom_FB_General_Var_Decls 
    FB_Body TOK_END_FUNCTION_BLOCK
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
    TOK_VERSION ':' TOK_VERSION_VALUE
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
    TOK_VAR_INPUT Zom_FB_Input_Decl TOK_END_VAR
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
    TOK_VAR_OUTPUT Zom_FB_Output_Decl TOK_END_VAR
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
    TOK_VAR_INOUT Zom_FB_Inout_Decl TOK_END_VAR
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
    TOK_VAR_STATIC Zom_FB_Static_Decl TOK_END_VAR
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
    TOK_BEGIN Zom_IL_Network
    {
      $$ = $2;
    }
    ;

// Function declaration 
Func_Decl:
    TOK_FUNCTION Derived_Func_Name ':' Func_Return_Value Version_Label 
    Zom_Func_General_Var_Decls Func_Body TOK_END_FUNCTION
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
    TOK_IDENTIFIER
    ;
    
Func_Return_Value:
    TOK_VOID
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
    TOK_VAR_INPUT Zom_Input_Decl TOK_END_VAR
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
    TOK_VAR_INOUT Zom_Inout_Decl TOK_END_VAR
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
    TOK_VAR_OUTPUT Zom_Output_Decl TOK_END_VAR
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
    TOK_VAR_TEMP Zom_Temp_Decl TOK_END_VAR
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
    TOK_VAR_CONSTANT Zom_Constant_Decl TOK_END_VAR
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
    TOK_BEGIN Zom_IL_Network
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
    TOK_NETWORK TOK_TITLE TOK_ASSIGN Opt_TITLE_VALUE Opt_Instruction_List
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_network);
      parser_stack($$).add_to_operands(std::move(parser_stack($4)), 
        std::move(parser_stack($5)));
    }
    ;
    
    
Opt_TITLE_VALUE:
    TOK_TITLE_VALUE
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
    
// Structured Text grammar
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
    Opt_Label Opt_Instruction ';'
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
    TOK_LABEL
    ;

Opt_Instruction:
    IL_Simple_Operation
    | IL_Invocation
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_instruction);
    }
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
    TOK_LOAD 
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_load);
    }
    | TOK_TRANSFER
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_transfer);
    }
    | TOK_NOP
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_nop);
    }
    | TOK_CONST_ADD
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_const_add);
    }
    | TOK_ACCU_INT_ADD
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_add);
    }
    | TOK_ACCU_INT_SUB
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_sub);
    }
    | TOK_ACCU_INT_MUL
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_mul);
    }
    | TOK_ACCU_INT_DIV
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_div);
    }
    | TOK_ACCU_INT_EQ
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_eq);
    }
    | TOK_ACCU_INT_NEQ
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_neq);
    }
    | TOK_ACCU_INT_GT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_gt);
    }
    | TOK_ACCU_INT_LT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_lt);
    }
    | TOK_ACCU_INT_GTE
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_gte);
    }
    | TOK_ACCU_INT_LTE
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_int_lte);
    }
    | TOK_ACCU_REAL_ADD
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_add);
    }
    | TOK_ACCU_REAL_SUB
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_sub);
    }
    | TOK_ACCU_REAL_MUL
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_mul);
    }
    | TOK_ACCU_REAL_DIV
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_div);
    }
    | TOK_ACCU_REAL_EQ
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_eq);
    }
    | TOK_ACCU_REAL_NEQ
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_neq);
    }
    | TOK_ACCU_REAL_GT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_gt);
    }
    | TOK_ACCU_REAL_LT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_lt);
    }
    | TOK_ACCU_REAL_GTE
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_gte);
    }
    | TOK_ACCU_REAL_LTE
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_real_lte);
    }
    | TOK_ACCU_DINT_ADD
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_add);
    }
    | TOK_ACCU_DINT_SUB
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_sub);
    }
    | TOK_ACCU_DINT_MUL
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_mul);
    }
    | TOK_ACCU_DINT_DIV
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_div);
    }
    | TOK_ACCU_DINT_EQ
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_eq);
    }
    | TOK_ACCU_DINT_NEQ
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_neq);
    }
    | TOK_ACCU_DINT_GT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_gt);
    }
    | TOK_ACCU_DINT_LT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_lt);
    }
    | TOK_ACCU_DINT_GTE
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_gte);
    }
    | TOK_ACCU_DINT_LTE
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_accu_dint_lte);
    }
    | TOK_AND 
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_and);
    }
    | TOK_AND_NOT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_and_not);
    } 
    | TOK_OR
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_or);
    } 
    | TOK_OR_NOT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_or_not);
    }  
    | TOK_XOR 
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_xor);
    }  
    | TOK_XOR_NOT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_xor_not);
    } 
    | TOK_AND_NESTED 
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_and_nested);
    }
    | TOK_AND_NOT_NESTED
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_and_not_nested);
    } 
    | TOK_OR_NESTED
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_or_nested);
    } 
    | TOK_OR_NOT_NESTED
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_or_not_nested);
    }  
    | TOK_XOR_NESTED 
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_xor_nested);
    }  
    | TOK_XOR_NOT_NESTED
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_xor_not_nested);
    }
    | TOK_NESTING_CLOSED
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_nesting_closed);
    }  
    | TOK_ASSIGN
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_assign);
    }
    | TOK_SET_RLO
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_set_rlo);
    }
    | TOK_CLR_RLO
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_clr_rlo);
    } 
    | TOK_SET
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_set);
    }
    | TOK_RESET
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_reset);
    } 
    | TOK_NOT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_not);
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
    TOK_INT_LITERAL
    | TOK_BOOL_LITERAL
    | TOK_REAL_LITERAL
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
    TOK_CALL
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
    '(' Oom_Param_Assignment TOK_NESTING_CLOSED
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
    Variable_Name TOK_ASSIGNMENT IL_Operand
    {
      newstack($$);
      parser_stack($$) = equal_exprt{std::move(parser_stack($1)), 
        std::move(parser_stack($3))};
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
    TOK_TAG Opt_Tag_List TOK_END_TAG
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
