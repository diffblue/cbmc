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
#include <util/std_expr.h>

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
%token TOK_VAR_OUTPUT           "VAR_OUTPUT"
%token TOK_END_VAR              "END_VAR"
%token TOK_NETWORK              "NETWORK"
%token TOK_TITLE                "TITLE"

/*** Siemens types ***********************************************************/
%token TOK_INT                  "Int"
%token TOK_DINT                 "DInt"
%token TOK_REAL                 "Real"
%token TOK_BOOL                 "Bool"
%token TOK_VOID                 "Void"

/*** Operators ***************************************************************/
%token TOK_LOAD                 "L"
%token TOK_TRANSFER             "T"
%token TOK_NOP                  "NOP"
%token TOK_AND                  "A"
%token TOK_AND_NOT              "AN"
%token TOK_OR                   "O"
%token TOK_OR_NOT               "ON"
%token TOK_XOR                  "X"
%token TOK_XOR_NOT              "XN"
%token TOK_CONST_ADD            "+"
%token TOK_ACCU_INT_ADD         "+I"
%token TOK_ACCU_INT_SUB         "-I"
%token TOK_ACCU_INT_MUL         "*I"
%token TOK_ACCU_INT_DIV         "/I"
%token TOK_ACCU_REAL_ADD        "+R"
%token TOK_ACCU_REAL_SUB        "-R"
%token TOK_ACCU_REAL_MUL        "*R"
%token TOK_ACCU_REAL_DIV        "/R"
%token TOK_ACCU_DINT_ADD        "+D"
%token TOK_ACCU_DINT_SUB        "-D"
%token TOK_ACCU_DINT_MUL        "*D"
%token TOK_ACCU_DINT_DIV        "/D"
%token TOK_ASSIGNMENT           ":="

/*** Value tokens ***/
%token TOK_INT_LITERAL
%token TOK_BOOL_LITERAL
%token TOK_REAL_LITERAL
%token TOK_IDENTIFIER
%token TOK_TITLE_VALUE
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
    | /* nothing */
    ;

// Variable and type declarations
Var_Decl_Init:
    Variable_List ':' Simple_Spec_Init 
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($3)));
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
      parser_stack($$).id(ID_statement_list_int);
    }
    ;

DInt_Type_Name:
    Sign_DInt_Type_Name
    ;

Sign_DInt_Type_Name:
    TOK_DINT
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_dint);
    }
    ;

Real_Type_Name:
    TOK_REAL
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_real);
    }
    ;
    
Bool_Type_Name:
    TOK_BOOL
    {
      $$ = $1;
      parser_stack($$).id(ID_statement_list_bool);
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
    TOK_VERSION ':' TOK_REAL_LITERAL 
    {
      $$ = $3;
      parser_stack($$).type().id(ID_statement_list_version);
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
    ;

FB_IO_Var_Decls:
    FB_Input_Decls 
    | FB_Output_Decls
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
    Var_Decl_Init
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
    Var_Decl_Init
    ;

FB_Body:
    TOK_BEGIN Oom_IL_Network
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
        std::move(parser_stack($5)));
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
    ;

IO_Var_Decls:
    Input_Decls 
    | Output_Decls
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
    
Func_Body:
    TOK_BEGIN Oom_IL_Network
    {
      $$ = $2;
    }
    ;
    
// Network declaration
Oom_IL_Network:
    Oom_IL_Network IL_Network 
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | IL_Network 
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_networks);
      parser_stack($$).add_to_operands(std::move(parser_stack($1)));
    }
    ;

IL_Network:
    TOK_NETWORK TOK_TITLE '=' Opt_TITLE_VALUE Opt_Instruction_List
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
    | IL_Expr
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

IL_Expr:
    IL_Expr_Operator '(' Opt_Operand Opt_Simple_Inst_List ')'
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_instruction);
      parser_stack($$).add_to_operands(std::move(parser_stack($3)), 
        std::move(parser_stack($4)));
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
    ;

IL_Operand:
    Constant
    | Variable_Access
    ;

Variable_Access:
    '#' Variable_Name
    {
      newstack($$);
      parser_stack($$) = 
        symbol_exprt::typeless(parser_stack($2).get(ID_value));
    }
    | Variable_Name
    ;
    
Constant:
    TOK_INT_LITERAL
    | TOK_BOOL_LITERAL
    ;

IL_Expr_Operator:
    TOK_AND 
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
    ;

IL_Simple_Inst_List:
    IL_Simple_Inst_List IL_Simple_Instruction
    {
      $$ = $1;
      parser_stack($$).add_to_operands(std::move(parser_stack($2)));
    }
    | IL_Simple_Instruction 
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_instructions);
      parser_stack($$).add_to_operands(std::move(parser_stack($1)));
    }
    ;

Opt_Simple_Inst_List:
    IL_Simple_Inst_List 
    | /* nothing */
    {
      newstack($$);
      parser_stack($$).id(ID_statement_list_instructions);
    }
    ;

IL_Simple_Instruction:
    IL_Simple_Operation';' 
    | IL_Expr';'
    ;
%%
