%{

/*
 * This parser is based on:
 *
 * c5.y, a ANSI-C grammar written by James A. Roskind.
 * "Portions Copyright (c) 1989, 1990 James A. Roskind".
 * (http://www.idiom.com/free-compilers/,
 * ftp://ftp.infoseek.com/ftp/pub/c++grammar/,
 * ftp://ftp.sra.co.jp/.a/pub/cmd/c++grammar2.0.tar.gz)
 */

#define PARSER ansi_c_parser

#include "ansi_c_parser.h"

int yyansi_clex();
extern char *yyansi_ctext;

#include "parser_static.inc"

#include "y.tab.h"

/*** token declaration **************************************************/
%}

/*** ANSI-C keywords ***/

%token TOK_AUTO      "auto"
%token TOK_BOOL      "bool"
%token TOK_COMPLEX   "complex"
%token TOK_BREAK     "break"
%token TOK_CASE      "case"
%token TOK_CHAR      "char"
%token TOK_CONST     "const"
%token TOK_CONTINUE  "continue"
%token TOK_DEFAULT   "default"
%token TOK_DO        "do"
%token TOK_DOUBLE    "double"
%token TOK_ELSE      "else"
%token TOK_ENUM      "enum"
%token TOK_EXTERN    "extern"
%token TOK_FLOAT     "float"
%token TOK_FOR       "for"
%token TOK_GOTO      "goto"
%token TOK_IF        "if"
%token TOK_INLINE    "inline"
%token TOK_INT       "int"
%token TOK_LONG      "long"
%token TOK_REGISTER  "register"
%token TOK_RESTRICT  "restrict"
%token TOK_RETURN    "return"
%token TOK_SHORT     "short"
%token TOK_SIGNED    "signed"
%token TOK_SIZEOF    "sizeof"
%token TOK_STATIC    "static"
%token TOK_STRUCT    "struct"
%token TOK_SWITCH    "switch"
%token TOK_TYPEDEF   "typedef"
%token TOK_UNION     "union"
%token TOK_UNSIGNED  "unsigned"
%token TOK_VOID      "void"
%token TOK_VOLATILE  "volatile"
%token TOK_WCHAR_T   "wchar_t"
%token TOK_WHILE     "while"

/*** multi-character operators ***/

%token TOK_ARROW     "->"
%token TOK_INCR      "++"
%token TOK_DECR      "--"
%token TOK_SHIFTLEFT "<<"
%token TOK_SHIFTRIGHT ">>"
%token TOK_LE        "<="
%token TOK_GE        ">="
%token TOK_EQ        "=="
%token TOK_NE        "!="
%token TOK_ANDAND    "&&"
%token TOK_OROR      "||"
%token TOK_ELLIPSIS  "..."

/*** modifying assignment operators ***/

%token TOK_MULTASSIGN  "*="
%token TOK_DIVASSIGN   "/="
%token TOK_MODASSIGN   "%="
%token TOK_PLUSASSIGN  "+="
%token TOK_MINUSASSIGN "-="
%token TOK_SHLASSIGN   "<<="
%token TOK_SHRASSIGN   ">>="
%token TOK_ANDASSIGN   "&="
%token TOK_XORASSIGN   "^="
%token TOK_ORASSIGN    "|="

/*** scanner parsed tokens (these have a value!) ***/

%token TOK_IDENTIFIER
%token TOK_TYPEDEFNAME
%token TOK_INTEGER
%token TOK_FLOATING
%token TOK_CHARACTER
%token TOK_STRING
%token TOK_ASM_STRING

/*** extensions ***/

%token TOK_INT8        "__int8"
%token TOK_INT16       "__int16"
%token TOK_INT32       "__int32"
%token TOK_INT64       "__int64"
%token TOK_PTR32       "__ptr32"
%token TOK_PTR64       "__ptr64"
%token TOK_TYPEOF      "typeof"
%token TOK_GCC_FLOAT128 "__float128"
%token TOK_GCC_INT128 "__int128"
%token TOK_GCC_DECIMAL32 "_Decimal32"
%token TOK_GCC_DECIMAL64 "_Decimal64"
%token TOK_GCC_DECIMAL128 "_Decimal128"
%token TOK_GCC_ASM     "__asm__"
%token TOK_GCC_ASM_PAREN "__asm__ (with parentheses)"
%token TOK_GCC_ATTRIBUTE_ALIGNED "aligned"
%token TOK_GCC_ATTRIBUTE_TRANSPARENT_UNION "transparent_union"
%token TOK_GCC_ATTRIBUTE_PACKED "packed"
%token TOK_GCC_ATTRIBUTE_VECTOR_SIZE "vector_size"
%token TOK_GCC_ATTRIBUTE_MODE "mode"
%token TOK_GCC_ATTRIBUTE_END ")"
%token TOK_GCC_LABEL   "__label__"
%token TOK_MSC_ASM     "__asm"
%token TOK_MSC_BASED   "__based"
%token TOK_CW_VAR_ARG_TYPEOF "_var_arg_typeof"
%token TOK_BUILTIN_VA_ARG "__builtin_va_arg"
%token TOK_GCC_BUILTIN_TYPES_COMPATIBLE_P "__builtin_types_compatible_p"
%token TOK_OFFSETOF    "__offsetof"
%token TOK_ALIGNOF     "__alignof__"
%token TOK_MSC_FINALLY "finally"
%token TOK_MSC_EXCEPT  "except"
%token TOK_MSC_LEAVE   "leave"
%token TOK_INTERFACE   "__interface"
%token TOK_CDECL       "__cdecl"
%token TOK_STDCALL     "__stdcall"
%token TOK_FASTCALL    "__fastcall"
%token TOK_CLRCALL     "__clrcall"
%token TOK_FORALL      "forall"
%token TOK_EXISTS      "exists"
%token TOK_ACSL_FORALL "\\forall"
%token TOK_ACSL_EXISTS "\\exists"
%token TOK_ARRAY_OF    "array_of"
%token TOK_CPROVER_BITVECTOR "__CPROVER_bitvector"
%token TOK_CPROVER_ATOMIC "__CPROVER_atomic"
%token TOK_CPROVER_BOOL "__CPROVER_bool"
%token TOK_IMPLIES     "==>"
%token TOK_EQUIVALENT  "<==>"
%token TOK_TRUE        "TRUE"
%token TOK_FALSE       "FALSE"
%token TOK_REAL        "__real__"
%token TOK_IMAG        "__imag__"
%token TOK_ALIGNAS     "_Alignas"
%token TOK_ATOMIC      "_Atomic"
%token TOK_GENERIC     "_Generic"
%token TOK_IMAGINARY   "_Imaginary"
%token TOK_NORETURN    "_Noreturn"
%token TOK_STATIC_ASSERT "_Static_assert"
%token TOK_THREAD_LOCAL "_Thread_local"
%token TOK_NULLPTR     "nullptr"
%token TOK_CONSTEXPR   "constexpr"

/*** special scanner reports ***/

%token TOK_SCANNER_ERROR /* used by scanner to report errors */
%token TOK_SCANNER_EOF   /* used by scanner to report end of import */

/*** these exist only for the benefit of the C++ frontend */

%token TOK_CATCH       "catch"
%token TOK_CLASS       "class"
%token TOK_DELETE      "delete"
%token TOK_DECLTYPE    "decltype"
%token TOK_EXPLICIT    "explicit"
%token TOK_FRIEND      "friend"
%token TOK_MUTABLE     "mutable"
%token TOK_NAMESPACE   "namespace"
%token TOK_NEW         "new"
%token TOK_OPERATOR    "operator"
%token TOK_PRIVATE     "private"
%token TOK_PROTECTED   "protected"
%token TOK_PUBLIC      "public"
%token TOK_TEMPLATE    "template"
%token TOK_THIS        "this"
%token TOK_THROW       "throw"
%token TOK_TYPEID      "typeid"
%token TOK_TYPENAME    "typename"
%token TOK_USING       "using"
%token TOK_VIRTUAL     "virtual"
%token TOK_TRY         "try"
%token TOK_SCOPE       "::"
%token TOK_DOTPM       ".*"
%token TOK_ARROWPM     "->*"
%token TOK_MSC_UNARY_TYPE_PREDICATE
%token TOK_MSC_BINARY_TYPE_PREDICATE
%token TOK_MSC_UUIDOF  "__uuidof"
%token TOK_MSC_IF_EXISTS "__if_exists"
%token TOK_MSC_IF_NOT_EXISTS "__if_not_exists"

/*** grammar selection ***/

%token TOK_PARSE_LANGUAGE
%token TOK_PARSE_EXPRESSION
%token TOK_PARSE_TYPE

/*** priority, associativity, etc. definitions **************************/

%start grammar

%expect 1 /* the famous "dangling `else'" ambiguity */
          /* results in one shift/reduce conflict   */
          /* that we don't want to be reported      */

%{
/************************************************************************/
/*** rules **************************************************************/
/************************************************************************/
%}
%%

/*** Grammar selection **************************************************/

grammar:
          TOK_PARSE_LANGUAGE translation_unit
        | TOK_PARSE_EXPRESSION comma_expression
        {
          ansi_c_declarationt ansi_c_declaration;
          ansi_c_declaration.value()=stack($2);
          PARSER.copy_item(ansi_c_declaration);
        }
        | TOK_PARSE_TYPE type_name
        {
          ansi_c_declarationt ansi_c_declaration;
          ansi_c_declaration.type()=
            static_cast<const typet &>(static_cast<const irept &>(stack($2)));
          ansi_c_declaration.set_is_type(true);
          PARSER.copy_item(ansi_c_declaration);
        }
        ;

/*** Token with values **************************************************/

identifier:
        TOK_IDENTIFIER
        ;

typedef_name:
        TOK_TYPEDEFNAME
        ;

integer:
        TOK_INTEGER
        ;

floating:
        TOK_FLOATING
        ;

character:
        TOK_CHARACTER
        ;

string:
        TOK_STRING
        ;

/*** Constants **********************************************************/

constant: integer
        | floating
        | character
        | string
        ;

/*** Expressions ********************************************************/

primary_expression:
          identifier
        | constant
        | '(' comma_expression ')'
        { $$ = $2; }
        | statement_expression
        | gcc_builtin_expressions
        | cw_builtin_expressions
        | offsetof
        | quantifier_expression
        | generic_selection
        ;

generic_selection:
          TOK_GENERIC '(' assignment_expression ',' generic_assoc_list ')'
        {
          init($$, ID_generic_selection);
          mto($$, $3);
          stack($$).add(ID_generic_associations).get_sub().swap(stack($5).add(ID_operands).get_sub());
        }
        ;

generic_assoc_list:
          generic_association
        {
          init($$); mto($$, $1);
        }
        | generic_assoc_list ',' generic_association
        {
          $$=$1; mto($$, $3);
        }
        ;

generic_association:
          type_name ':' assignment_expression
        {
          $$=$2;
          stack($$).id(ID_generic_association);
          stack($$).set(ID_type_arg, stack($1));
          stack($$).set(ID_value, stack($3));
        }
        | TOK_DEFAULT ':' assignment_expression
        {
          $$=$2;
          stack($$).id(ID_generic_association);
          stack($$).set(ID_type_arg, irept(ID_default));
          stack($$).set(ID_value, stack($3));
        }
        ;

gcc_builtin_expressions:
          TOK_BUILTIN_VA_ARG '(' assignment_expression ',' type_name ')'
        {
          $$=$1;
          stack($$).id(ID_gcc_builtin_va_arg);
          mto($$, $3);
          stack($$).type().swap(stack($5));
        }
        | TOK_GCC_BUILTIN_TYPES_COMPATIBLE_P '('
           type_name ',' type_name ')'
        {
          $$=$1;
          stack($$).id(ID_gcc_builtin_types_compatible_p);
          irept::subt &subtypes=stack($$).add(ID_subtypes).get_sub();
          subtypes.resize(2);
          subtypes[0].swap(stack($3));
          subtypes[1].swap(stack($5));
        }
        ;

cw_builtin_expressions:
          TOK_CW_VAR_ARG_TYPEOF '(' type_name ')'
        {
          $$=$1;
          stack($$).id(ID_cw_va_arg_typeof);
          stack($$).add(ID_type_arg).swap(stack($3));
        }
        ;

offsetof:
        TOK_OFFSETOF '(' type_name ',' offsetof_member_designator ')'
        {
          $$=$1;
          stack($$).id(ID_builtin_offsetof);
          stack($$).add(ID_type_arg).swap(stack($3));
          stack($$).add(ID_designator).swap(stack($5));
        }
        ;

offsetof_member_designator:
          member_name
        {
          init($$, ID_designated_initializer);
          stack($$).operands().resize(1);
          stack($$).op0().id(ID_member);
          stack($$).op0().location()=stack($1).location();
          stack($$).op0().set(ID_component_name, stack($1).get(ID_C_base_name));
        }
        | offsetof_member_designator '.' member_name
        {
          $$=$1;
          set($2, ID_member);
          stack($2).set(ID_component_name, stack($3).get(ID_C_base_name));
          mto($$, $2);
        }
        | offsetof_member_designator '[' comma_expression ']'
        {
          $$=$1;
          set($2, ID_index);
          mto($2, $3);
          mto($$, $2);
        }
        ;
          
quantifier_expression:
          TOK_FORALL compound_scope '{' declaration comma_expression '}'
        {
          init($$);
          stack($$).id(ID_forall);
          stack($$).location()=stack($1).location();
          mto($$, $4);
          mto($$, $5);
          PARSER.pop_scope();
        }
        | TOK_ACSL_FORALL compound_scope declaration primary_expression
        {
          init($$);
          stack($$).id(ID_forall);
          stack($$).location()=stack($1).location();
          mto($$, $3);
          mto($$, $4);
          PARSER.pop_scope();
        }
        | TOK_EXISTS compound_scope '{' declaration comma_expression '}'
        {
          init($$);
          stack($$).id(ID_exists);
          stack($$).location()=stack($1).location();
          mto($$, $4);
          mto($$, $5);
          PARSER.pop_scope();
        }
        | TOK_ACSL_EXISTS compound_scope declaration primary_expression
        {
          init($$);
          stack($$).id(ID_exists);
          stack($$).location()=stack($1).location();
          mto($$, $3);
          mto($$, $4);
          PARSER.pop_scope();
        }
        ;

statement_expression: '(' compound_statement ')'
        { init($$, ID_sideeffect);
          stack($$).set(ID_statement, ID_statement_expression);
          stack($$).location()=stack($1).location();
          mto($$, $2);
        }
        ;

postfix_expression:
          primary_expression
        | postfix_expression '[' comma_expression ']'
        { binary($$, $1, $2, ID_index, $3); }
        | postfix_expression '(' ')'
        { $$=$2;
          set($$, ID_sideeffect);
          stack($$).operands().resize(2);
          stack($$).op0().swap(stack($1));
          stack($$).op1().clear();
          stack($$).op1().id(ID_arguments);
          stack($$).set(ID_statement, ID_function_call);
        }
        | postfix_expression '(' argument_expression_list ')'
        { $$=$2;
          locationt location=stack($2).location();
          init($$, ID_sideeffect);
          stack($$).set(ID_statement, ID_function_call);
          stack($$).operands().resize(2);
          stack($$).op0().swap(stack($1));
          stack($$).op1().swap(stack($3));
          stack($$).op1().id(ID_arguments);
          stack($$).location()=location;
        }
        | postfix_expression '.' member_name
        { $$=$2;
          set($$, ID_member);
          mto($$, $1);
          stack($$).set(ID_component_name, stack($3).get(ID_C_base_name));
        }
        | postfix_expression TOK_ARROW member_name
        { $$=$2;
          set($$, ID_ptrmember);
          mto($$, $1);
          stack($$).set(ID_component_name, stack($3).get(ID_C_base_name));
        }
        | postfix_expression TOK_INCR
        { $$=$2;
          locationt location=stack($2).location();
          init($$, ID_sideeffect);
          mto($$, $1);
          stack($$).set(ID_statement, ID_postincrement);
          stack($$).location()=location;
        }
        | postfix_expression TOK_DECR
        { $$=$2;
          locationt location=stack($2).location();
          init($$, ID_sideeffect);
          mto($$, $1);
          stack($$).set(ID_statement, ID_postdecrement);
          stack($$).location()=location;
        }
        /* The following is a) GCC and b) ISO C 11 compliant */
        | '(' type_name ')' '{' initializer_list_opt '}'
        {
          exprt tmp(ID_initializer_list);
          tmp.location()=stack($4).location();
          tmp.operands().swap(stack($5).operands());
          $$=$1;
          set($$, ID_typecast);
          stack($$).move_to_operands(tmp);
          stack($$).type().swap(stack($2));
        }
        | '(' type_name ')' '{' initializer_list ',' '}'
        {
          // same as above
          exprt tmp(ID_initializer_list);
          tmp.location()=stack($4).location();
          tmp.operands().swap(stack($5).operands());
          $$=$1;
          set($$, ID_typecast);
          stack($$).move_to_operands(tmp);
          stack($$).type().swap(stack($2));
        }
        ;

member_name:
          identifier
        | typedef_name
        ;

argument_expression_list:
          assignment_expression
        {
          init($$, ID_expression_list);
          mto($$, $1);
        }
        | argument_expression_list ',' assignment_expression
        {
          $$=$1;
          mto($$, $3);
        }
        ;

unary_expression:
          postfix_expression
        | TOK_INCR unary_expression
        { $$=$1;
          set($$, ID_sideeffect);
          stack($$).set(ID_statement, ID_preincrement);
          mto($$, $2);
        }
        | TOK_DECR unary_expression
        { $$=$1;
          set($$, ID_sideeffect);
          stack($$).set(ID_statement, ID_predecrement);
          mto($$, $2);
        }
        | '&' cast_expression
        { $$=$1;
          set($$, ID_address_of);
          mto($$, $2);
        }
        | TOK_ANDAND identifier_or_typedef_name
        { $$=$1;
          irep_idt identifier=PARSER.lookup_label(stack($2).get(ID_C_base_name));
          set($$, ID_address_of);
          stack($$).operands().resize(1);
          stack($$).op0()=stack($2);
          stack($$).op0().id(ID_label);
          stack($$).op0().set(ID_identifier, identifier);
        }
        | '*' cast_expression
        { $$=$1;
          set($$, ID_dereference);
          mto($$, $2);
        }
        | '+' cast_expression
        { $$=$1;
          set($$, ID_unary_plus);
          mto($$, $2);
        }
        | '-' cast_expression
        { $$=$1;
          set($$, ID_unary_minus);
          mto($$, $2);
        }
        | '~' cast_expression
        { $$=$1;
          set($$, ID_bitnot);
          mto($$, $2);
        }
        | '!' cast_expression
        { $$=$1;
          set($$, ID_not);
          mto($$, $2);
        }
        | TOK_SIZEOF unary_expression
        { $$=$1;
          set($$, ID_sizeof);
          mto($$, $2);
        }
        | TOK_SIZEOF '(' type_name ')'
        { $$=$1;
          set($$, ID_sizeof);
          stack($$).add(ID_type_arg).swap(stack($3));
        }
        | TOK_ALIGNOF unary_expression
        { // note no parentheses for expressions, just like sizeof
          $$=$1;
          set($$, ID_alignof);
          mto($$, $2);
        }
        | TOK_ALIGNOF '(' type_name ')'
        {
          $$=$1;
          stack($$).id(ID_alignof);
          stack($$).add(ID_type_arg).swap(stack($3));
        }
        | TOK_REAL unary_expression
        { $$=$1;
          set($$, ID_complex_real);
          mto($$, $2);
        }
        | TOK_IMAG unary_expression
        { $$=$1;
          set($$, ID_complex_imag);
          mto($$, $2);
        }
        ;

cast_expression:
          unary_expression
        | '(' type_name ')' cast_expression
        {
          $$=$1;
          set($$, ID_typecast);
          mto($$, $4);
          stack($$).type().swap(stack($2));
        }
        ;

multiplicative_expression:
          cast_expression
        | multiplicative_expression '*' cast_expression
        { binary($$, $1, $2, ID_mult, $3); }
        | multiplicative_expression '/' cast_expression
        { binary($$, $1, $2, ID_div, $3); }
        | multiplicative_expression '%' cast_expression
        { binary($$, $1, $2, ID_mod, $3); }
        ;

additive_expression:
          multiplicative_expression
        | additive_expression '+' multiplicative_expression
        { binary($$, $1, $2, ID_plus, $3); }
        | additive_expression '-' multiplicative_expression
        { binary($$, $1, $2, ID_minus, $3); }
        ;

shift_expression:
          additive_expression
        | shift_expression TOK_SHIFTLEFT additive_expression
        { binary($$, $1, $2, ID_shl, $3); }
        | shift_expression TOK_SHIFTRIGHT additive_expression
        { binary($$, $1, $2, ID_shr, $3); }
        ;

relational_expression:
          shift_expression
        | relational_expression '<' shift_expression
        { binary($$, $1, $2, ID_lt, $3); }
        | relational_expression '>' shift_expression
        { binary($$, $1, $2, ID_gt, $3); }
        | relational_expression TOK_LE shift_expression
        { binary($$, $1, $2, ID_le, $3); }
        | relational_expression TOK_GE shift_expression
        { binary($$, $1, $2, ID_ge, $3); }
        ;

equality_expression:
          relational_expression
        | equality_expression TOK_EQ relational_expression
        { binary($$, $1, $2, ID_equal, $3); }
        | equality_expression TOK_NE relational_expression
        { binary($$, $1, $2, ID_notequal, $3); }
        ;

and_expression:
          equality_expression
        | and_expression '&' equality_expression
        { binary($$, $1, $2, ID_bitand, $3); }
        ;

exclusive_or_expression:
          and_expression
        | exclusive_or_expression '^' and_expression
        { binary($$, $1, $2, ID_bitxor, $3); }
        ;

inclusive_or_expression:
          exclusive_or_expression
        | inclusive_or_expression '|' exclusive_or_expression
        { binary($$, $1, $2, ID_bitor, $3); }
        ;

logical_and_expression:
          inclusive_or_expression
        | logical_and_expression TOK_ANDAND inclusive_or_expression
        { binary($$, $1, $2, ID_and, $3); }
        ;

logical_or_expression:
          logical_and_expression
        | logical_or_expression TOK_OROR logical_and_expression
        { binary($$, $1, $2, ID_or, $3); }
        ;

/* This is obviously non-standard, but inspired by Spec#. */
/* Implication is generally considered to be right-associative,
   and binds weaker than 'OR', and stronger than bi-implication. */
logical_implication_expression:
          logical_or_expression
        | logical_or_expression TOK_IMPLIES logical_implication_expression
        { binary($$, $1, $2, ID_implies, $3); }
        ;

/* This is obviously non-standard, but inspired by Spec#. */
/* Bi-Implication is generally considered to be left-associative,
   and binds weaker than '==>', and stronger than quantifiers. */
logical_equivalence_expression:
          logical_implication_expression
        | logical_equivalence_expression TOK_EQUIVALENT logical_implication_expression
        { binary($$, $1, $2, ID_equal, $3); }
        ;

conditional_expression:
          logical_equivalence_expression
        | logical_equivalence_expression '?' comma_expression ':' conditional_expression
        { $$=$2;
          stack($$).id(ID_if);
          mto($$, $1);
          mto($$, $3);
          mto($$, $5);
        }
        | logical_equivalence_expression '?' ':' conditional_expression
        { $$=$2;
          stack($$).id(ID_sideeffect);
          stack($$).set(ID_statement, ID_gcc_conditional_expression);
          mto($$, $1);
          mto($$, $4);
        }
        ;

assignment_expression:
          conditional_expression
        | cast_expression '=' assignment_expression
        { binary($$, $1, $2, ID_sideeffect, $3); stack($$).set(ID_statement, ID_assign); }
        | cast_expression TOK_MULTASSIGN assignment_expression
        { binary($$, $1, $2, ID_sideeffect, $3); stack($$).set(ID_statement, ID_assign_mult); }
        | cast_expression TOK_DIVASSIGN assignment_expression
        { binary($$, $1, $2, ID_sideeffect, $3); stack($$).set(ID_statement, ID_assign_div); }
        | cast_expression TOK_MODASSIGN assignment_expression
        { binary($$, $1, $2, ID_sideeffect, $3); stack($$).set(ID_statement, ID_assign_mod); }
        | cast_expression TOK_PLUSASSIGN assignment_expression
        { binary($$, $1, $2, ID_sideeffect, $3); stack($$).set(ID_statement, ID_assign_plus); }
        | cast_expression TOK_MINUSASSIGN assignment_expression
        { binary($$, $1, $2, ID_sideeffect, $3); stack($$).set(ID_statement, ID_assign_minus); }
        | cast_expression TOK_SHLASSIGN assignment_expression
        { binary($$, $1, $2, ID_sideeffect, $3); stack($$).set(ID_statement, ID_assign_shl); }
        | cast_expression TOK_SHRASSIGN assignment_expression
        { binary($$, $1, $2, ID_sideeffect, $3); stack($$).set(ID_statement, ID_assign_shr); }
        | cast_expression TOK_ANDASSIGN assignment_expression
        { binary($$, $1, $2, ID_sideeffect, $3); stack($$).set(ID_statement, ID_assign_bitand); }
        | cast_expression TOK_XORASSIGN assignment_expression
        { binary($$, $1, $2, ID_sideeffect, $3); stack($$).set(ID_statement, ID_assign_bitxor); }
        | cast_expression TOK_ORASSIGN assignment_expression
        { binary($$, $1, $2, ID_sideeffect, $3); stack($$).set(ID_statement, ID_assign_bitor); }
        ;

comma_expression:
          assignment_expression
        | comma_expression ',' assignment_expression
        { binary($$, $1, $2, ID_comma, $3); }
        ;

constant_expression:
        assignment_expression
        ;

comma_expression_opt:
        /* nothing */
        { init($$); stack($$).make_nil(); }
        | comma_expression
        ;

/*** Declarations *******************************************************/

declaration:
          declaration_specifier ';'
        {
          // type only, no identifier!
          codet decl(ID_decl_type);
          decl.add(ID_type_arg).swap(stack($1));
          init($$);
          stack($$).move_to_operands(decl);
        }
        | type_specifier ';'
        {
          // type only, no identifier!
          codet decl(ID_decl_type);
          decl.add(ID_type_arg).swap(stack($1));
          init($$);
          stack($$).move_to_operands(decl);
        }
        | declaring_list ';'
        | default_declaring_list ';'
        | static_assert_declaration ';'
        ;
        
static_assert_declaration:
          TOK_STATIC_ASSERT '(' assignment_expression ',' assignment_expression ')'
        {
          mto($1, $3);
          mto($1, $5);
          stack($1).id(ID_code);
          stack($1).set(ID_statement, ID_static_assert);
          init($$);
          mto($$, $1);
        }
        ;

default_declaring_list:
          declaration_qualifier_list identifier_declarator
          {
            init($$);
            PARSER.new_declaration(stack($1), stack($2), stack($$));
            PARSER.copy_item(to_ansi_c_declaration(stack($$)));
          }
          initializer_opt
        {
          init($$);
          stack($$).add(ID_type)=stack($1);
          decl_statement($$, $3, $4);
        }
        | type_qualifier_list identifier_declarator
          {
            init($$);
            PARSER.new_declaration(stack($1), stack($2), stack($$));
            PARSER.copy_item(to_ansi_c_declaration(stack($$)));
          }
          initializer_opt
        {
          init($$);
          stack($$).add(ID_type)=stack($1);
          decl_statement($$, $3, $4);
        }
        | default_declaring_list ',' identifier_declarator
          {
            init($$);
            const irept &t=stack($1).find(ID_type);
            PARSER.new_declaration(t, stack($3), stack($$));
            PARSER.copy_item(to_ansi_c_declaration(stack($$)));
          }
          initializer_opt
        {
          $$=$1;
          decl_statement($$, $4, $5);
        }
        ;

post_declarator_attribute:
          TOK_GCC_ASM_PAREN volatile_or_goto_opt '(' gcc_asm_commands ')'
        {
          $$=$1;
          stack($$).id(ID_asm);
        }
        | gcc_type_attribute
        ;

post_declarator_attributes:
          post_declarator_attributes post_declarator_attribute
        {
          $$=$1;
          merge_types($1, $2);
        }
        | post_declarator_attribute
        ;

post_declarator_attributes_opt:
          /* nothing */
        {
          init($$);
        }
        | post_declarator_attributes
        ;

declaring_list:
          declaration_specifier declarator
          post_declarator_attributes_opt
          {
            // the symbol has to be visible during initialization
            merge_types($1, $3); // type attribute
            init($$);
            PARSER.new_declaration(stack($1), stack($2), stack($$));
            PARSER.copy_item(to_ansi_c_declaration(stack($$)));
          }
          initializer_opt
        {
          init($$);
          stack($$).add(ID_type)=stack($1); // save for later
          decl_statement($$, $4, $5);
        }
        | type_specifier declarator
          post_declarator_attributes_opt
          {
            // the symbol has to be visible during initialization
            merge_types($1, $3); // type attribute
            init($$);
            PARSER.new_declaration(stack($1), stack($2), stack($$));
            PARSER.copy_item(to_ansi_c_declaration(stack($$)));
          }
          initializer_opt
        {
          init($$);
          stack($$).add(ID_type)=stack($1); // save for later
          decl_statement($$, $4, $5);
        }
        | declaring_list ',' declarator
          post_declarator_attributes_opt
          {
            init($$);
            irept t=stack($1).find(ID_type);
            merge_types(t, stack($4)); // type attribute
            PARSER.new_declaration(t, stack($3), stack($$));
            PARSER.copy_item(to_ansi_c_declaration(stack($$)));
          }
          initializer_opt
        {
          $$=$1;
          decl_statement($$, $5, $6);
        }
        ;

declaration_specifier:
          basic_declaration_specifier
        | sue_declaration_specifier
        | typedef_declaration_specifier
        | typeof_declaration_specifier
        ;

type_specifier:
          basic_type_specifier
        | sue_type_specifier
        | typedef_type_specifier
        | typeof_type_specifier
        ;

declaration_qualifier_list:
          storage_class
        | type_qualifier_list storage_class
        {
          $$=$1;
          merge_types($$, $2);
        }
        | gcc_type_attribute
        | declaration_qualifier_list gcc_type_attribute
        {
          $$=$1;
          merge_types($$, $2);
        }
        | declaration_qualifier_list declaration_qualifier
        {
          $$=$1;
          merge_types($$, $2);
        }
        ;

type_qualifier_list:
          type_qualifier
        | type_qualifier_list type_qualifier
        {
          $$=$1;
          merge_types($$, $2);
        }
        /* The following is to allow mixing of type attributes with
           type qualifiers, but the list has to start with a
           proper type qualifier. */
        | type_qualifier_list gcc_type_attribute
        {
          $$=$1;
          merge_types($$, $2);
        }
        ;

attribute_type_qualifier_list:
          attribute_or_type_qualifier
        | type_qualifier_list attribute_or_type_qualifier
        {
          $$=$1;
          merge_types($$, $2);
        }
        ;

declaration_qualifier:
          storage_class
        | type_qualifier
        ;

type_qualifier:
          TOK_ATOMIC   { $$=$1; set($$, ID_atomic); }
        | TOK_CONST    { $$=$1; set($$, ID_const); }
        | TOK_RESTRICT { $$=$1; set($$, ID_restrict); }
        | TOK_VOLATILE { $$=$1; set($$, ID_volatile); }
        | TOK_CPROVER_ATOMIC { $$=$1; set($$, ID_cprover_atomic); }
        | TOK_PTR32    { $$=$1; set($$, ID_ptr32); }
        | TOK_PTR64    { $$=$1; set($$, ID_ptr64); }
        | TOK_MSC_BASED '(' comma_expression ')' { $$=$1; set($$, ID_msc_based); }
        ;

attribute_or_type_qualifier:
          type_qualifier
        | gcc_type_attribute
        ;

basic_declaration_specifier:
          declaration_qualifier_list basic_type_name gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | basic_type_specifier storage_class gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | basic_declaration_specifier declaration_qualifier gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | basic_declaration_specifier basic_type_name gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        ;

basic_type_specifier:
          basic_type_name gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2); // type attribute
        }
        | type_qualifier_list basic_type_name gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | basic_type_specifier type_qualifier
        {
          $$=$1;
          merge_types($$, $2);
        }
        | basic_type_specifier basic_type_name gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        ;

/* no gcc type attributes after the following! */
sue_declaration_specifier:
          declaration_qualifier_list elaborated_type_name
        {
          $$=$1;
          merge_types($$, $2);
        }
        | sue_type_specifier storage_class
        {
          $$=$1;
          merge_types($$, $2);
        }
        | sue_declaration_specifier declaration_qualifier
        {
          $$=$1;
          merge_types($$, $2);
        }
        ;

/* no gcc type attributes after the following! */
sue_type_specifier:
          elaborated_type_name
        | type_qualifier_list elaborated_type_name
        {
          $$=$1;
          merge_types($$, $2);
        }
        | sue_type_specifier type_qualifier
        {
          $$=$1;
          merge_types($$, $2);
        }
        ;

typedef_declaration_specifier:
          typedef_type_specifier storage_class gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | declaration_qualifier_list typedef_name gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | typedef_declaration_specifier declaration_qualifier gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        ;

typeof_declaration_specifier:
          typeof_type_specifier storage_class gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | declaration_qualifier_list typeof_specifier gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | typeof_declaration_specifier declaration_qualifier gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        ;

typedef_type_specifier:
          typedef_name gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2); // type attribute
        }
        | type_qualifier_list typedef_name gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | typedef_type_specifier type_qualifier gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        ;

typeof_specifier:
          TOK_TYPEOF '(' comma_expression ')'
        { $$ = $1;
          stack($$).id(ID_typeof);
          mto($$, $3);
        }
        | TOK_TYPEOF '(' type_name ')'
        { $$ = $1;
          stack($$).id(ID_typeof);
          stack($$).set(ID_type_arg, stack($3));
        }
        ;

typeof_type_specifier:
          typeof_specifier
        | type_qualifier_list typeof_specifier
        {
          $$=$1;
          merge_types($$, $2);
        }
        | type_qualifier_list typeof_specifier type_qualifier_list
        {
          $$=$1;
          merge_types($$, $3);
          merge_types($$, $2);
        }
        | typeof_specifier type_qualifier_list
        {
          $$=$2;
          merge_types($$, $1);
        }
        ;

/*
gcc_attribute_expression_list:
          assignment_expression
        {
          init($$, ID_expression_list);
          mto($$, $1);
        }
        | gcc_attribute_expression_list ',' assignment_expression
        {
          $$=$1;
          mto($$, $3);
        }
        ;
*/

/*
gcc_attribute_expression_list_opt:
*/
          /* empty */
/*
        {
          init($$, ID_expression_list);
        }
        | gcc_attribute_expression_list
        ;
*/

/*
gcc_attribute_parameters:
          '(' gcc_attribute_expression_list_opt ')'
        ;
*/

storage_class:
          TOK_TYPEDEF      { $$=$1; set($$, ID_typedef); }
        | TOK_EXTERN       { $$=$1; set($$, ID_extern); }
        | TOK_STATIC       { $$=$1; set($$, ID_static); }
        | TOK_AUTO         { $$=$1; set($$, ID_auto); }
        | TOK_REGISTER     { $$=$1; set($$, ID_register); }
        | TOK_INLINE       { $$=$1; set($$, ID_inline); }
        | TOK_THREAD_LOCAL { $$=$1; set($$, ID_thread_local); }
        | TOK_GCC_ASM      { $$=$1; set($$, ID_asm); }
        ;

basic_type_name:
          TOK_INT      { $$=$1; set($$, ID_int); }
        | TOK_INT8     { $$=$1; set($$, ID_int8); }
        | TOK_INT16    { $$=$1; set($$, ID_int16); }
        | TOK_INT32    { $$=$1; set($$, ID_int32); }
        | TOK_INT64    { $$=$1; set($$, ID_int64); }
        | TOK_CHAR     { $$=$1; set($$, ID_char); }
        | TOK_SHORT    { $$=$1; set($$, ID_short); }
        | TOK_LONG     { $$=$1; set($$, ID_long); }
        | TOK_FLOAT    { $$=$1; set($$, ID_float); }
        | TOK_GCC_FLOAT128 { $$=$1; set($$, ID_gcc_float128); }
        | TOK_GCC_INT128 { $$=$1; set($$, ID_gcc_int128); }
        | TOK_GCC_DECIMAL32 { $$=$1; set($$, ID_gcc_decimal32); }
        | TOK_GCC_DECIMAL64 { $$=$1; set($$, ID_gcc_decimal64); }
        | TOK_GCC_DECIMAL128 { $$=$1; set($$, ID_gcc_decimal128); }
        | TOK_DOUBLE   { $$=$1; set($$, ID_double); }
        | TOK_SIGNED   { $$=$1; set($$, ID_signed); }
        | TOK_UNSIGNED { $$=$1; set($$, ID_unsigned); }
        | TOK_VOID     { $$=$1; set($$, ID_void); }
        | TOK_BOOL     { $$=$1; set($$, ID_bool); }
        | TOK_COMPLEX  { $$=$1; set($$, ID_complex); }
        | TOK_CPROVER_BITVECTOR '[' comma_expression ']'
        {
          $$=$1;
          set($$, ID_bv);
          stack($$).add(ID_size).swap(stack($3));
        }
        | TOK_CPROVER_BOOL { $$=$1; set($$, ID_proper_bool); }
        ;

elaborated_type_name:
          aggregate_name
        | enum_name
        | array_of_construct
        ;
        
array_of_construct:
          TOK_ARRAY_OF '<' type_name '>'
        { $$=$1; ((typet &)stack($$)).subtype().swap(stack($2)); }
        ;

aggregate_name:
          aggregate_key
          gcc_type_attribute_opt
          {
            // an anon struct/union
            exprt symbol(ID_symbol);
            symbol.set(ID_C_base_name, PARSER.get_anon_name());

            init($$);
            PARSER.new_declaration(stack($1), symbol, stack($$), true);
          }
          '{' member_declaration_list_opt '}'
          gcc_type_attribute_opt
        {
          typet &type=to_ansi_c_declaration(stack($3)).type();
          type.add(ID_components).get_sub().swap(
            stack($5).add(ID_operands).get_sub());

          // throw in the gcc attributes
          merge_types(type, stack($2));
          merge_types(type, stack($7));

          // grab symbol
          init($$, ID_symbol);
          stack($$).set(ID_identifier, to_ansi_c_declaration(stack($3)).get_name());
          stack($$).location()=to_ansi_c_declaration(stack($3)).location();
          PARSER.copy_item(to_ansi_c_declaration(stack($3)));
        }
        | aggregate_key
          gcc_type_attribute_opt
          identifier_or_typedef_name
          {
            // a struct/union with tag
            init($$);
            PARSER.new_declaration(stack($1), stack($3), stack($$), true);
            
            // announce the tag before the members
            ansi_c_declarationt tmp=to_ansi_c_declaration(stack($$)); // copy!
            tmp.type().id("incomplete_"+stack($1).id_string());
            assert(tmp.id()==ID_declaration);
            PARSER.copy_item(tmp);            
          }
          '{' member_declaration_list_opt '}'
          gcc_type_attribute_opt
        {
          typet &type=stack($4).type();
          type.add(ID_components).get_sub().swap(
            stack($6).add(ID_operands).get_sub());

          // throw in the gcc attributes
          merge_types(type, stack($2));
          merge_types(type, stack($8));

          // grab symbol
          init($$, ID_symbol);
          stack($$).set(ID_identifier, stack($4).get(ID_name));
          stack($$).location()=stack($4).location();
          PARSER.copy_item(to_ansi_c_declaration(stack($4)));
        }
        | aggregate_key
          gcc_type_attribute_opt
          identifier_or_typedef_name
          gcc_type_attribute_opt
        {
          do_tag($1, $3);
          $$=$3;
          // type attributes
          merge_types($$, $2);
          merge_types($$, $4);
        }
        ;

aggregate_key:
          TOK_STRUCT
        { $$=$1; set($$, ID_struct); }
        | TOK_UNION
        { $$=$1; set($$, ID_union); }
        ;
        
gcc_type_attribute_opt:
          /* empty */
        {
          init($$);
        }
        | gcc_type_attribute_list
        ;

gcc_type_attribute_list:
          gcc_type_attribute
        | gcc_type_attribute_list gcc_type_attribute
        {
          merge_types($1, $2);
        }
        ;

gcc_type_attribute:
          TOK_GCC_ATTRIBUTE_PACKED TOK_GCC_ATTRIBUTE_END
        { $$=$1; set($$, ID_packed); }
        | TOK_GCC_ATTRIBUTE_TRANSPARENT_UNION TOK_GCC_ATTRIBUTE_END
        { $$=$1; set($$, ID_transparent_union); }
        | TOK_GCC_ATTRIBUTE_VECTOR_SIZE '(' comma_expression ')' TOK_GCC_ATTRIBUTE_END
        { $$=$1; set($$, ID_vector); stack($$).add(ID_size)=stack($3); }
        | TOK_GCC_ATTRIBUTE_ALIGNED TOK_GCC_ATTRIBUTE_END
        { $$=$1; set($$, ID_aligned); }
        | TOK_GCC_ATTRIBUTE_ALIGNED '(' comma_expression ')' TOK_GCC_ATTRIBUTE_END
        { $$=$1; set($$, ID_aligned); stack($$).set(ID_size, stack($3)); }
        | TOK_GCC_ATTRIBUTE_MODE '(' identifier ')' TOK_GCC_ATTRIBUTE_END
        { $$=$1; set($$, ID_gcc_attribute_mode); stack($$).set(ID_size, stack($3).get(ID_identifier)); }
        ;

member_declaration_list_opt:
                  /* Nothing */
        {
          init($$, ID_declaration_list);
        }
        | member_declaration_list
        ;

member_declaration_list:
          member_declaration
        | member_declaration_list member_declaration
        {
          assert(stack($1).id()==ID_declaration_list);
          assert(stack($2).id()==ID_declaration_list);
          $$=$1;
          Forall_operands(it, stack($2))
            stack($$).move_to_operands(*it);
          stack($2).clear();
        }
        ;

member_declaration:
          member_declaring_list ';'
        | member_default_declaring_list ';'
        | ';' /* empty declaration */
        {
          init($$, ID_declaration_list);
        }
        | static_assert_declaration ';'
        {
          init($$, ID_declaration_list);
          assert(stack($1).operands().size()==1);
          stack($$).move_to_operands(stack($1).op0());
        }
        ;

member_default_declaring_list:
          gcc_type_attribute_opt
          type_qualifier_list
          member_identifier_declarator
        {
          merge_types($2, $1); // type attribute

          init($$, ID_declaration_list);

          exprt declaration;
          PARSER.new_declaration(stack($2), stack($3), declaration, false, false);

          stack($$).move_to_operands(declaration);
        }
        | member_default_declaring_list ',' member_identifier_declarator
        {
          exprt declaration;
          PARSER.new_declaration(stack($1), stack($3), declaration, false, false);

          $$=$1;
          stack($$).move_to_operands(declaration);
        }
        ;

member_declaring_list:
          gcc_type_attribute_opt
          type_specifier
          member_declarator
        {
          // TODO merge_types($2, $1); // type attribute

          init($$, ID_declaration_list);

          // save the type_specifier for later
          stack($$).add(ID_type)=stack($2);

          exprt declaration;
          PARSER.new_declaration(stack($2), stack($3), declaration, false, false);

          stack($$).move_to_operands(declaration);
        }
        | member_declaring_list ',' member_declarator
        {
          exprt declaration;

          irept declaration_type=stack($1).find(ID_type);
          PARSER.new_declaration(declaration_type, stack($3), declaration, false, false);

          $$=$1;
          stack($$).move_to_operands(declaration);
        }
        ;

member_declarator:
          declarator bit_field_size_opt gcc_type_attribute_opt
        {
          $$=$1;

          if(stack($2).is_not_nil())
            make_subtype($$, $2);

          if(stack($3).is_not_nil()) // type attribute
          {
            merge_types(stack($3), stack($$));
            stack($$).swap(stack($3));
          }
        }
        | /* empty */
        {
          init($$, ID_abstract);
        }
        | bit_field_size gcc_type_attribute_opt
        {
          $$=$1;
          stack($$).add(ID_subtype)=irept(ID_abstract);

          if(stack($2).is_not_nil()) // type attribute
          {
            merge_types(stack($2), stack($$));
            stack($$).swap(stack($2));
          }
        }
        ;

member_identifier_declarator:
          identifier_declarator bit_field_size_opt gcc_type_attribute_opt
        {
          $$=$1;
          if(stack($2).is_not_nil())
            make_subtype($$, $2);
          
          if(stack($3).is_not_nil()) // type attribute
          {
            merge_types(stack($3), stack($$));
            stack($$).swap(stack($3));
          }
        }
        | bit_field_size gcc_type_attribute_opt
        {
          $$=$1;
          stack($$).add(ID_subtype)=irept(ID_abstract);

          if(stack($2).is_not_nil()) // type attribute
          {
            merge_types(stack($2), stack($$));
            stack($$).swap(stack($2));
          }
        }
        ;

bit_field_size_opt:
        /* nothing */
        {
          init($$, ID_nil);
        }
        | bit_field_size
        ;

bit_field_size:
        ':' constant_expression
        {
          $$=$1;
          set($$, ID_c_bitfield);
          stack($$).set(ID_size, stack($2));
          stack($$).add(ID_subtype).id(ID_abstract);
        }
        ;

enum_name:
          enum_key
          gcc_type_attribute_opt
          {
            // an anon enum, we want that to be visible before the
            // members
            exprt symbol(ID_symbol);
            symbol.set(ID_C_base_name, PARSER.get_anon_name());

            init($$);
            PARSER.new_declaration(stack($1), symbol, stack($$), true);
            PARSER.copy_item(to_ansi_c_declaration(stack($$)));
          }
          '{' enumerator_list '}'
          gcc_type_attribute_opt
        {
          // grab symbol
          init($$, ID_symbol);
          stack($$).set(ID_identifier, stack($3).get(ID_name));
          stack($$).location()=stack($3).location();

          // throw in the gcc attributes
          merge_types($$, $2);
          merge_types($$, $7);

          do_enum_members((const typet &)stack($$), stack($5));
        }
        | enum_key
          gcc_type_attribute_opt
          identifier_or_typedef_name
          {
            // we want the tag to be visible before the members
            init($$);
            PARSER.new_declaration(stack($1), stack($3), stack($$), true);
            PARSER.copy_item(to_ansi_c_declaration(stack($$)));
          }
          '{' enumerator_list '}'
          gcc_type_attribute_opt
        {
          // grab symbol
          init($$, ID_symbol);
          stack($$).set(ID_identifier, stack($4).get(ID_name));
          stack($$).location()=stack($4).location();

          // throw in the gcc attributes
          merge_types($$, $2);
          merge_types($$, $8);

          do_enum_members((const typet &)stack($$), stack($6));
        }
        | enum_key
          gcc_type_attribute_opt
          identifier_or_typedef_name
        {
          do_tag($1, $3);
          $$=$3;
          merge_types($$, $2);
        }
        ;
        
enum_key: TOK_ENUM
        {
          $$=$1;
          set($$, ID_c_enum);
        }
        ;

enumerator_list:
          enumerator_declaration
        {
          init($$);
          mto($$, $1);
        }
        | enumerator_list ',' enumerator_declaration
        {
          $$=$1;
          mto($$, $3);
        }
        | enumerator_list ','
        {
          $$=$1;
        }
        ;

enumerator_declaration:
          identifier_or_typedef_name enumerator_value_opt
        {
          // enum constants in C have signed int type,
          // not the enum type!
          init($$);
          irept type(ID_int);
          PARSER.new_declaration(type, stack($1), stack($$));
          stack($$).set(ID_is_macro, true);
          stack($$).add(ID_value).swap(stack($2));
        }
        ;

enumerator_value_opt:
        /* nothing */
        {
          init($$);
          stack($$).make_nil();
        }
        | '=' constant_expression
        {
          $$=$2;
        }
        ;

parameter_type_list:
          parameter_list
        | parameter_list ',' TOK_ELLIPSIS
        {
          typet tmp(ID_ellipsis);
          $$=$1;
          ((typet &)stack($$)).move_to_subtypes(tmp);
        }
        ;

KnR_parameter_list:
          KnR_parameter
        {
          init($$, ID_arguments);
          mts($$, $1);
        }
        | KnR_parameter_list ',' KnR_parameter
        {
          $$=$1;
          mts($$, $3);
        }
        ;

KnR_parameter: identifier
        {
          init($$);
          irept type(ID_KnR);
          PARSER.new_declaration(type, stack($1), stack($$));
        }
        ;

parameter_list:
          parameter_declaration
        {
          init($$, ID_arguments);
          mts($$, $1);
        }
        | parameter_list ',' parameter_declaration
        {
          $$=$1;
          mts($$, $3);
        }
        ;

parameter_declaration:
          declaration_specifier
        {
          init($$);
          exprt declarator=exprt(ID_abstract);
          PARSER.new_declaration(stack($1), declarator, stack($$));
        }
        | declaration_specifier parameter_abstract_declarator
        {
          init($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
        }
        | declaration_specifier identifier_declarator gcc_type_attribute_opt
        {
          init($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
        }
        | declaration_specifier parameter_typedef_declarator
        {
          // the second tree is really the argument -- not part
          // of the type!
          init($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
        }
        | declaration_qualifier_list
        {
          init($$);
          exprt declarator=exprt(ID_abstract);
          PARSER.new_declaration(stack($1), declarator, stack($$));
        }
        | declaration_qualifier_list parameter_abstract_declarator
        {
          init($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
        }
        | declaration_qualifier_list identifier_declarator gcc_type_attribute_opt
        {
          init($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
        }
        | type_specifier
        {
          init($$);
          exprt declarator=exprt(ID_abstract);
          PARSER.new_declaration(stack($1), declarator, stack($$));
        }
        | type_specifier parameter_abstract_declarator
        {
          init($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
        }
        | type_specifier identifier_declarator gcc_type_attribute_opt
        {
          init($$);
          stack($1), stack($2), stack($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
        }
        | type_specifier parameter_typedef_declarator
        {
          // the second tree is really the argument -- not part
          // of the type!
          init($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
        }
        | type_qualifier_list
        {
          init($$);
          exprt declarator=exprt(ID_abstract);
          PARSER.new_declaration(stack($1), declarator, stack($$));
        }
        | type_qualifier_list parameter_abstract_declarator
        {
          init($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
        }
        | type_qualifier_list identifier_declarator gcc_type_attribute_opt
        {
          init($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
        }
        ;

identifier_or_typedef_name:
          identifier
        | typedef_name
        ;

type_name:
          type_specifier
        | type_specifier abstract_declarator
        {
          $$=$1;
          make_subtype($$, $2);
        }
        | type_qualifier_list
        | type_qualifier_list abstract_declarator
        {
          $$=$1;
          make_subtype($$, $2);
        }
        ;

initializer_opt:
        /* nothing */
        {
          newstack($$);
          stack($$).make_nil();
        }
        | '=' initializer
        { $$ = $2; }
        ;

/* note: the following has been changed from the ANSI-C grammar:	*/
/*	- an initializer is not an assignment_expression,		*/
/*	  but a constant_expression					*/
/*	  (which probably is the case anyway for 99.9% of C programs)	*/

initializer:
          constant_expression        /* was: assignment_expression */
        | '{' initializer_list_opt '}'
        {
          $$=$1;
          set($$, ID_initializer_list);
          stack($$).operands().swap(stack($2).operands());
        }
        | '{' initializer_list ',' '}'
        {
          $$=$1;
          set($$, ID_initializer_list);
          stack($$).operands().swap(stack($2).operands());
        }
        ;

initializer_list:
          designated_initializer
        {
          $$=$1;
          exprt tmp;
          tmp.swap(stack($$));
          stack($$).clear();
          stack($$).move_to_operands(tmp);
        }
        | initializer_list ',' designated_initializer
        {
          $$=$1;
          mto($$, $3);
        }
        ;

initializer_list_opt:
          initializer_list
        | /* nothing */
        {
          init($$);
          set($$, ID_initializer_list);
          stack($$).operands().clear();
        }
        ;

designated_initializer:
          initializer
        | designator '=' initializer
        {
          $$=$2;
          stack($$).id(ID_designated_initializer);
          stack($$).add(ID_designator).swap(stack($1));
          mto($$, $3);
        }
        /* the following two are obsolete GCC extensions */
        | designator initializer
        {
          init($$, ID_designated_initializer);
          stack($$).add(ID_designator).swap(stack($1));
          mto($$, $2);
        }
        | member_name ':' initializer
        {
          // yet another GCC speciality
          $$=$2;
          stack($$).id(ID_designated_initializer);
          exprt designator;
          exprt member(ID_member);
          member.set(ID_component_name, stack($1).get(ID_C_base_name));
          designator.move_to_operands(member);
          stack($$).add(ID_designator).swap(designator);
          mto($$, $3);
        }
        ;

designator:
          '.' member_name
        {
          init($$);
          stack($1).id(ID_member);
          stack($1).set(ID_component_name, stack($2).get(ID_C_base_name));
          mto($$, $1);
        }
        | '[' comma_expression ']'
        {
          init($$);
          stack($1).id(ID_index);
          mto($1, $2);
          mto($$, $1);
        }
        | '[' comma_expression TOK_ELLIPSIS comma_expression ']'
        {
          // TODO
          init($$);
          stack($1).id(ID_index);
          mto($1, $2);
          mto($$, $1);
        }
        | designator '[' comma_expression ']'
        {
          $$=$1;
          stack($2).id(ID_index);
          mto($2, $3);
          mto($$, $2);
        }
        | designator '[' comma_expression TOK_ELLIPSIS comma_expression ']'
        {
          // TODO
          $$=$1;
          stack($2).id(ID_index);
          mto($2, $3);
          mto($$, $2);
        }
        | designator '.' member_name
        {
          $$=$1;
          stack($2).id(ID_member);
          stack($2).set(ID_component_name, stack($3).get(ID_C_base_name));
          mto($$, $2);
        }
        ;

/*** Statements *********************************************************/

statement:
          labeled_statement
        | compound_statement
        | declaration_statement
        | expression_statement
        | selection_statement
        | iteration_statement
        | jump_statement
        | gcc_asm_statement
        | gcc_local_label_statement
        | msc_asm_statement
        | msc_seh_statement
        ;

declaration_statement:
          declaration
        {
          init($$);
          statement($$, ID_decl_block);
          stack($$).operands().swap(stack($1).operands());
        }
        ;

labeled_statement:
          identifier_or_typedef_name ':' statement
        {
          $$=$2;
          statement($$, ID_label);
          irep_idt identifier=PARSER.lookup_label(stack($1).get(ID_C_base_name));
          stack($$).set(ID_label, identifier);
          mto($$, $3);
        }
        | TOK_CASE constant_expression ':' statement
        {
          $$=$1;
          statement($$, ID_label);
          mto($$, $4);
          static_cast<exprt &>(stack($$).add(ID_case)).
                move_to_operands(stack($2));
        }
        | TOK_CASE constant_expression TOK_ELLIPSIS constant_expression ':' statement
        {
          // this is a GCC extension
          $$=$1;
          statement($$, ID_label);
          mto($$, $6);
          static_cast<exprt &>(stack($$).add(ID_case)).
                move_to_operands(stack($2));
          // TODO -- the other one
        }
        | TOK_DEFAULT ':' statement
        {
          $$=$1;
          statement($$, ID_label);
          mto($$, $3);
          stack($$).set(ID_default, true);
        }
        ;

/* note: the following has been changed from the ANSI-C grammar:	*/
/*	- rule compound_scope is used to prepare an inner scope for	*/
/*	  each compound_statement (and to obtain the line infos)	*/

compound_statement:
          compound_scope '{' '}'
        {
          $$=$2;
          statement($$, ID_block);
          stack($$).set(ID_C_end_location, stack($3).location());
          PARSER.pop_scope();
        }
        | compound_scope '{' statement_list '}'
        {
          $$=$3;
          stack($$).location()=stack($2).location();
          stack($$).set(ID_C_end_location, stack($4).location());
          PARSER.pop_scope();
        }
        | compound_scope '{' TOK_ASM_STRING '}'
        {
          init($$);
          stack($$).location()=stack($2).location();
          stack($$).set(ID_statement, ID_asm);
          mto($$, $3);
          PARSER.pop_scope();
        }
        ;

compound_scope:
        /* nothing */
        {
          unsigned prefix=++PARSER.current_scope().compound_counter;
          PARSER.new_scope(i2string(prefix)+"::");
        }
        ;

statement_list:
          statement
        {
          $$=$1;
          to_code(stack($$)).make_block();
        }
        | statement_list statement
        {
          mto($$, $2);
        }
        ;

expression_statement:
          comma_expression_opt ';'
        {
          $$=$2;

          if(stack($1).is_nil())
            statement($$, ID_skip);
          else
          {
            statement($$, ID_expression);
            mto($$, $1);
          }
        }
        ;

selection_statement:
          TOK_IF '(' comma_expression ')' statement
        {
          $$=$1;
          statement($$, ID_ifthenelse);
          stack($$).operands().reserve(3);
          mto($$, $3);
          mto($$, $5);
          stack($$).copy_to_operands(nil_exprt());
        }
        | TOK_IF '(' comma_expression ')' statement TOK_ELSE statement
        {
          $$=$1;
          statement($$, ID_ifthenelse);
          stack($$).operands().reserve(3);
          mto($$, $3);
          mto($$, $5);
          mto($$, $7);
        }
        | TOK_SWITCH '(' comma_expression ')' statement
        {
          $$=$1;
          statement($$, ID_switch);
          stack($$).operands().reserve(2);
          mto($$, $3);
          mto($$, $5);
        }
        ;

declaration_or_expression_statement:
          declaration_statement
        | expression_statement
        ;

iteration_statement:
        TOK_WHILE '(' comma_expression_opt ')' statement
        {
          $$=$1;
          statement($$, ID_while);
          stack($$).operands().reserve(2);
          mto($$, $3);
          mto($$, $5);
        }
        | TOK_DO statement TOK_WHILE '(' comma_expression ')' ';'
        {
          $$=$1;
          statement($$, ID_dowhile);
          stack($$).operands().reserve(2);
          mto($$, $5);
          mto($$, $2);
        }
        | TOK_FOR
          {
            // In C99 and upwards, for(;;) has a scope
            if(PARSER.for_has_scope)
            {
              unsigned prefix=++PARSER.current_scope().compound_counter;
              PARSER.new_scope(i2string(prefix)+"::");
            }
          }
          '(' declaration_or_expression_statement
              comma_expression_opt ';'
              comma_expression_opt ')'
          statement
        {
          $$=$1;
          statement($$, ID_for);
          stack($$).operands().reserve(4);
          mto($$, $4);
          mto($$, $5);
          mto($$, $7);
          mto($$, $9);

          if(PARSER.for_has_scope)
            PARSER.pop_scope(); // remove the C99 for-scope
        }
        ;

jump_statement:
          TOK_GOTO comma_expression ';'
        {
          $$=$1;
          if(stack($2).id()==ID_symbol)
          {
            statement($$, ID_goto);
            irep_idt identifier=PARSER.lookup_label(stack($2).get(ID_C_base_name));
            stack($$).set(ID_destination, identifier);
          }
          else
          {
            // this is a gcc extension.
            // the original grammar uses identifier_or_typedef_name
            statement($$, "computed-goto");
            mto($$, $2);
          }
        }
        | TOK_CONTINUE ';'
        { $$=$1; statement($$, ID_continue); }
        | TOK_BREAK ';'
        { $$=$1; statement($$, ID_break); }
        | TOK_RETURN ';'
        { $$=$1; statement($$, ID_return); }
        | TOK_RETURN comma_expression ';'
        { $$=$1; statement($$, ID_return); mto($$, $2); }
        ;

gcc_local_label_statement:
          TOK_GCC_LABEL gcc_local_label_list ';'
        { 
          $$=$1;
          statement($$, ID_gcc_local_label);
          
          // put these into the scope
          forall_operands(it, stack($2))
          {
            // labels have a separate name space
            irep_idt base_name=it->get(ID_identifier);
            irep_idt id="label-"+id2string(base_name);
            ansi_c_parsert::identifiert &i=PARSER.current_scope().name_map[id];
            i.id_class=ANSI_C_LOCAL_LABEL;
            i.base_name=base_name;
          }

          stack($$).add(ID_label).get_sub().swap(stack($2).add(ID_operands).get_sub());
        }
        ;

gcc_local_label_list:
          gcc_local_label
        {
          init($$);
          mto($$, $1);
        }
        | gcc_local_label_list ',' gcc_local_label
        {
          $$=$1;
          mto($$, $3);
        }
        ;
        
gcc_local_label: identifier_or_typedef_name
        ;

gcc_asm_statement:
          TOK_GCC_ASM_PAREN volatile_or_goto_opt '(' gcc_asm_commands ')' ';'
        { $$=$1;
          statement($$, ID_asm);
          stack($$).set(ID_flavor, ID_gcc);
          stack($$).operands().swap(stack($4).operands());
        }
        | TOK_GCC_ASM_PAREN '{' TOK_ASM_STRING '}'
        {
          $$=$1;
          statement($$, ID_asm);
          stack($$).set(ID_flavor, ID_gcc);
          mto($$, $3);
        }
        ;

msc_asm_statement:
          TOK_MSC_ASM '{' TOK_ASM_STRING '}'
        { $$=$1;
          statement($$, ID_asm);
          stack($$).set(ID_flavor, ID_msc);
          mto($$, $3);
        }
        | TOK_MSC_ASM TOK_ASM_STRING
        { $$=$1;
          statement($$, ID_asm);
          stack($$).set(ID_flavor, ID_msc);
          mto($$, $2);
        }
        ;

msc_seh_statement:
          TOK_TRY compound_statement
          TOK_MSC_EXCEPT '(' comma_expression ')' compound_statement
        {
          $$=$1;
          statement($$, ID_msc_try_except);
          mto($$, $2);
          mto($$, $5);
          mto($$, $7);
        }
        | TOK_TRY compound_statement
          TOK_MSC_FINALLY compound_statement
        {
          $$=$1;
          statement($$, ID_msc_try_finally);
          mto($$, $2);
          mto($$, $4);
        }
        | TOK_MSC_LEAVE
        {
          $$=$1;
          statement($$, ID_msc_leave);
        }
        ;

volatile_or_goto_opt:
          /* nothing */
        | TOK_VOLATILE
        | TOK_GOTO
        | TOK_GOTO TOK_VOLATILE
        | TOK_VOLATILE TOK_GOTO
        ;

/* asm ( assembler template
           : output operands                  // optional
           : input operands                   // optional
           : list of clobbered registers      // optional
           : list of C labels                 // optional
           );
*/

gcc_asm_commands:
          gcc_asm_assembler_template
          {
            init($$);
            mto($$, $1);
          }
        | gcc_asm_assembler_template gcc_asm_outputs
          {
            init($$);
            mto($$, $1);
          }
        | gcc_asm_assembler_template gcc_asm_outputs gcc_asm_inputs
          {
            init($$);
            mto($$, $1);
          }
        | gcc_asm_assembler_template gcc_asm_outputs gcc_asm_inputs gcc_asm_clobbered_registers
          {
            init($$);
            mto($$, $1);
          }
        | gcc_asm_assembler_template gcc_asm_outputs gcc_asm_inputs gcc_asm_clobbered_registers gcc_asm_labels
          {
            init($$);
            mto($$, $1);
          }
        ;

gcc_asm_assembler_template: string
        ;

gcc_asm_outputs:
          ':' gcc_asm_output_list
        | ':'
        ;

gcc_asm_output:
          string '(' comma_expression ')'
        | '[' identifier_or_typedef_name ']'
          string '(' comma_expression ')'
        ;

gcc_asm_output_list:
          gcc_asm_output
        | gcc_asm_output_list ',' gcc_asm_output
        ;

gcc_asm_inputs:
          ':' gcc_asm_input_list
        | ':'
        ;

gcc_asm_input:
          string '(' comma_expression ')'
        | '[' identifier_or_typedef_name ']'
          string '(' comma_expression ')'
        ;

gcc_asm_input_list:
          gcc_asm_input
        | gcc_asm_input_list ',' gcc_asm_input

gcc_asm_clobbered_registers:
          ':' gcc_asm_clobbered_registers_list
        | ':'
        ;

gcc_asm_clobbered_register:
          string
        ;

gcc_asm_clobbered_registers_list:
          gcc_asm_clobbered_register
        | gcc_asm_clobbered_registers_list ',' gcc_asm_clobbered_register
        ;

gcc_asm_labels:
          ':' gcc_asm_labels_list
        | ':'
        ;

gcc_asm_labels_list:
          gcc_local_label
        | gcc_asm_labels_list ',' gcc_local_label
        ;

/*** External Definitions ***********************************************/


/* note: the following has been changed from the ANSI-C grammar:	*/
/*	- translation unit is allowed to be empty!			*/

translation_unit:
        /* nothing */
        | external_definition_list
        ;

external_definition_list:
          external_definition
        | external_definition_list external_definition
        ;

external_definition:
          function_definition
        | declaration
        | asm_definition
        | ';' // empty declaration
        ;

asm_definition:
          TOK_GCC_ASM_PAREN '(' string ')' ';'
        ;

function_definition:
          function_head
        {
          // the function symbol needs to be visible before any declarations
          // in the body (the following compound_statement)
          to_ansi_c_declaration(stack($1)).value().make_nil();
          PARSER.copy_item(to_ansi_c_declaration(stack($1)));
        }
          function_body
        {
          // we now present the body as initializer
          to_ansi_c_declaration(stack($1)).value().swap(stack($3));
          PARSER.copy_item(to_ansi_c_declaration(stack($1)));
          
          // kill scope
          PARSER.pop_scope();
          PARSER.function=irep_idt();
        }
        ;

function_body:
          compound_statement
        ;

KnR_parameter_header_opt:
          /* empty */
        {
          init($$);
        }
        | KnR_parameter_header
        ;

KnR_parameter_header:
          KnR_parameter_declaration
        {
          $$=$1;
        }
        | KnR_parameter_header KnR_parameter_declaration
        {
          $$=$1;
          Forall_irep(it, stack($2).get_sub())
            stack($$).move_to_sub(*it);
        }
        ;

KnR_parameter_declaration:
          KnR_parameter_declaring_list ';'
        ;

        /* The following is stripped down because of conflicts due to gcc type attributes! */
KnR_basic_declaration_specifier:
          storage_class basic_type_name gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | basic_type_specifier storage_class gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | KnR_basic_declaration_specifier declaration_qualifier gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | KnR_basic_declaration_specifier basic_type_name gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        ;

        /* The following is stripped down because of conflicts due to gcc type attributes! */
KnR_typedef_declaration_specifier:
          typedef_type_specifier storage_class gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | storage_class typedef_name gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        | KnR_typedef_declaration_specifier declaration_qualifier gcc_type_attribute_opt
        {
          $$=$1;
          merge_types($$, $2);
          merge_types($$, $3); // type attribute
        }
        ;

        /* The following is stripped down because of conflicts due to gcc type attributes! */
KnR_declaration_specifier:
          KnR_basic_declaration_specifier
        | KnR_typedef_declaration_specifier
        ;

KnR_parameter_declaring_list:
          KnR_declaration_specifier declarator
        {
          init($$);
          stack($$).add(ID_type)=stack($1); // save for later
          exprt tmp;
          PARSER.new_declaration(stack($1), stack($2), tmp);
          stack($$).move_to_sub(tmp);
        }
        | type_specifier declarator
        {
          init($$);
          stack($$).add(ID_type)=stack($1); // save for later
          exprt tmp;
          PARSER.new_declaration(stack($1), stack($2), tmp);
          stack($$).move_to_sub(tmp);
        }
        | KnR_parameter_declaring_list ',' declarator
        {
          $$=$1;
          // need to get type from $1
          const irept &t=stack($1).type();
          exprt tmp;
          PARSER.new_declaration(t, stack($3), tmp);
          stack($$).move_to_sub(tmp);
        }
        ;

function_head:
          identifier_declarator /* no return type given */
        {
          init($$);
          irept return_type(ID_int);
          PARSER.new_declaration(return_type, stack($1), stack($$));
          create_function_scope(stack($$));
        }
        | declaration_specifier declarator
        {
          init($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
          create_function_scope(stack($$));
        }
        | type_specifier declarator
        {
          init($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
          create_function_scope(stack($$));
        }
        | declaration_qualifier_list identifier_declarator
        {
          init($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
          create_function_scope(stack($$));
        }
        | type_qualifier_list identifier_declarator
        {
          init($$);
          PARSER.new_declaration(stack($1), stack($2), stack($$));
          create_function_scope(stack($$));
        }
        ;

declarator:
          identifier_declarator
        | typedef_declarator
        ;

typedef_declarator:
          paren_typedef_declarator
        | parameter_typedef_declarator
        ;

parameter_typedef_declarator:
          typedef_name
        | typedef_name postfixing_abstract_declarator
        {
          $$=$1;
          make_subtype($$, $2);
        }
        | clean_typedef_declarator
        ;

clean_typedef_declarator:
          clean_postfix_typedef_declarator
        | '*' parameter_typedef_declarator
        {
          $$=$2;
          do_pointer($1, $2);
        }
        | '*' attribute_type_qualifier_list parameter_typedef_declarator
        {
          merge_types($2, $3);
          $$=$2;
          do_pointer($1, $2);
        }
        ;

clean_postfix_typedef_declarator:
          '(' clean_typedef_declarator ')'
        { $$ = $2; }
        | '(' clean_typedef_declarator ')' postfixing_abstract_declarator
        {
          /* note: this is a pointer ($2) to a function ($4) */
          /* or an array ($4)! */
          $$=$2;
          make_subtype($$, $4);
        }
        ;

paren_typedef_declarator:
          paren_postfix_typedef_declarator
        | '*' '(' simple_paren_typedef_declarator ')'
        {
          $$=$3;
          do_pointer($1, $3);
        }
        | '*' attribute_type_qualifier_list '(' simple_paren_typedef_declarator ')'
        {
          // not sure where the type qualifiers belong
          merge_types($2, $4);
          $$=$2;
          do_pointer($1, $2);
        }
        | '*' paren_typedef_declarator
        {
          $$=$2;
          do_pointer($1, $2);
        }
        | '*' attribute_type_qualifier_list paren_typedef_declarator
        {
          merge_types($2, $3);
          $$=$2;
          do_pointer($1, $2);
        }
        ;

paren_postfix_typedef_declarator:
          '(' paren_typedef_declarator ')'
        { $$ = $2; }
        | '(' simple_paren_typedef_declarator postfixing_abstract_declarator ')'
        {        /* note: this is a function ($3) with a typedef name ($2) */
          $$=$2;
          make_subtype($$, $3);
        }
        | '(' paren_typedef_declarator ')' postfixing_abstract_declarator
        {
          /* note: this is a pointer ($2) to a function ($4) */
          /* or an array ($4)! */
          $$=$2;
          make_subtype($$, $4);
        }
        ;

simple_paren_typedef_declarator:
          typedef_name
        | '(' simple_paren_typedef_declarator ')'
        { $$=$2; }
        ;

identifier_declarator:
          unary_identifier_declarator
        | paren_identifier_declarator
        ;

unary_identifier_declarator:
          postfix_identifier_declarator
        | '*' identifier_declarator
        {
          $$=$2;
          do_pointer($1, $2);
        }
        | '*' attribute_type_qualifier_list identifier_declarator
        {
          // the type_qualifier_list is for the pointer,
          // and not the identifier_declarator
          stack($1).id(ID_pointer);
          stack($1).add(ID_subtype)=irept(ID_abstract);
          merge_types($2, $1); // dest=$2
          make_subtype($3, $2); // dest=$3
          $$=$3;
        }
        ;

postfix_identifier_declarator:
          paren_identifier_declarator postfixing_abstract_declarator
        {
          /* note: this is a function or array ($2) with name ($1) */
          $$=$1;
          make_subtype($$, $2);
        }
        | '(' unary_identifier_declarator ')'
        { $$ = $2; }
        | '(' unary_identifier_declarator ')' postfixing_abstract_declarator
        {
          /* note: this is a pointer ($2) to a function ($4) */
          /* or an array ($4)! */
          $$=$2;
          make_subtype($$, $4);
        }
        ;

paren_identifier_declarator:
          identifier
        | '(' paren_identifier_declarator ')'
        { $$=$2; }
        ;

abstract_declarator:
          unary_abstract_declarator
        | postfix_abstract_declarator
        | postfixing_abstract_declarator
        ;

parameter_abstract_declarator:
          parameter_unary_abstract_declarator
        | parameter_postfix_abstract_declarator
        ;

postfixing_abstract_declarator:
          array_abstract_declarator
        | '(' ')'
        {
          $$=$1;
          set($$, ID_code);
          stack($$).add(ID_arguments);
          stack($$).add(ID_subtype)=irept(ID_abstract);
        }
        | '('
          {
            unsigned prefix=++PARSER.current_scope().compound_counter;
            PARSER.new_scope(i2string(prefix)+"::");
          }
          parameter_type_list
          ')'
        {
          $$=$1;
          set($$, ID_code);
          stack($$).add(ID_subtype)=irept(ID_abstract);
          stack($$).add(ID_arguments).get_sub().
            swap(stack($3).add(ID_subtypes).get_sub());
          PARSER.pop_scope();
        }
        /* The following rule implements K&R headers! */
        | '('
          {
            unsigned prefix=++PARSER.current_scope().compound_counter;
            PARSER.new_scope(i2string(prefix)+"::");
          }
          KnR_parameter_list
          ')'
          KnR_parameter_header_opt
        {
          $$=$1;
          set($$, ID_code);
          stack($$).add(ID_subtype)=irept(ID_abstract);
          stack($$).add(ID_arguments).get_sub().
            swap(stack($3).add(ID_subtypes).get_sub());
          PARSER.pop_scope();
          adjust_KnR_arguments(stack($$).add(ID_arguments), stack($5));
          stack($$).set(ID_C_KnR, true);
        }
        ;

parameter_postfixing_abstract_declarator:
          array_abstract_declarator
        | '(' ')'
        {
          $$=$1;
          set($$, ID_code);
          stack($$).add(ID_arguments);
          stack($$).add(ID_subtype)=irept(ID_abstract);
        }
        | '('
          {
            unsigned prefix=++PARSER.current_scope().compound_counter;
            PARSER.new_scope(i2string(prefix)+"::");
          }
          parameter_type_list
          ')'
        {
          $$=$1;
          set($$, ID_code);
          stack($$).add(ID_subtype)=irept(ID_abstract);
          stack($$).add(ID_arguments).get_sub().
            swap(stack($3).add(ID_subtypes).get_sub());
          PARSER.pop_scope();
        }
        ;

array_abstract_declarator:
          '[' ']'
        {
          $$=$1;
          set($$, ID_array);
          stack($$).add(ID_subtype)=irept(ID_abstract);
          stack($$).add(ID_size).make_nil();
        }
        | '[' attribute_type_qualifier_list ']'
        {
          // this is C99: e.g., restrict, const, etc
          // The type qualifier belongs to the array, not the
          // contents of the array, nor the size.
          set($1, ID_array);
          stack($1).add(ID_subtype)=irept(ID_abstract);
          stack($1).add(ID_size).make_nil();
          merge_types($2, $1); // dest=$2
          $$=$2;
        }
        | '[' '*' ']'
        {
          $$=$1;
          set($$, ID_array);
          stack($$).add(ID_subtype)=irept(ID_abstract);
          stack($$).add(ID_size).make_nil();
        }
        | '[' constant_expression ']'
        {
          $$=$1;
          set($$, ID_array);
          stack($$).add(ID_size).swap(stack($2));
          stack($$).add(ID_subtype)=irept(ID_abstract);
        }
        | '[' TOK_STATIC constant_expression ']'
        {
          // this is C99 and the constant_expression is a minimum size
          $$=$1;
          set($$, ID_array);
          stack($$).add(ID_size).swap(stack($2));
          stack($$).add(ID_subtype)=irept(ID_abstract);
        }
        | '[' attribute_type_qualifier_list constant_expression ']'
        {
          // The type qualifier belongs to the array, not the
          // contents of the array, nor the size.
          set($1, ID_array);
          stack($1).add(ID_size).swap(stack($3));
          stack($1).add(ID_subtype)=irept(ID_abstract);
          merge_types($2, $1); // dest=$2
          $$=$2;
        }
        | array_abstract_declarator '[' constant_expression ']'
        {
          // we need to push this down
          $$=$1;
          set($2, ID_array);
          stack($2).add(ID_size).swap(stack($3));
          stack($2).add(ID_subtype)=irept(ID_abstract);
          make_subtype($1, $2);
        }
        ;

unary_abstract_declarator:
          '*'
        {
          $$=$1;
          set($$, ID_pointer);
          stack($$).add(ID_subtype)=irept(ID_abstract);
        }
        | '*' attribute_type_qualifier_list
        {
          // The type_qualifier_list belongs to the pointer,
          // not to the (missing) abstract declarator.
          $$=$2;
          set($1, ID_pointer);
          stack($1).add(ID_subtype)=irept(ID_abstract);
          merge_types($$, $1);
        }
        | '*' abstract_declarator
        {
          $$=$2;
          do_pointer($1, $2);
        }
        | '*' attribute_type_qualifier_list abstract_declarator
        {
          // The type_qualifier_list belongs to the pointer,
          // not to the abstract declarator.
          $$=$2;
          do_pointer($1, $3);
          merge_types($$, $3);
        }
        | '^'
        {
          // This is an Apple extension to C/C++/Objective C.
          // http://en.wikipedia.org/wiki/Blocks_(C_language_extension)
          $$=$1;
          set($$, ID_block_pointer);
          stack($$).add(ID_subtype)=irept(ID_abstract);
        }
        ;

parameter_unary_abstract_declarator:
          '*'
        {
          $$=$1;
          set($$, ID_pointer);
          stack($$).add(ID_subtype)=irept(ID_abstract);
        }
        | '*' attribute_type_qualifier_list
        {
          // The type_qualifier_list belongs to the pointer,
          // not to the (missing) abstract declarator.
          $$=$2;
          set($$, ID_pointer);
          stack($$).add(ID_subtype)=irept(ID_abstract);
          merge_types($$, $1);
        }
        | '*' parameter_abstract_declarator
        {
          $$=$2;
          do_pointer($1, $2);
        }
        | '*' attribute_type_qualifier_list parameter_abstract_declarator
        {
          // The type_qualifier_list belongs to the pointer,
          // not to the (missing) abstract declarator.
          $$=$2;
          do_pointer($1, $3);
          merge_types($$, $3);
        }
        | '^'
        {
          // This is an Apple extension to C/C++/Objective C.
          // http://en.wikipedia.org/wiki/Blocks_(C_language_extension)
          $$=$1;
          set($$, ID_block_pointer);
          stack($$).add(ID_subtype)=irept(ID_abstract);
        }
        ;

postfix_abstract_declarator:
          '(' unary_abstract_declarator ')'
        { $$ = $2; }
        | '(' postfix_abstract_declarator ')'
        { $$ = $2; }
        | '(' postfixing_abstract_declarator ')'
        { $$ = $2; }
        | '(' unary_abstract_declarator ')' postfixing_abstract_declarator
        {
          /* note: this is a pointer ($2) to a function ($4) */
          $$=$2;
          make_subtype($$, $4);
        }
        ;

parameter_postfix_abstract_declarator:
          '(' parameter_unary_abstract_declarator ')'
        { $$ = $2; }
        | '(' parameter_postfix_abstract_declarator ')'
        { $$ = $2; }
        | parameter_postfixing_abstract_declarator
        | '(' parameter_unary_abstract_declarator ')' parameter_postfixing_abstract_declarator
        {
          /* note: this is a pointer ($2) to a function ($4) */
          $$=$2;
          make_subtype($$, $4);
        }
        ;

%%
