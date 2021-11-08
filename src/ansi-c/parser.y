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

#ifdef ANSI_C_DEBUG
#define YYDEBUG 1
#endif
#define PARSER ansi_c_parser

#include "ansi_c_parser.h"

int yyansi_clex();
extern char *yyansi_ctext;

#include "parser_static.inc"

#include "literals/convert_integer_literal.h"

#include "ansi_c_y.tab.h"

#include <util/mathematical_expr.h>

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

// statements have right recursion, deep nesting of statements thus
// requires more stack space
#define YYMAXDEPTH 25600

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
%token TOK_GCC_AUTO_TYPE "__auto_type"
%token TOK_GCC_FLOAT16 "_Float16"
%token TOK_GCC_FLOAT32 "_Float32"
%token TOK_GCC_FLOAT32X "_Float32x"
%token TOK_GCC_FLOAT80 "__float80"
%token TOK_GCC_FLOAT64 "_Float64"
%token TOK_GCC_FLOAT64X "_Float64x"
%token TOK_GCC_FLOAT128 "_Float128"
%token TOK_GCC_FLOAT128X "_Float128x"
%token TOK_GCC_INT128 "__int128"
%token TOK_GCC_DECIMAL32 "_Decimal32"
%token TOK_GCC_DECIMAL64 "_Decimal64"
%token TOK_GCC_DECIMAL128 "_Decimal128"
%token TOK_GCC_ASM     "__asm__"
%token TOK_GCC_ASM_PAREN "__asm__ (with parentheses)"
%token TOK_GCC_ATTRIBUTE "__attribute__"
%token TOK_GCC_ATTRIBUTE_ALIGNED "aligned"
%token TOK_GCC_ATTRIBUTE_TRANSPARENT_UNION "transparent_union"
%token TOK_GCC_ATTRIBUTE_PACKED "packed"
%token TOK_GCC_ATTRIBUTE_VECTOR_SIZE "vector_size"
%token TOK_GCC_ATTRIBUTE_MODE "mode"
%token TOK_GCC_ATTRIBUTE_GNU_INLINE "__gnu_inline__"
%token TOK_GCC_ATTRIBUTE_WEAK "weak"
%token TOK_GCC_ATTRIBUTE_ALIAS "alias"
%token TOK_GCC_ATTRIBUTE_SECTION "section"
%token TOK_GCC_ATTRIBUTE_NORETURN "noreturn"
%token TOK_GCC_ATTRIBUTE_CONSTRUCTOR "constructor"
%token TOK_GCC_ATTRIBUTE_DESTRUCTOR "destructor"
%token TOK_GCC_ATTRIBUTE_FALLTHROUGH "fallthrough"
%token TOK_GCC_ATTRIBUTE_USED "used"
%token TOK_GCC_LABEL   "__label__"
%token TOK_MSC_ASM     "__asm"
%token TOK_MSC_BASED   "__based"
%token TOK_CW_VAR_ARG_TYPEOF "_var_arg_typeof"
%token TOK_BUILTIN_VA_ARG "__builtin_va_arg"
%token TOK_GCC_BUILTIN_TYPES_COMPATIBLE_P "__builtin_types_compatible_p"
%token TOK_CLANG_BUILTIN_CONVERTVECTOR "__builtin_convertvector"
%token TOK_OFFSETOF    "__offsetof"
%token TOK_ALIGNOF     "__alignof__"
%token TOK_MSC_TRY     "__try"
%token TOK_MSC_FINALLY "__finally"
%token TOK_MSC_EXCEPT  "__except"
%token TOK_MSC_LEAVE   "__leave"
%token TOK_MSC_DECLSPEC "__declspec"
%token TOK_MSC_FORCEINLINE "__forceinline"
%token TOK_INTERFACE   "__interface"
%token TOK_CDECL       "__cdecl"
%token TOK_STDCALL     "__stdcall"
%token TOK_FASTCALL    "__fastcall"
%token TOK_CLRCALL     "__clrcall"
%token TOK_FORALL      "forall"
%token TOK_EXISTS      "exists"
%token TOK_ACSL_FORALL "\\forall"
%token TOK_ACSL_EXISTS "\\exists"
%token TOK_ACSL_LAMBDA "\\lambda"
%token TOK_ACSL_LET    "\\let"
%token TOK_ARRAY_OF    "array_of"
%token TOK_CPROVER_BITVECTOR "__CPROVER_bitvector"
%token TOK_CPROVER_FLOATBV "__CPROVER_floatbv"
%token TOK_CPROVER_FIXEDBV "__CPROVER_fixedbv"
%token TOK_CPROVER_ATOMIC "__CPROVER_atomic"
%token TOK_CPROVER_BOOL "__CPROVER_bool"
%token TOK_CPROVER_THROW "__CPROVER_throw"
%token TOK_CPROVER_CATCH "__CPROVER_catch"
%token TOK_CPROVER_TRY "__CPROVER_try"
%token TOK_CPROVER_FINALLY "__CPROVER_finally"
%token TOK_CPROVER_ID  "__CPROVER_ID"
%token TOK_CPROVER_LOOP_INVARIANT  "__CPROVER_loop_invariant"
%token TOK_CPROVER_DECREASES "__CPROVER_decreases"
%token TOK_CPROVER_REQUIRES  "__CPROVER_requires"
%token TOK_CPROVER_ENSURES  "__CPROVER_ensures"
%token TOK_CPROVER_ASSIGNS "__CPROVER_assigns"
%token TOK_IMPLIES     "==>"
%token TOK_EQUIVALENT  "<==>"
%token TOK_XORXOR      "^^"
%token TOK_TRUE        "TRUE"
%token TOK_FALSE       "FALSE"
%token TOK_REAL        "__real__"
%token TOK_IMAG        "__imag__"
%token TOK_ALIGNAS     "_Alignas"
%token TOK_ATOMIC_TYPE_QUALIFIER "_Atomic"
%token TOK_ATOMIC_TYPE_SPECIFIER "_Atomic()"
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
%token TOK_CHAR16_T    "char16_t"
%token TOK_CHAR32_T    "char32_t"
%token TOK_CLASS       "class"
%token TOK_DELETE      "delete"
%token TOK_DECLTYPE    "decltype"
%token TOK_EXPLICIT    "explicit"
%token TOK_FRIEND      "friend"
%token TOK_MUTABLE     "mutable"
%token TOK_NAMESPACE   "namespace"
%token TOK_NEW         "new"
%token TOK_NOEXCEPT    "noexcept"
%token TOK_OPERATOR    "operator"
%token TOK_PRIVATE     "private"
%token TOK_PROTECTED   "protected"
%token TOK_PUBLIC      "public"
%token TOK_TEMPLATE    "template"
%token TOK_THIS        "this"
%token TOK_THROW       "throw"
%token TOK_TYPEID      "typeid"
%token TOK_TYPENAME    "typename"
%token TOK_TRY         "try"
%token TOK_USING       "using"
%token TOK_VIRTUAL     "virtual"
%token TOK_SCOPE       "::"
%token TOK_DOTPM       ".*"
%token TOK_ARROWPM     "->*"
%token TOK_UNARY_TYPE_PREDICATE
%token TOK_BINARY_TYPE_PREDICATE
%token TOK_MSC_UUIDOF  "__uuidof"
%token TOK_MSC_IF_EXISTS "__if_exists"
%token TOK_MSC_IF_NOT_EXISTS "__if_not_exists"
%token TOK_UNDERLYING_TYPE "__underlying_type"

/*** priority, associativity, etc. definitions **************************/

%start grammar

%expect 2 /* the famous "dangling `else'" ambiguity */
          /* results in one shift/reduce conflict   */
          /* that we don't want to be reported      */

          /* a second shift/reduce conflict arises due to enum underlying */
          /* type specifications and bitfield specifications, which are both */
          /* introduced by a ':' and follow a type */

%{
/************************************************************************/
/*** rules **************************************************************/
/************************************************************************/
%}
%%

grammar: 
        translation_unit
        ;

/*** Token with values **************************************************/

identifier:
          TOK_IDENTIFIER
        | TOK_CPROVER_ID TOK_STRING
        {
          $$=$1;
          parser_stack($$).id(ID_symbol);
          irep_idt value=parser_stack($2).get(ID_value);
          parser_stack($$).set(ID_C_base_name, value);
          parser_stack($$).set(ID_identifier, value);
          parser_stack($$).set(
            ID_C_id_class, static_cast<int>(ansi_c_id_classt::ANSI_C_SYMBOL));
        }
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
        | clang_builtin_expressions
        | cw_builtin_expressions
        | offsetof
        | quantifier_expression
        | generic_selection
        ;

generic_selection:
          TOK_GENERIC '(' assignment_expression ',' generic_assoc_list ')'
        {
          $$=$1;
          set($$, ID_generic_selection);
          mto($$, $3);
          parser_stack($$).add(ID_generic_associations).get_sub().swap((irept::subt&)parser_stack($5).operands());
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
          parser_stack($$).id(ID_generic_association);
          parser_stack($$).set(ID_type_arg, parser_stack($1));
          parser_stack($$).set(ID_value, parser_stack($3));
        }
        | TOK_DEFAULT ':' assignment_expression
        {
          $$=$2;
          parser_stack($$).id(ID_generic_association);
          parser_stack($$).set(ID_type_arg, irept(ID_default));
          parser_stack($$).set(ID_value, parser_stack($3));
        }
        ;

gcc_builtin_expressions:
          TOK_BUILTIN_VA_ARG '(' assignment_expression ',' type_name ')'
        {
          $$=$1;
          parser_stack($$).id(ID_gcc_builtin_va_arg);
          mto($$, $3);
          parser_stack($$).type().swap(parser_stack($5));
        }
        | TOK_GCC_BUILTIN_TYPES_COMPATIBLE_P '('
           type_name ',' type_name ')'
        {
          $$=$1;
          parser_stack($$).id(ID_gcc_builtin_types_compatible_p);
          auto &type_arg=static_cast<type_with_subtypest &>(parser_stack($$).add(ID_type_arg));
          auto &subtypes=type_arg.subtypes();
          subtypes.resize(2);
          subtypes[0].swap(parser_stack($3));
          subtypes[1].swap(parser_stack($5));
        }
        ;

clang_builtin_expressions:
          TOK_CLANG_BUILTIN_CONVERTVECTOR '(' assignment_expression ',' type_name ')'
        {
          $$=$1;
          parser_stack($$).id(ID_clang_builtin_convertvector);
          mto($$, $3);
          parser_stack($$).type().swap(parser_stack($5));
        }
        ;

cw_builtin_expressions:
          TOK_CW_VAR_ARG_TYPEOF '(' type_name ')'
        {
          $$=$1;
          parser_stack($$).id(ID_cw_va_arg_typeof);
          parser_stack($$).add(ID_type_arg).swap(parser_stack($3));
        }
        ;

offsetof:
        TOK_OFFSETOF '(' type_name ',' offsetof_member_designator ')'
        {
          $$=$1;
          parser_stack($$).id(ID_builtin_offsetof);
          parser_stack($$).add(ID_type_arg).swap(parser_stack($3));
          parser_stack($$).add(ID_designator).swap(parser_stack($5));
        }
        ;

offsetof_member_designator:
          member_name
        {
          init($$);
          exprt op{ID_member};
          op.add_source_location()=parser_stack($1).source_location();
          op.set(ID_component_name, parser_stack($1).get(ID_C_base_name));
          parser_stack($$).add_to_operands(std::move(op));
        }
        | offsetof_member_designator '.' member_name
        {
          $$=$1;
          set($2, ID_member);
          parser_stack($2).set(ID_component_name, parser_stack($3).get(ID_C_base_name));
          mto($$, $2);
        }
        | offsetof_member_designator '[' comma_expression ']'
        {
          $$=$1;
          set($2, ID_index);
          mto($2, $3);
          mto($$, $2);
        }
        | offsetof_member_designator TOK_ARROW member_name
        {
          $$=$1;
          set($2, ID_index);
          parser_stack($2).add_to_operands(convert_integer_literal("0"));
          mto($$, $2);
          set($2, ID_member);
          parser_stack($2).set(ID_component_name, parser_stack($3).get(ID_C_base_name));
          mto($$, $2);
        }
        ;
          
quantifier_expression:
          TOK_FORALL compound_scope '{' declaration comma_expression '}'
        {
          $$=$1;
          set($$, ID_forall);
          parser_stack($$).add_to_operands(tuple_exprt( { std::move(parser_stack($4)) } ));
          mto($$, $5);
          PARSER.pop_scope();
        }
        | TOK_EXISTS compound_scope '{' declaration comma_expression '}'
        {
          $$=$1;
          set($$, ID_exists);
          parser_stack($$).add_to_operands(tuple_exprt( { std::move(parser_stack($4)) } ));
          mto($$, $5);
          PARSER.pop_scope();
        }
        ;

cprover_contract_loop_invariant:
          TOK_CPROVER_LOOP_INVARIANT '(' ACSL_binding_expression ')'
        { $$=$3; }
        ;

cprover_contract_loop_invariant_list:
          cprover_contract_loop_invariant
        { init($$); mto($$, $1); }
        | cprover_contract_loop_invariant_list cprover_contract_loop_invariant
        { $$=$1; mto($$, $2); }
        ;

cprover_contract_loop_invariant_list_opt:
        /* nothing */
        { init($$); parser_stack($$).make_nil(); }
        | cprover_contract_loop_invariant_list
        ;

ACSL_binding_expression_list:
          ACSL_binding_expression
        { init($$); mto($$, $1); }
        | ACSL_binding_expression_list ',' ACSL_binding_expression
        { $$=$1; mto($$, $3); }
        ;

cprover_contract_decreases_opt:
        /* nothing */
        { init($$); parser_stack($$).make_nil(); }
        | TOK_CPROVER_DECREASES '(' ACSL_binding_expression_list ')'
        { $$=$3; }
        ;

statement_expression: '(' compound_statement ')'
        { 
          $$=$1;
          set($$, ID_side_effect);
          parser_stack($$).set(ID_statement, ID_statement_expression);
          mto($$, $2);
        }
        ;

postfix_expression:
          primary_expression
        | postfix_expression '[' comma_expression ']'
        { binary($$, $1, $2, ID_index, $3); }
        | postfix_expression '(' ')'
        { $$=$2;
          set($$, ID_side_effect);
          auto &side_effect = to_side_effect_expr(parser_stack($$));
          side_effect.set_statement(ID_function_call);
          side_effect.operands().resize(2);
          to_binary_expr(side_effect).op0().swap(parser_stack($1));
          to_binary_expr(side_effect).op1().clear();
          to_binary_expr(side_effect).op1().id(ID_arguments);
        }
        | postfix_expression '(' argument_expression_list ')'
        { $$=$2;
          set($$, ID_side_effect);
          auto &side_effect = to_side_effect_expr(parser_stack($$));
          side_effect.set_statement(ID_function_call);
          side_effect.operands().resize(2);
          to_binary_expr(side_effect).op0().swap(parser_stack($1));
          to_binary_expr(side_effect).op1().swap(parser_stack($3));
          to_binary_expr(side_effect).op1().id(ID_arguments);
        }
        | postfix_expression '.' member_name
        { $$=$2;
          set($$, ID_member);
          mto($$, $1);
          parser_stack($$).set(ID_component_name, parser_stack($3).get(ID_C_base_name));
        }
        | postfix_expression TOK_ARROW member_name
        { $$=$2;
          set($$, ID_ptrmember);
          mto($$, $1);
          parser_stack($$).set(ID_component_name, parser_stack($3).get(ID_C_base_name));
        }
        | postfix_expression TOK_INCR
        { $$=$2;
          set($$, ID_side_effect);
          parser_stack($$).set(ID_statement, ID_postincrement);
          mto($$, $1);
        }
        | postfix_expression TOK_DECR
        { $$=$2;
          set($$, ID_side_effect);
          parser_stack($$).set(ID_statement, ID_postdecrement);
          mto($$, $1);
        }
        /* The following is a) GCC and b) ISO C 11 compliant */
        | '(' type_name ')' '{' initializer_list_opt '}'
        {
          exprt tmp(ID_initializer_list);
          tmp.add_source_location()=parser_stack($4).source_location();
          tmp.operands().swap(parser_stack($5).operands());
          $$=$1;
          set($$, ID_typecast);
          parser_stack($$).add_to_operands(std::move(tmp));
          parser_stack($$).type().swap(parser_stack($2));
        }
        | '(' type_name ')' '{' initializer_list ',' '}'
        {
          // same as above
          exprt tmp(ID_initializer_list);
          tmp.add_source_location()=parser_stack($4).source_location();
          tmp.operands().swap(parser_stack($5).operands());
          $$=$1;
          set($$, ID_typecast);
          parser_stack($$).add_to_operands(std::move(tmp));
          parser_stack($$).type().swap(parser_stack($2));
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
          set($$, ID_side_effect);
          parser_stack($$).set(ID_statement, ID_preincrement);
          mto($$, $2);
        }
        | TOK_DECR unary_expression
        { $$=$1;
          set($$, ID_side_effect);
          parser_stack($$).set(ID_statement, ID_predecrement);
          mto($$, $2);
        }
        | '&' cast_expression
        { $$=$1;
          set($$, ID_address_of);
          mto($$, $2);
        }
        | TOK_ANDAND gcc_local_label
        { // this takes the address of a label (a gcc extension)
          $$=$1;
          irep_idt identifier=PARSER.lookup_label(parser_stack($2).get(ID_C_base_name));
          set($$, ID_address_of);
          parser_stack($$).operands().resize(1);
          auto &op = to_unary_expr(parser_stack($$)).op();
          op=parser_stack($2);
          op.id(ID_label);
          op.set(ID_identifier, identifier);
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
          parser_stack($$).add(ID_type_arg).swap(parser_stack($3));
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
          parser_stack($$).id(ID_alignof);
          parser_stack($$).add(ID_type_arg).swap(parser_stack($3));
        }
        ;

cast_expression:
          unary_expression
        | '(' type_name ')' cast_expression
        {
          $$=$1;
          set($$, ID_typecast);
          mto($$, $4);
          parser_stack($$).type().swap(parser_stack($2));
        }
        | TOK_REAL cast_expression
        { $$=$1;
          set($$, ID_complex_real);
          mto($$, $2);
        }
        | TOK_IMAG cast_expression
        { $$=$1;
          set($$, ID_complex_imag);
          mto($$, $2);
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

logical_xor_expression:
          logical_and_expression
        | logical_xor_expression TOK_XORXOR logical_and_expression
        { binary($$, $1, $2, ID_xor, $3); }
        ;

logical_or_expression:
          logical_xor_expression
        | logical_or_expression TOK_OROR logical_xor_expression
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

/* Non-standard, defined by ACSL. Lowest precedence of all operators. */
ACSL_binding_expression:
          conditional_expression
        | TOK_ACSL_FORALL compound_scope declaration ACSL_binding_expression
        {
          $$=$1;
          set($$, ID_forall);
          parser_stack($$).add_to_operands(tuple_exprt( { std::move(parser_stack($3)) } ));
          mto($$, $4);
          PARSER.pop_scope();
        }
        | TOK_ACSL_EXISTS compound_scope declaration ACSL_binding_expression
        {
          $$=$1;
          set($$, ID_exists);
          parser_stack($$).add_to_operands(tuple_exprt( { std::move(parser_stack($3)) } ));
          mto($$, $4);
          PARSER.pop_scope();
        }
        | TOK_ACSL_LAMBDA compound_scope declaration ACSL_binding_expression
        {
          $$=$1;
          set($$, ID_lambda);
          parser_stack($$).add_to_operands(tuple_exprt( { std::move(parser_stack($3)) } ));
          mto($$, $4);
          PARSER.pop_scope();
        }
        ;

conditional_expression:
          logical_equivalence_expression
        | logical_equivalence_expression '?' comma_expression ':' conditional_expression
        { $$=$2;
          parser_stack($$).id(ID_if);
          mto($$, $1);
          mto($$, $3);
          mto($$, $5);
        }
        | logical_equivalence_expression '?' ':' conditional_expression
        { $$=$2;
          parser_stack($$).id(ID_side_effect);
          parser_stack($$).set(ID_statement, ID_gcc_conditional_expression);
          mto($$, $1);
          mto($$, $4);
        }
        ;

assignment_expression:
          ACSL_binding_expression /* usually conditional_expression */
        | cast_expression '=' assignment_expression
        { binary($$, $1, $2, ID_side_effect, $3); parser_stack($$).set(ID_statement, ID_assign); }
        | cast_expression TOK_MULTASSIGN assignment_expression
        { binary($$, $1, $2, ID_side_effect, $3); parser_stack($$).set(ID_statement, ID_assign_mult); }
        | cast_expression TOK_DIVASSIGN assignment_expression
        { binary($$, $1, $2, ID_side_effect, $3); parser_stack($$).set(ID_statement, ID_assign_div); }
        | cast_expression TOK_MODASSIGN assignment_expression
        { binary($$, $1, $2, ID_side_effect, $3); parser_stack($$).set(ID_statement, ID_assign_mod); }
        | cast_expression TOK_PLUSASSIGN assignment_expression
        { binary($$, $1, $2, ID_side_effect, $3); parser_stack($$).set(ID_statement, ID_assign_plus); }
        | cast_expression TOK_MINUSASSIGN assignment_expression
        { binary($$, $1, $2, ID_side_effect, $3); parser_stack($$).set(ID_statement, ID_assign_minus); }
        | cast_expression TOK_SHLASSIGN assignment_expression
        { binary($$, $1, $2, ID_side_effect, $3); parser_stack($$).set(ID_statement, ID_assign_shl); }
        | cast_expression TOK_SHRASSIGN assignment_expression
        { binary($$, $1, $2, ID_side_effect, $3); parser_stack($$).set(ID_statement, ID_assign_shr); }
        | cast_expression TOK_ANDASSIGN assignment_expression
        { binary($$, $1, $2, ID_side_effect, $3); parser_stack($$).set(ID_statement, ID_assign_bitand); }
        | cast_expression TOK_XORASSIGN assignment_expression
        { binary($$, $1, $2, ID_side_effect, $3); parser_stack($$).set(ID_statement, ID_assign_bitxor); }
        | cast_expression TOK_ORASSIGN assignment_expression
        { binary($$, $1, $2, ID_side_effect, $3); parser_stack($$).set(ID_statement, ID_assign_bitor); }
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
        { init($$); parser_stack($$).make_nil(); }
        | comma_expression
        ;

/*** Declarations *******************************************************/

declaration:
          declaration_specifier ';'
        {
          // type only, no declarator!
          init($$, ID_declaration);
          parser_stack($$).type().swap(parser_stack($1));
        }
        | type_specifier ';'
        {
          // type only, no identifier!
          init($$, ID_declaration);
          parser_stack($$).type().swap(parser_stack($1));
        }
        | static_assert_declaration ';'
        | declaring_list ';'
        | default_declaring_list ';'
        ;
        
static_assert_declaration:
          TOK_STATIC_ASSERT '(' assignment_expression ',' assignment_expression ')'
        {
          $$=$1;
          set($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_static_assert(true);
          mto($$, $3);
          mto($$, $5);
        }
        ;

default_declaring_list:
          declaration_qualifier_list identifier_declarator
          {
            init($$, ID_declaration);
            parser_stack($$).type().swap(parser_stack($1));
            PARSER.add_declarator(parser_stack($$), parser_stack($2));
          }
          initializer_opt
        {
          // patch on the initializer
          $$=$3;
          to_ansi_c_declaration(parser_stack($$)).add_initializer(parser_stack($4));
        }
        | type_qualifier_list identifier_declarator
          {
            init($$, ID_declaration);
            parser_stack($$).type().swap(parser_stack($1));
            PARSER.add_declarator(parser_stack($$), parser_stack($2));
          }
          initializer_opt
        {
          // patch on the initializer
          $$=$3;
          to_ansi_c_declaration(parser_stack($$)).add_initializer(parser_stack($4));
        }
        | default_declaring_list ',' identifier_declarator
          {
            // just add the declarator
            PARSER.add_declarator(parser_stack($1), parser_stack($3));
            // Needs to be done before initializer, as we want to see that identifier
            // already there!
          }
          initializer_opt
        {
          // patch on the initializer
          $$=$1;
          to_ansi_c_declaration(parser_stack($$)).add_initializer(parser_stack($5));
        }
        ;

post_declarator_attribute:
          TOK_GCC_ASM_PAREN volatile_or_goto_opt '(' gcc_asm_commands ')'
        {
          $$=$1;
          parser_stack($$).id(ID_asm);
          parser_stack($$).set(ID_flavor, ID_gcc);
          parser_stack($$).operands().swap(parser_stack($4).operands());
        }
        | gcc_attribute_specifier
        ;

post_declarator_attributes:
          post_declarator_attributes post_declarator_attribute
        {
          $$=merge($1, $2);
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
            $2=merge($3, $2); // type attribute
            
            // the symbol has to be visible during initialization
            init($$, ID_declaration);
            parser_stack($$).type().swap(parser_stack($1));
            PARSER.add_declarator(parser_stack($$), parser_stack($2));
          }
          initializer_opt
        {
          // add the initializer
          $$=$4;
          to_ansi_c_declaration(parser_stack($$)).add_initializer(parser_stack($5));
        }
        | type_specifier declarator
          post_declarator_attributes_opt
          {
            $2=merge($3, $2);
            
            // the symbol has to be visible during initialization
            init($$, ID_declaration);
            parser_stack($$).type().swap(parser_stack($1));
            PARSER.add_declarator(parser_stack($$), parser_stack($2));
          }
          initializer_opt
        {
          // add the initializer
          $$=$4;
          to_ansi_c_declaration(parser_stack($$)).add_initializer(parser_stack($5));
        }
        | TOK_GCC_AUTO_TYPE declarator
          post_declarator_attributes_opt '=' initializer
        {
          // handled as typeof(initializer)
          parser_stack($1).id(ID_typeof);
          parser_stack($1).copy_to_operands(parser_stack($5));

          $2=merge($3, $2);

          // the symbol has to be visible during initialization
          init($$, ID_declaration);
          parser_stack($$).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
          // add the initializer
          to_ansi_c_declaration(parser_stack($$)).add_initializer(parser_stack($5));
        }
        | declaring_list ',' gcc_type_attribute_opt declarator
          post_declarator_attributes_opt
          {
            // type attribute goes into declarator
            $5=merge($5, $3);
            $4=merge($5, $4);
            PARSER.add_declarator(parser_stack($1), parser_stack($4));
          }
          initializer_opt
        {
          // add in the initializer
          $$=$1;
          to_ansi_c_declaration(parser_stack($$)).add_initializer(parser_stack($7));
        }
        ;

declaration_specifier:
          basic_declaration_specifier
        | sue_declaration_specifier
        | typedef_declaration_specifier
        | typeof_declaration_specifier
        | atomic_declaration_specifier
        ;

type_specifier:
          basic_type_specifier
        | sue_type_specifier
        | typedef_type_specifier
        | typeof_type_specifier
        | atomic_type_specifier
        ;

declaration_qualifier_list:
          storage_class
        | type_qualifier_list storage_class
        {
          $$=merge($1, $2);
        }
        | gcc_attribute_specifier
        | declaration_qualifier_list gcc_attribute_specifier
        {
          $$=merge($1, $2);
        }
        | declaration_qualifier_list declaration_qualifier
        {
          $$=merge($1, $2);
        }
        ;

type_qualifier_list:
          type_qualifier
        | type_qualifier_list type_qualifier
        {
          $$=merge($1, $2);
        }
        /* The following is to allow mixing of type attributes with
           type qualifiers, but the list has to start with a
           proper type qualifier. */
        | type_qualifier_list gcc_attribute_specifier
        {
          $$=merge($1, $2);
        }
        ;

attribute_type_qualifier_list:
          attribute_or_type_qualifier
        | attribute_type_qualifier_list attribute_or_type_qualifier
        {
          $$=merge($1, $2);
        }
        ;

declaration_qualifier:
          storage_class
        | type_qualifier
        ;

type_qualifier:
          TOK_ATOMIC_TYPE_QUALIFIER { $$=$1; set($$, ID_atomic); }
        | TOK_CONST                 { $$=$1; set($$, ID_const); }
        | TOK_RESTRICT              { $$=$1; set($$, ID_restrict); }
        | TOK_VOLATILE              { $$=$1; set($$, ID_volatile); }
        | TOK_CPROVER_ATOMIC        { $$=$1; set($$, ID_cprover_atomic); }
        | TOK_PTR32                 { $$=$1; set($$, ID_ptr32); }
        | TOK_PTR64                 { $$=$1; set($$, ID_ptr64); }
        | TOK_MSC_BASED '(' comma_expression ')' { $$=$1; set($$, ID_msc_based); mto($$, $3); }
        | alignas_specifier
        ;

alignas_specifier:
          TOK_ALIGNAS '(' comma_expression ')'
        { $$ = $1;
          parser_stack($$).id(ID_aligned);
          parser_stack($$).set(ID_size, parser_stack($3));
        }
        | TOK_ALIGNAS '(' type_name ')'
        { $$ = $1;
          parser_stack($$).id(ID_aligned);
          parser_stack($3).set(ID_type_arg, parser_stack($3));
        }
        ;

attribute_or_type_qualifier:
          type_qualifier
        | gcc_attribute_specifier
        ;

attribute_or_type_qualifier_or_storage_class:
          type_qualifier
        | gcc_attribute_specifier
        | storage_class
        ;

attribute_type_qualifier_storage_class_list:
          attribute_or_type_qualifier_or_storage_class
        | attribute_type_qualifier_storage_class_list attribute_or_type_qualifier_or_storage_class
        {
          $$=merge($1, $2);
        }
        ;

basic_declaration_specifier:
          declaration_qualifier_list basic_type_name gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | basic_type_specifier storage_class gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | basic_declaration_specifier declaration_qualifier gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | basic_declaration_specifier basic_type_name gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        ;

basic_type_specifier:
          basic_type_name gcc_type_attribute_opt
        {
          $$=merge($1, $2); // type attribute
        }
        | type_qualifier_list basic_type_name gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | basic_type_specifier type_qualifier
        {
          $$=merge($1, $2);
        }
        | basic_type_specifier basic_type_name gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        ;

sue_declaration_specifier:
          declaration_qualifier_list elaborated_type_name
        {
          $$=merge($1, $2);
        }
        | sue_type_specifier storage_class gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | sue_declaration_specifier declaration_qualifier gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        ;

sue_type_specifier:
          elaborated_type_name
        | type_qualifier_list elaborated_type_name
        {
          $$=merge($1, $2);
        }
        | sue_type_specifier type_qualifier gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        ;

typedef_declaration_specifier:
          typedef_type_specifier storage_class gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | declaration_qualifier_list typedef_name gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | typedef_declaration_specifier declaration_qualifier gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        ;

typeof_declaration_specifier:
          typeof_type_specifier storage_class gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | declaration_qualifier_list typeof_specifier gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | typeof_declaration_specifier declaration_qualifier gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        ;

atomic_declaration_specifier:
          atomic_type_specifier storage_class gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | declaration_qualifier_list atomic_specifier gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | atomic_declaration_specifier declaration_qualifier gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        ;

typedef_type_specifier:
          typedef_name gcc_type_attribute_opt
        {
          $$=merge($1, $2);
        }
        | type_qualifier_list typedef_name gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | typedef_type_specifier type_qualifier gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        ;

typeof_specifier:
          TOK_TYPEOF '(' comma_expression ')'
        { $$ = $1;
          parser_stack($$).id(ID_typeof);
          mto($$, $3);
        }
        | TOK_TYPEOF '(' type_name ')'
        { $$ = $1;
          parser_stack($$).id(ID_typeof);
          parser_stack($$).set(ID_type_arg, parser_stack($3));
        }
        ;

typeof_type_specifier:
          typeof_specifier
        | type_qualifier_list typeof_specifier
        {
          $$=merge($1, $2);
        }
        | type_qualifier_list typeof_specifier type_qualifier_list
        {
          $$=merge($1, merge($2, $3));
        }
        | typeof_specifier type_qualifier_list
        {
          $$=merge($1, $2);
        }
        ;

atomic_specifier:
          TOK_ATOMIC_TYPE_SPECIFIER '(' type_name ')'
        {
          $$=$1;
          parser_stack($$).id(ID_atomic_type_specifier);
          stack_type($$).subtype()=stack_type($3);
        }
        ;

atomic_type_specifier:
          atomic_specifier
        | type_qualifier_list atomic_specifier
        {
          $$=merge($1, $2);
        }
        | type_qualifier_list atomic_specifier type_qualifier_list
        {
          $$=merge($1, merge($2, $3));
        }
        | atomic_specifier type_qualifier_list
        {
          $$=merge($1, $2);
        }
        ;

msc_decl_identifier:
          TOK_IDENTIFIER
        {
          parser_stack($$).id(parser_stack($$).get(ID_identifier));
        }
        | TOK_TYPEDEFNAME
        {
          parser_stack($$).id(parser_stack($$).get(ID_identifier));
        }
        | TOK_RESTRICT
        {
          parser_stack($$).id(ID_restrict);
        }
        ;

msc_decl_modifier:
          msc_decl_identifier
        | msc_decl_identifier '(' TOK_STRING ')'
        {
          $$=$1; mto($$, $3);
        }
        | msc_decl_identifier '(' TOK_INTEGER ')'
        {
          $$=$1; mto($$, $3);
        }
        | msc_decl_identifier '(' msc_decl_identifier '=' msc_decl_identifier ')'
        {
          $$=$1; mto($$, $3); mto($$, $5);
        }
        | msc_decl_identifier '(' msc_decl_identifier '=' msc_decl_identifier ',' msc_decl_identifier '=' msc_decl_identifier ')'
        {
          $$=$1; mto($$, $3); mto($$, $5); mto($$, $7); mto($$, $9);
        }
        | ',' { init($$, ID_nil); }
        ;

msc_declspec_seq:
          msc_decl_modifier
        {
          init($$); mto($$, $1);
        }
        | msc_declspec_seq msc_decl_modifier
        {
          $$=$1; mto($$, $2);
        }
        ;

msc_declspec:
          TOK_MSC_DECLSPEC '(' msc_declspec_seq ')'
        {
          $$=$1; set($$, ID_msc_declspec);
          parser_stack($$).operands().swap(parser_stack($3).operands());
        }
        | TOK_MSC_DECLSPEC '(' ')'
        {
          $$=$1; set($$, ID_msc_declspec);
        }
        ;

msc_declspec_opt:
          /* blank */
        {
          init($$, ID_nil);
        }
        | msc_declspec_opt msc_declspec
        {
          if(parser_stack($1).is_not_nil())
          {
            $$ = $1;
            exprt::operandst &operands = parser_stack($1).operands();
            operands.insert(
              operands.end(),
              parser_stack($2).operands().begin(),
              parser_stack($2).operands().end());
          }
          else
            $$ = $2;
        }
        ;

storage_class:
          TOK_TYPEDEF      { $$=$1; set($$, ID_typedef); }
        | TOK_EXTERN       { $$=$1; set($$, ID_extern); }
        | TOK_STATIC       { $$=$1; set($$, ID_static); }
        | TOK_AUTO         { $$=$1; set($$, ID_auto); }
        | TOK_REGISTER     { $$=$1; set($$, ID_register); }
        | TOK_INLINE       { $$=$1; set($$, ID_inline); }
        | TOK_THREAD_LOCAL { $$=$1; set($$, ID_thread_local); }
        | TOK_GCC_ASM      { $$=$1; set($$, ID_asm); }
        | msc_declspec     { $$=$1; }
        | TOK_MSC_FORCEINLINE
        {
          // equivalent to always_inline, and seemingly also has the semantics
          // of extern inline in that multiple definitions can be provided in
          // the same translation unit
          init($$);
          set($$, ID_static);
          set($1, ID_inline);
          #if 0
          // enable once always_inline support is reinstantiated
          $1=merge($1, $$);

          init($$);
          set($$, ID_always_inline);
          $$=merge($1, $$);
          #else
          $$=merge($1, $$);
          #endif
        }
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
        | TOK_GCC_FLOAT16   { $$=$1; set($$, ID_gcc_float16); }
        | TOK_GCC_FLOAT32   { $$=$1; set($$, ID_gcc_float32); }
        | TOK_GCC_FLOAT32X  { $$=$1; set($$, ID_gcc_float32x); }
        | TOK_GCC_FLOAT64   { $$=$1; set($$, ID_gcc_float64); }
        | TOK_GCC_FLOAT64X  { $$=$1; set($$, ID_gcc_float64x); }
        | TOK_GCC_FLOAT80   { $$=$1; set($$, ID_gcc_float80); }
        | TOK_GCC_FLOAT128  { $$=$1; set($$, ID_gcc_float128); }
        | TOK_GCC_FLOAT128X { $$=$1; set($$, ID_gcc_float128x); }
        | TOK_GCC_INT128    { $$=$1; set($$, ID_gcc_int128); }
        | TOK_GCC_DECIMAL32 { $$=$1; set($$, ID_gcc_decimal32); }
        | TOK_GCC_DECIMAL64 { $$=$1; set($$, ID_gcc_decimal64); }
        | TOK_GCC_DECIMAL128 { $$=$1; set($$, ID_gcc_decimal128); }
        | TOK_DOUBLE   { $$=$1; set($$, ID_double); }
        | TOK_SIGNED   { $$=$1; set($$, ID_signed); }
        | TOK_UNSIGNED { $$=$1; set($$, ID_unsigned); }
        | TOK_VOID     { $$=$1; set($$, ID_void); }
        | TOK_BOOL     { $$=$1; set($$, ID_c_bool); }
        | TOK_COMPLEX  { $$=$1; set($$, ID_complex); }
        | TOK_CPROVER_BITVECTOR '[' comma_expression ']'
        {
          $$=$1;
          set($$, ID_custom_bv);
          parser_stack($$).add(ID_size).swap(parser_stack($3));
        }
        | TOK_CPROVER_FLOATBV '[' comma_expression ']' '[' comma_expression ']'
        {
          $$=$1;
          set($$, ID_custom_floatbv);
          parser_stack($$).add(ID_size).swap(parser_stack($3));
          parser_stack($$).add(ID_f).swap(parser_stack($6));
        }
        | TOK_CPROVER_FIXEDBV '[' comma_expression ']' '[' comma_expression ']'
        {
          $$=$1;
          set($$, ID_custom_fixedbv);
          parser_stack($$).add(ID_size).swap(parser_stack($3));
          parser_stack($$).add(ID_f).swap(parser_stack($6));
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
        { $$=$1; stack_type($$).subtype().swap(parser_stack($2)); }
        ;

pragma_packed:
        {
          init($$);
          if(!PARSER.pragma_pack.empty() &&
             PARSER.pragma_pack.back().is_one())
            set($$, ID_packed);
        }
        ;

aggregate_name:
          aggregate_key
          gcc_type_attribute_opt
          msc_declspec_opt
          {
            // an anon struct/union with body
          }
          '{' member_declaration_list_opt '}'
          gcc_type_attribute_opt
          pragma_packed
        {
          // save the members
          parser_stack($1).add(ID_components).get_sub().swap(
            (irept::subt &)parser_stack($6).operands());

          // throw in the gcc attributes
          $$=merge($1, merge($2, merge($8, $9)));
        }
        | aggregate_key
          gcc_type_attribute_opt
          msc_declspec_opt
          identifier_or_typedef_name
          {
            // A struct/union with tag and body.
            PARSER.add_tag_with_body(parser_stack($4));
            parser_stack($1).set(ID_tag, parser_stack($4));
          }
          '{' member_declaration_list_opt '}'
          gcc_type_attribute_opt
          pragma_packed
        {
          // save the members
          parser_stack($1).add(ID_components).get_sub().swap(
            (irept::subt &)parser_stack($7).operands());

          // throw in the gcc attributes
          $$=merge($1, merge($2, merge($9, $10)));
        }
        | aggregate_key
          gcc_type_attribute_opt
          msc_declspec_opt
          identifier_or_typedef_name
          {
            // a struct/union with tag but without body
            parser_stack($1).set(ID_tag, parser_stack($4));
          }
          gcc_type_attribute_opt
        {
          parser_stack($1).set(ID_components, ID_nil);
          // type attributes
          $$=merge($1, merge($2, $6));
        }
        ;

aggregate_key:
          TOK_STRUCT
        { $$=$1; set($$, ID_struct); }
        | TOK_UNION
        { $$=$1; set($$, ID_union); }
        ;

gcc_type_attribute:
          TOK_GCC_ATTRIBUTE_PACKED
        { $$=$1; set($$, ID_packed); }
        | TOK_GCC_ATTRIBUTE_TRANSPARENT_UNION
        { $$=$1; set($$, ID_transparent_union); }
        | TOK_GCC_ATTRIBUTE_VECTOR_SIZE '(' comma_expression ')'
        { $$=$1; set($$, ID_vector); parser_stack($$).add(ID_size)=parser_stack($3); }
        | TOK_GCC_ATTRIBUTE_ALIGNED
        { $$=$1; set($$, ID_aligned); }
        | TOK_GCC_ATTRIBUTE_ALIGNED '(' comma_expression ')'
        { $$=$1; set($$, ID_aligned); parser_stack($$).set(ID_size, parser_stack($3)); }
        | TOK_GCC_ATTRIBUTE_MODE '(' identifier ')'
        { $$=$1; set($$, ID_gcc_attribute_mode); parser_stack($$).set(ID_size, parser_stack($3).get(ID_identifier)); }
        | TOK_GCC_ATTRIBUTE_GNU_INLINE
        { $$=$1; set($$, ID_static); } /* GCC extern inline - cleanup in ansi_c_declarationt::to_symbol */
        | TOK_GCC_ATTRIBUTE_WEAK
        { $$=$1; set($$, ID_weak); }
        | TOK_GCC_ATTRIBUTE_ALIAS '(' TOK_STRING ')'
        { $$=$1; set($$, ID_alias); mto($$, $3); }
        | TOK_GCC_ATTRIBUTE_SECTION '(' TOK_STRING ')'
        { $$=$1; set($$, ID_section); mto($$, $3); }
        | TOK_GCC_ATTRIBUTE_NORETURN
        { $$=$1; set($$, ID_noreturn); }
        | TOK_GCC_ATTRIBUTE_CONSTRUCTOR
        { $$=$1; set($$, ID_constructor); }
        | TOK_GCC_ATTRIBUTE_DESTRUCTOR
        { $$=$1; set($$, ID_destructor); }
        | TOK_GCC_ATTRIBUTE_USED
        { $$=$1; set($$, ID_used); }
        ;

gcc_attribute:
          /* empty */
        {
          init($$);
        }
        | TOK_GCC_ATTRIBUTE_FALLTHROUGH
        {
          // attribute ignored
          init($$);
        }
        | gcc_type_attribute
        ;

gcc_attribute_list:
          gcc_attribute
        | gcc_attribute_list ',' gcc_attribute
        {
          $$=merge($1, $3);
        }
        ;          

gcc_attribute_specifier:
          TOK_GCC_ATTRIBUTE '(' '(' gcc_attribute_list ')' ')'
        { $$=$4; }
        | TOK_NORETURN
        { $$=$1; set($$, ID_noreturn); }
        ;

gcc_type_attribute_opt:
          /* empty */
        {
          init($$);
        }
        | gcc_type_attribute_list
        ;

gcc_type_attribute_list:
          gcc_attribute_specifier
        | gcc_type_attribute_list gcc_attribute_specifier
        {
          $$=merge($1, $2);
        }
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
        {
          init($$, ID_declaration_list);
          mto($$, $1);
        }
        | member_declaration_list member_declaration
        {
          $$=$1;
          mto($$, $2);
        }
        ;

member_declaration:
          member_declaring_list ';'
        | member_default_declaring_list ';'
        | ';' /* empty declaration */
        {
          $$=$1; // the ';' becomes the location of the declaration
          parser_stack($$).id(ID_declaration);
        }
        | static_assert_declaration ';'
        ;

// This rule is for member declarations _without_ type, which
// is assumed to be 'int'. Clang issues a warning about these.

member_default_declaring_list:
          gcc_type_attribute_opt
          type_qualifier_list
          member_identifier_declarator
        {
          $2=merge($2, $1);

          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_member(true);
          parser_stack($$).add_source_location()=parser_stack($2).source_location();
          parser_stack($$).type().swap(parser_stack($2));
          PARSER.add_declarator(parser_stack($$), parser_stack($3));
        }
        | member_default_declaring_list ',' member_identifier_declarator
        {
          $$=$1;
          PARSER.add_declarator(parser_stack($$), parser_stack($3));
        }
        ;

member_declaring_list:
          gcc_type_attribute_opt
          type_specifier
          member_declarator
        {
          if(!PARSER.pragma_pack.empty() &&
             !PARSER.pragma_pack.back().is_zero())
          {
            // communicate #pragma pack(n) alignment constraints by
            // by both setting packing AND alignment; see padding.cpp
            // for more details
            init($$);
            set($$, ID_packed);
            $2=merge($2, $$);

            init($$);
            set($$, ID_aligned);
            parser_stack($$).set(ID_size, PARSER.pragma_pack.back());
            $2=merge($2, $$);
          }

          $2=merge($2, $1);

          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_member(true);
          parser_stack($$).add_source_location()=parser_stack($2).source_location();
          parser_stack($$).type().swap(parser_stack($2));
          PARSER.add_declarator(parser_stack($$), parser_stack($3));
        }
        | member_declaring_list ',' member_declarator
        {
          $$=$1;
          PARSER.add_declarator(parser_stack($$), parser_stack($3));
        }
        ;

member_declarator:
          declarator bit_field_size_opt gcc_type_attribute_opt
        {
          $$=$1;

          if(parser_stack($2).is_not_nil())
            make_subtype($$, $2);

          if(parser_stack($3).is_not_nil()) // type attribute
            $$=merge($3, $$);
        }
        | /* empty */
        {
          init($$, ID_abstract);
        }
        | bit_field_size gcc_type_attribute_opt
        {
          $$=$1;
          stack_type($$).subtype()=typet(ID_abstract);

          if(parser_stack($2).is_not_nil()) // type attribute
            $$=merge($2, $$);
        }
        ;

member_identifier_declarator:
          identifier_declarator bit_field_size_opt gcc_type_attribute_opt
        {
          $$=$1;
          if(parser_stack($2).is_not_nil())
            make_subtype($$, $2);
          
          if(parser_stack($3).is_not_nil()) // type attribute
            $$=merge($3, $$);
        }
        | bit_field_size gcc_type_attribute_opt
        {
          $$=$1;
          stack_type($$).subtype()=typet(ID_abstract);

          if(parser_stack($2).is_not_nil()) // type attribute
            $$=merge($2, $$);
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
          set($$, ID_c_bit_field);
          stack_type($$).set(ID_size, parser_stack($2));
          stack_type($$).subtype().id(ID_abstract);
        }
        ;

enum_name:
          enum_key
          gcc_type_attribute_opt
          enum_underlying_type_opt
        {
          // an anon enum
          if(parser_stack($3).is_not_nil())
          {
            parser_stack($1).set(ID_enum_underlying_type, parser_stack($3));
          }
        }
         '{' enumerator_list_opt '}'
          gcc_type_attribute_opt
        {
          parser_stack($1).operands().swap(parser_stack($6).operands());
          $$=merge($1, merge($2, $8)); // throw in the gcc attributes
        }
        | enum_key
          gcc_type_attribute_opt
          identifier_or_typedef_name
          enum_underlying_type_opt
        {
          // an enum with tag
          parser_stack($1).set(ID_tag, parser_stack($3));

          if(parser_stack($4).is_not_nil())
          {
            parser_stack($1).set(ID_enum_underlying_type, parser_stack($4));
          }
        }
          braced_enumerator_list_opt
          gcc_type_attribute_opt
        {
          if(parser_stack($6).is_not_nil())
          {
            parser_stack($1).operands().swap(parser_stack($6).operands());
          }
          else
          {
            parser_stack($1).id(ID_c_enum_tag);
          }

          $$=merge($1, merge($2, $7)); // throw in the gcc attributes
        }
        ;

basic_type_name_list:
    basic_type_name
  | basic_type_name_list basic_type_name
  {
    $$ = merge($1, $2);
  }

enum_underlying_type:
    basic_type_name_list
  | typedef_name

enum_underlying_type_opt:
        /* empty */
        {
          init($$);
          parser_stack($$).make_nil();
        }
        | ':' enum_underlying_type
        {
          $$=$2;
        }

braced_enumerator_list_opt:
        /* empty */
        {
          init($$);
          parser_stack($$).make_nil();
        }
        | '{' enumerator_list_opt '}'
        {
          $$=$2;
        }

enum_key: TOK_ENUM
        {
          $$=$1;
          set($$, ID_c_enum);
        }
        ;

enumerator_list_opt:
          /* nothing */
        {
          init($$, ID_declaration_list);
        }
        | enumerator_list
        ;

enumerator_list:
          enumerator_declaration
        {
          init($$, ID_declaration_list);
          mto($$, $1);
        }
        | enumerator_list ',' enumerator_declaration
        {
          $$=$1;
          mto($$, $3);
        }
        | enumerator_list ',' // trailing comma ok
        {
          $$=$1;
        }
        ;

enumerator_declaration:
          identifier_or_typedef_name gcc_type_attribute_opt enumerator_value_opt
        {
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_enum_constant(true);
          PARSER.add_declarator(parser_stack($$), parser_stack($1));
          to_ansi_c_declaration(parser_stack($$)).add_initializer(parser_stack($3));
        }
        ;

enumerator_value_opt:
        /* nothing */
        {
          init($$);
          parser_stack($$).make_nil();
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
          to_type_with_subtypes(stack_type($$)).move_to_subtypes(tmp);
        }
        ;

KnR_parameter_list:
          KnR_parameter
        {
          init($$, ID_parameters);
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
          init($$, ID_declaration);
          parser_stack($$).type()=typet(ID_KnR);
          PARSER.add_declarator(parser_stack($$), parser_stack($1));
        }
        ;

parameter_list:
          parameter_declaration
        {
          init($$, ID_parameters);
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
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          exprt declarator=exprt(ID_abstract);
          PARSER.add_declarator(parser_stack($$), declarator);
        }
        | declaration_specifier parameter_abstract_declarator
        {
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
        }
        | declaration_specifier identifier_declarator gcc_type_attribute_opt
        {
          $2=merge($3, $2); // type attribute to go into declarator
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
        }
        | declaration_specifier parameter_typedef_declarator
        {
          // the second tree is really the declarator -- not part
          // of the type!
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
        }
        | declaration_qualifier_list
        {
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          exprt declarator=exprt(ID_abstract);
          PARSER.add_declarator(parser_stack($$), declarator);
        }
        | declaration_qualifier_list parameter_abstract_declarator
        {
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
        }
        | declaration_qualifier_list identifier_declarator gcc_type_attribute_opt
        {
          $2=merge($3, $2); // type attribute to go into declarator
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
        }
        | type_specifier
        {
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          exprt declarator=exprt(ID_abstract);
          PARSER.add_declarator(parser_stack($$), declarator);
        }
        | type_specifier parameter_abstract_declarator
        {
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
        }
        | type_specifier identifier_declarator gcc_type_attribute_opt
        {
          $2=merge($3, $2); // type attribute to go into declarator
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
        }
        | type_specifier parameter_typedef_declarator
        {
          // the second tree is really the declarator -- not part of the type!
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
        }
        | type_qualifier_list
        {
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          exprt declarator=exprt(ID_abstract);
          PARSER.add_declarator(parser_stack($$), declarator);
        }
        | type_qualifier_list parameter_abstract_declarator
        {
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
        }
        | type_qualifier_list identifier_declarator gcc_type_attribute_opt
        {
          $2=merge($3, $2); // type attribute to go into declarator
          init($$, ID_declaration);
          to_ansi_c_declaration(parser_stack($$)).set_is_parameter(true);
          to_ansi_c_declaration(parser_stack($$)).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
        }
        ;

identifier_or_typedef_name:
          identifier
        | typedef_name
        ;

type_name:
          gcc_type_attribute_opt type_specifier
        {
          $$=merge($2, $1);
        }
        | gcc_type_attribute_opt type_specifier abstract_declarator
        {
          $$=merge($2, $1);
          make_subtype($$, $3);
        }
        | gcc_type_attribute_opt type_qualifier_list
        {
          $$=merge($2, $1);
        }
        | gcc_type_attribute_opt type_qualifier_list abstract_declarator
        {
          $$=merge($2, $1);
          make_subtype($$, $3);
        }
        ;

initializer_opt:
        /* nothing */
        {
          init($$);
          parser_stack($$).make_nil();
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
          parser_stack($$).operands().swap(parser_stack($2).operands());
        }
        | '{' initializer_list ',' '}'
        {
          $$=$1;
          set($$, ID_initializer_list);
          parser_stack($$).operands().swap(parser_stack($2).operands());
        }
        ;

initializer_list:
          designated_initializer
        {
          $$=$1;
          exprt tmp;
          tmp.swap(parser_stack($$));
          parser_stack($$).clear();
          parser_stack($$).add_to_operands(std::move(tmp));
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
          parser_stack($$).operands().clear();
        }
        ;

designated_initializer:
          initializer
        | designator '=' initializer
        {
          $$=$2;
          parser_stack($$).id(ID_designated_initializer);
          parser_stack($$).add(ID_designator).swap(parser_stack($1));
          mto($$, $3);
        }
        /* the following two are obsolete GCC extensions */
        | designator initializer
        {
          init($$, ID_designated_initializer);
          parser_stack($$).add(ID_designator).swap(parser_stack($1));
          mto($$, $2);
        }
        | member_name ':' initializer
        {
          // yet another GCC speciality
          $$=$2;
          parser_stack($$).id(ID_designated_initializer);
          exprt designator;
          exprt member(ID_member);
          member.set(ID_component_name, parser_stack($1).get(ID_C_base_name));
          designator.add_to_operands(std::move(member));
          parser_stack($$).add(ID_designator).swap(designator);
          mto($$, $3);
        }
        ;

designator:
          '.' member_name
        {
          init($$);
          parser_stack($1).id(ID_member);
          parser_stack($1).set(ID_component_name, parser_stack($2).get(ID_C_base_name));
          mto($$, $1);
        }
        | '[' comma_expression ']'
        {
          init($$);
          parser_stack($1).id(ID_index);
          mto($1, $2);
          mto($$, $1);
        }
        | '[' comma_expression TOK_ELLIPSIS comma_expression ']'
        {
          // TODO
          init($$);
          parser_stack($1).id(ID_index);
          mto($1, $2);
          mto($$, $1);
        }
        | designator '[' comma_expression ']'
        {
          $$=$1;
          parser_stack($2).id(ID_index);
          mto($2, $3);
          mto($$, $2);
        }
        | designator '[' comma_expression TOK_ELLIPSIS comma_expression ']'
        {
          // TODO
          $$=$1;
          parser_stack($2).id(ID_index);
          mto($2, $3);
          mto($$, $2);
        }
        | designator '.' member_name
        {
          $$=$1;
          parser_stack($2).id(ID_member);
          parser_stack($2).set(ID_component_name, parser_stack($3).get(ID_C_base_name));
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
        | cprover_exception_statement
        | statement_attribute
        ;

declaration_statement:
          declaration
        {
          init($$);
          statement($$, ID_decl);
          mto($$, $1);
        }
        ;

labeled_statement:
        identifier_or_typedef_name ':' statement
        {
          $$=$2;
          statement($$, ID_label);
          irep_idt identifier=PARSER.lookup_label(parser_stack($1).get(ID_C_base_name));
          parser_stack($$).set(ID_label, identifier);
          mto($$, $3);
        }
        | TOK_CASE constant_expression ':' statement
        {
          $$=$1;
          statement($$, ID_switch_case);
          mto($$, $2);
          mto($$, $4);
        }
        | TOK_CASE constant_expression TOK_ELLIPSIS constant_expression ':' statement
        {
          // this is a GCC extension
          $$=$1;
          statement($$, ID_gcc_switch_case_range);
          mto($$, $2);
          mto($$, $4);
          mto($$, $6);
        }
        | TOK_DEFAULT ':' statement
        {
          $$=$1;
          statement($$, ID_switch_case);
          parser_stack($$).operands().push_back(nil_exprt());
          mto($$, $3);
          parser_stack($$).set(ID_default, true);
        }
        ;

statement_attribute:
        gcc_attribute_specifier ';'
        {
          // Really should only be TOK_GCC_ATTRIBUTE_FALLTHROUGH or a label
          // attribute. Only semicolons permitted after the attribute:
          // https://gcc.gnu.org/onlinedocs/gcc/Label-Attributes.html
          // We ignore all such attributes.
          $$=$1;
          statement($$, ID_skip);
        }
        ;

compound_statement:
          compound_scope '{' '}'
        {
          $$=$2;
          statement($$, ID_block);
          parser_stack($$).set(ID_C_end_location, parser_stack($3).source_location());
          PARSER.pop_scope();
        }
        | compound_scope '{' statement_list '}'
        {
          $$=$2;
          statement($$, ID_block);
          parser_stack($$).set(ID_C_end_location, parser_stack($4).source_location());
          parser_stack($$).operands().swap(parser_stack($3).operands());
          PARSER.pop_scope();
        }
        | compound_scope '{' TOK_ASM_STRING '}'
        {
          $$=$2;
          statement($$, ID_asm);
          parser_stack($$).set(ID_C_end_location, parser_stack($4).source_location());
          mto($$, $3);
          PARSER.pop_scope();
        }
        ;

compound_scope:
        /* nothing */
        {
          unsigned prefix=++PARSER.current_scope().compound_counter;
          PARSER.new_scope(std::to_string(prefix)+"::");
        }
        ;

statement_list:
          statement
        {
          init($$);
          mto($$, $1);
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

          if(parser_stack($1).is_nil())
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
          parser_stack($$).add_to_operands(
            std::move(parser_stack($3)), std::move(parser_stack($5)), nil_exprt());
        }
        | TOK_IF '(' comma_expression ')' statement TOK_ELSE statement
        {
          $$=$1;
          statement($$, ID_ifthenelse);
          parser_stack($$).add_to_operands(
            std::move(parser_stack($3)), std::move(parser_stack($5)), std::move(parser_stack($7)));
        }
        | TOK_SWITCH '(' comma_expression ')' statement
        {
          $$=$1;
          statement($$, ID_switch);
          parser_stack($$).add_to_operands(std::move(parser_stack($3)), std::move(parser_stack($5)));
        }
        ;

declaration_or_expression_statement:
          declaration_statement
        | expression_statement
        ;

iteration_statement:
        TOK_WHILE '(' comma_expression_opt ')'
          cprover_contract_assigns_opt
          cprover_contract_loop_invariant_list_opt 
          cprover_contract_decreases_opt
          statement
        {
          $$=$1;
          statement($$, ID_while);
          parser_stack($$).add_to_operands(std::move(parser_stack($3)), std::move(parser_stack($8)));

          if(!parser_stack($5).operands().empty())
            static_cast<exprt &>(parser_stack($$).add(ID_C_spec_assigns)).operands().swap(parser_stack($5).operands());

          if(!parser_stack($6).operands().empty())
            static_cast<exprt &>(parser_stack($$).add(ID_C_spec_loop_invariant)).operands().swap(parser_stack($6).operands());

          if(!parser_stack($7).operands().empty())
            static_cast<exprt &>(parser_stack($$).add(ID_C_spec_decreases)).operands().swap(parser_stack($7).operands());
        }
        | TOK_DO statement TOK_WHILE '(' comma_expression ')'
          cprover_contract_assigns_opt
          cprover_contract_loop_invariant_list_opt 
          cprover_contract_decreases_opt ';'
        {
          $$=$1;
          statement($$, ID_dowhile);
          parser_stack($$).add_to_operands(std::move(parser_stack($5)), std::move(parser_stack($2)));

          if(!parser_stack($7).operands().empty())
            static_cast<exprt &>(parser_stack($$).add(ID_C_spec_assigns)).operands().swap(parser_stack($7).operands());

          if(!parser_stack($8).operands().empty())
            static_cast<exprt &>(parser_stack($$).add(ID_C_spec_loop_invariant)).operands().swap(parser_stack($8).operands());

          if(!parser_stack($9).operands().empty())
            static_cast<exprt &>(parser_stack($$).add(ID_C_spec_decreases)).operands().swap(parser_stack($9).operands());
        }
        | TOK_FOR
          {
            // In C99 and upwards, for(;;) has a scope
            if(PARSER.for_has_scope)
            {
              unsigned prefix=++PARSER.current_scope().compound_counter;
              PARSER.new_scope(std::to_string(prefix)+"::");
            }
          }
          '(' declaration_or_expression_statement
              comma_expression_opt ';'
              comma_expression_opt ')'
              cprover_contract_assigns_opt
              cprover_contract_loop_invariant_list_opt 
              cprover_contract_decreases_opt
          statement
        {
          $$=$1;
          statement($$, ID_for);
          parser_stack($$).operands().reserve(4);
          mto($$, $4);
          mto($$, $5);
          mto($$, $7);
          mto($$, $12);

          if(!parser_stack($9).operands().empty())
            static_cast<exprt &>(parser_stack($$).add(ID_C_spec_assigns)).operands().swap(parser_stack($9).operands());

          if(!parser_stack($10).operands().empty())
            static_cast<exprt &>(parser_stack($$).add(ID_C_spec_loop_invariant)).operands().swap(parser_stack($10).operands());

          if(!parser_stack($11).operands().empty())
            static_cast<exprt &>(parser_stack($$).add(ID_C_spec_decreases)).operands().swap(parser_stack($11).operands());

          if(PARSER.for_has_scope)
            PARSER.pop_scope(); // remove the C99 for-scope
        }
        ;

jump_statement:
          TOK_GOTO comma_expression ';'
        {
          $$=$1;
          if(parser_stack($2).id()==ID_symbol)
          {
            statement($$, ID_goto);
            irep_idt identifier=PARSER.lookup_label(parser_stack($2).get(ID_C_base_name));
            parser_stack($$).set(ID_destination, identifier);
          }
          else
          {
            // this is a gcc extension.
            // the original grammar uses identifier_or_typedef_name
            statement($$, ID_gcc_computed_goto);
            mto($$, $2);
          }
        }
        | TOK_GOTO typedef_name ';'
        {
          $$=$1;
          statement($$, ID_goto);
          irep_idt identifier=PARSER.lookup_label(parser_stack($2).get(ID_C_base_name));
          parser_stack($$).set(ID_destination, identifier);
        }
        | TOK_CONTINUE ';'
        { $$=$1; statement($$, ID_continue); }
        | TOK_BREAK ';'
        { $$=$1; statement($$, ID_break); }
        | TOK_RETURN ';'
        {
          $$=$1;
          statement($$, ID_return);
          parser_stack($$).operands().push_back(nil_exprt());
        }
        | TOK_RETURN comma_expression ';'
        { $$=$1; statement($$, ID_return); mto($$, $2); }
        ;

gcc_local_label_statement:
          TOK_GCC_LABEL gcc_local_label_list ';'
        { 
          $$=$1;
          statement($$, ID_gcc_local_label);
          
          // put these into the scope
          forall_operands(it, parser_stack($2))
          {
            // labels have a separate name space
            irep_idt base_name=it->get(ID_identifier);
            irep_idt id="label-"+id2string(base_name);
            ansi_c_parsert::identifiert &i=PARSER.current_scope().name_map[id];
            i.id_class=ansi_c_id_classt::ANSI_C_LOCAL_LABEL;
            i.prefixed_name=PARSER.current_scope().prefix+id2string(id);
            i.base_name=base_name;
          }

          parser_stack($$).add(ID_label).get_sub().swap((irept::subt&)parser_stack($2).operands());
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
          parser_stack($$).set(ID_flavor, ID_gcc);
          parser_stack($$).operands().swap(parser_stack($4).operands());
        }
        | TOK_GCC_ASM_PAREN volatile_or_goto_opt '{' TOK_ASM_STRING '}'
        {
          $$=$1;
          statement($$, ID_asm);
          parser_stack($$).set(ID_flavor, ID_gcc);
          parser_stack($$).operands().resize(5);
          to_multi_ary_expr(parser_stack($$)).op0()=parser_stack($4);
        }
        ;

msc_asm_statement:
          TOK_MSC_ASM '{' TOK_ASM_STRING '}'
        { $$=$1;
          statement($$, ID_asm);
          parser_stack($$).set(ID_flavor, ID_msc);
          mto($$, $3);
        }
        | TOK_MSC_ASM TOK_ASM_STRING
        { $$=$1;
          statement($$, ID_asm);
          parser_stack($$).set(ID_flavor, ID_msc);
          mto($$, $2);
        }
        ;

msc_seh_statement:
          TOK_MSC_TRY compound_statement
          TOK_MSC_EXCEPT '(' comma_expression ')' compound_statement
        {
          $$=$1;
          statement($$, ID_msc_try_except);
          mto($$, $2);
          mto($$, $5);
          mto($$, $7);
        }
        | TOK_MSC_TRY compound_statement
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

cprover_exception_statement:
          TOK_CPROVER_THROW ';'
        {
          $$=$1;
          statement($$, ID_CPROVER_throw);
        }
        | TOK_CPROVER_TRY compound_statement
          TOK_CPROVER_CATCH compound_statement
        {
          $$=$1;
          statement($$, ID_CPROVER_try_catch);
          mto($$, $2);
          mto($$, $4);
        }
        | TOK_CPROVER_TRY compound_statement
          TOK_CPROVER_FINALLY compound_statement
        {
          $$=$1;
          statement($$, ID_CPROVER_try_finally);
          mto($$, $2);
          mto($$, $4);
        }
        ;

volatile_or_goto_opt:
          /* nothing */
        | volatile_or_goto_opt TOK_VOLATILE
        | volatile_or_goto_opt TOK_GOTO
        | volatile_or_goto_opt TOK_INLINE
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
          parser_stack($$).operands().resize(5);
          parser_stack($$).operands()[0]=parser_stack($1);
        }
        | gcc_asm_assembler_template gcc_asm_outputs
        {
          init($$);
          parser_stack($$).operands().resize(5);
          parser_stack($$).operands()[0]=parser_stack($1);
          parser_stack($$).operands()[1]=parser_stack($2);
        }
        | gcc_asm_assembler_template gcc_asm_outputs gcc_asm_inputs
        {
          init($$);
          parser_stack($$).operands().resize(5);
          parser_stack($$).operands()[0]=parser_stack($1);
          parser_stack($$).operands()[1]=parser_stack($2);
          parser_stack($$).operands()[2]=parser_stack($3);
        }
        | gcc_asm_assembler_template gcc_asm_outputs gcc_asm_inputs gcc_asm_clobbered_registers
        {
          init($$);
          parser_stack($$).operands().resize(5);
          parser_stack($$).operands()[0]=parser_stack($1);
          parser_stack($$).operands()[1]=parser_stack($2);
          parser_stack($$).operands()[2]=parser_stack($3);
          parser_stack($$).operands()[3]=parser_stack($4);
        }
        | gcc_asm_assembler_template gcc_asm_outputs gcc_asm_inputs gcc_asm_clobbered_registers gcc_asm_labels
        {
          init($$);
          parser_stack($$).operands().resize(5);
          parser_stack($$).operands()[0]=parser_stack($1);
          parser_stack($$).operands()[1]=parser_stack($2);
          parser_stack($$).operands()[2]=parser_stack($3);
          parser_stack($$).operands()[3]=parser_stack($4);
          parser_stack($$).operands()[4]=parser_stack($5);
        }
        ;

gcc_asm_assembler_template: string
        ;

gcc_asm_outputs:
          ':' gcc_asm_output_list
        {
          $$=$2;
        }
        | ':'
        ;

gcc_asm_output:
          string '(' comma_expression ')'
        {
          $$=$2;
          parser_stack($$).id(ID_gcc_asm_output);
          parser_stack($$).add_to_operands(std::move(parser_stack($1)), std::move(parser_stack($3)));
        }
        | '[' identifier_or_typedef_name ']'
          string '(' comma_expression ')'
        {
          $$=$5;
          parser_stack($$).id(ID_gcc_asm_output);
          parser_stack($$).add_to_operands(std::move(parser_stack($4)), std::move(parser_stack($6)));
        }
        ;

gcc_asm_output_list:
          gcc_asm_output
        {
          init($$, irep_idt());
          mto($$, $1);
        }
        | gcc_asm_output_list ',' gcc_asm_output
        {
          $$=$1;
          mto($$, $3);
        }
        ;

gcc_asm_inputs:
          ':' gcc_asm_input_list
        {
          $$=$2;
        }
        | ':'
        ;

gcc_asm_input:
          string '(' comma_expression ')'
        {
          $$=$2;
          parser_stack($$).id(ID_gcc_asm_input);
          parser_stack($$).add_to_operands(std::move(parser_stack($1)), std::move(parser_stack($3)));
        }
        | '[' identifier_or_typedef_name ']'
          string '(' comma_expression ')'
        {
          $$=$5;
          parser_stack($$).id(ID_gcc_asm_input);
          parser_stack($$).add_to_operands(std::move(parser_stack($4)), std::move(parser_stack($6)));
        }
        ;

gcc_asm_input_list:
          gcc_asm_input
        {
          init($$, irep_idt());
          mto($$, $1);
        }
        | gcc_asm_input_list ',' gcc_asm_input
        {
          $$=$1;
          mto($$, $3);
        }
        ;

gcc_asm_clobbered_registers:
          ':' gcc_asm_clobbered_registers_list
        {
          $$=$2;
        }
        | ':'
        ;

gcc_asm_clobbered_register:
          string
        {
          init($$, ID_gcc_asm_clobbered_register);
          mto($$, $1);
        }
        ;

gcc_asm_clobbered_registers_list:
          gcc_asm_clobbered_register
        {
          init($$, irep_idt());
          mto($$, $1);
        }
        | gcc_asm_clobbered_registers_list ',' gcc_asm_clobbered_register
        {
          $$=$1;
          mto($$, $3);
        }
        ;

gcc_asm_labels:
          ':' gcc_asm_labels_list
        {
          $$=$2;
        }
        | ':'
        ;

gcc_asm_labels_list:
          gcc_asm_label
        {
          init($$);
          mto($$, $1);
        }
        | gcc_asm_labels_list ',' gcc_asm_label
        {
          $$=$1;
          mto($$, $3);
        }
        ;

gcc_asm_label:
          gcc_local_label
        {
          $$=$1;
          irep_idt identifier=PARSER.lookup_label(parser_stack($$).get(ID_C_base_name));
          parser_stack($$).id(ID_label);
          parser_stack($$).set(ID_identifier, identifier);
        }

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
        {
          // put into global list of items
          PARSER.copy_item(to_ansi_c_declaration(parser_stack($1)));
        }
        | declaration
        {
          PARSER.copy_item(to_ansi_c_declaration(parser_stack($1)));
        }
        | asm_definition
        | ';' // empty declaration
        ;

asm_definition:
          TOK_GCC_ASM_PAREN '(' string ')' ';'
        {
          // Not obvious what to do with this.
        }
        | '{' TOK_ASM_STRING '}'
        {
          // Not obvious what to do with this.
        }
        ;

function_definition:
          function_head
          function_body
        {
          // The head is a declaration with one declarator,
          // and the body becomes the 'value'.
          $$=$1;
          ansi_c_declarationt &ansi_c_declaration=
            to_ansi_c_declaration(parser_stack($$));
            
          assert(ansi_c_declaration.declarators().size()==1);
          ansi_c_declaration.add_initializer(parser_stack($2));
          
          // Kill the scope that 'function_head' creates.
          PARSER.pop_scope();
          
          // We are no longer in any function.
          PARSER.set_function(irep_idt());
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
          init($$, ID_decl_block);
          mto($$, $1);
        }
        | KnR_parameter_header KnR_parameter_declaration
        {
          $$=$1;
          mto($$, $2);
        }
        ;

KnR_parameter_declaration:
          KnR_parameter_declaring_list ';'
        ;

        /* The following is stripped down because of conflicts due to gcc type attributes! */
KnR_declaration_qualifier_list:
          storage_class
        | type_qualifier storage_class
        {
          $$=merge($2, $1);
        }
        | KnR_declaration_qualifier_list declaration_qualifier
        {
          $$=merge($2, $1);
        }
        ;

KnR_basic_declaration_specifier:
          KnR_declaration_qualifier_list basic_type_name gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | basic_type_specifier storage_class gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | KnR_basic_declaration_specifier declaration_qualifier gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | KnR_basic_declaration_specifier basic_type_name gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        ;

        /* The following is stripped down because of conflicts due to gcc type attributes! */
KnR_typedef_declaration_specifier:
          typedef_type_specifier storage_class gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | KnR_declaration_qualifier_list typedef_name gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        | KnR_typedef_declaration_specifier declaration_qualifier gcc_type_attribute_opt
        {
          $$=merge($1, merge($2, $3));
        }
        ;

        /* The following is stripped down because of conflicts due to gcc type attributes! */
KnR_sue_declaration_specifier:
        KnR_declaration_qualifier_list aggregate_key identifier_or_typedef_name gcc_type_attribute_opt
        {
          parser_stack($2).set(ID_tag, parser_stack($3));
          $$=merge($1, merge($2, $4));
        }
        | KnR_declaration_qualifier_list enum_key identifier_or_typedef_name gcc_type_attribute_opt
        {
          parser_stack($2).id(ID_c_enum_tag);
          parser_stack($2).set(ID_tag, parser_stack($3));
          $$=merge($1, merge($2, $4));
        }
        ;

        /* The following is stripped down because of conflicts due to gcc type attributes! */
KnR_declaration_specifier:
          KnR_basic_declaration_specifier
        | KnR_typedef_declaration_specifier
        | KnR_sue_declaration_specifier
        ;

KnR_parameter_declaring_list:
          KnR_declaration_specifier declarator
        {
          init($$, ID_declaration);
          parser_stack($$).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
        }
        | type_specifier declarator
        {
          init($$, ID_declaration);
          parser_stack($$).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
        }
        | KnR_parameter_declaring_list ',' declarator
        {
          $$=$1;
          PARSER.add_declarator(parser_stack($$), parser_stack($3));
        }
        ;

function_head:
          identifier_declarator /* no return type given */
        {
          init($$, ID_declaration);
          irept return_type(ID_int);
          parser_stack($$).type().swap(return_type);
          PARSER.add_declarator(parser_stack($$), parser_stack($1));
          create_function_scope($$);
        }
        | declaration_specifier declarator post_declarator_attributes_opt
        {
          init($$, ID_declaration);
          parser_stack($$).type().swap(parser_stack($1));
          $2=merge($3, $2);
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
          create_function_scope($$);
        }
        | type_specifier declarator post_declarator_attributes_opt
        {
          init($$, ID_declaration);
          parser_stack($$).type().swap(parser_stack($1));
          $2=merge($3, $2);
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
          create_function_scope($$);
        }
        | declaration_qualifier_list identifier_declarator
        {
          init($$, ID_declaration);
          parser_stack($$).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
          create_function_scope($$);
        }
        | type_qualifier_list identifier_declarator
        {
          init($$, ID_declaration);
          parser_stack($$).type().swap(parser_stack($1));
          PARSER.add_declarator(parser_stack($$), parser_stack($2));
          create_function_scope($$);
        }
        ;

declarator:
          identifier_declarator
        | typedef_declarator
        | paren_attribute_declarator
        ;

paren_attribute_declarator:
          '(' gcc_type_attribute_list identifier_declarator ')'
        {
          stack_type($1)=typet(ID_abstract);
          $2=merge($2, $1); // dest=$2
          make_subtype($3, $2); // dest=$3
          $$=$3;
        }
        | '(' gcc_type_attribute_list identifier_declarator ')' postfixing_abstract_declarator
        {
          stack_type($1)=typet(ID_abstract);
          $2=merge($2, $1); // dest=$2
          make_subtype($3, $2); // dest=$3
          /* note: this is (a pointer to) a function ($5) */
          /* or an array ($5) with name ($3) */
          $$=$3;
          make_subtype($$, $5);
        }
        | '*' paren_attribute_declarator
        {
          $$=$2;
          do_pointer($1, $2);
        }
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
          $$=merge($2, $3);
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
          $$=merge($2, $4);
          do_pointer($1, $2);
        }
        | '*' paren_typedef_declarator
        {
          $$=$2;
          do_pointer($1, $2);
        }
        | '*' attribute_type_qualifier_list paren_typedef_declarator
        {
          $$=merge($2, $3);
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
        | '^' identifier_declarator
        {
          // This is an Apple extension to C/C++/Objective C.
          // http://en.wikipedia.org/wiki/Blocks_(C_language_extension)
          $$=$2;
          do_pointer($1, $2);
        }
        | '*' attribute_type_qualifier_list identifier_declarator
        {
          // the type_qualifier_list is for the pointer,
          // and not the identifier_declarator
          // The below is deliberately not using pointer_type();
          // the width is added during conversion.
          stack_type($1).id(ID_frontend_pointer);
          stack_type($1).subtype()=typet(ID_abstract);
          $2=merge($2, $1); // dest=$2
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
        {
          // We remember the last declarator for the benefit
          // of function argument scoping.
          PARSER.current_scope().last_declarator=
            parser_stack($1).get(ID_identifier);
        }
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

cprover_function_contract:
          TOK_CPROVER_ENSURES '(' ACSL_binding_expression ')'
        {
          $$=$1;
          set($$, ID_C_spec_ensures);
          mto($$, $3);
        }
        | TOK_CPROVER_REQUIRES '(' ACSL_binding_expression ')'
        {
          $$=$1;
          set($$, ID_C_spec_requires);
          mto($$, $3);
        }
        | cprover_contract_assigns
        ;

cprover_contract_assigns:
         TOK_CPROVER_ASSIGNS '(' argument_expression_list ')'
        {
          $$=$1;
          set($$, ID_C_spec_assigns);
          parser_stack($3).id(ID_target_list);
          mto($$, $3);
        }
        | TOK_CPROVER_ASSIGNS '(' ')'
        {
          $$=$1;
          set($$, ID_C_spec_assigns);
          parser_stack($$).add_to_operands(exprt(ID_target_list));
        }
        ;

cprover_contract_assigns_opt:
        /* nothing */
        { init($$); parser_stack($$).make_nil(); }
        | cprover_contract_assigns
        ;

cprover_function_contract_sequence:
          cprover_function_contract
        | cprover_function_contract_sequence cprover_function_contract
        {
          $$=$1;
          merge($$, $2);
        }
        ;

cprover_function_contract_sequence_opt:
          /* nothing */
          { init($$); }
        | cprover_function_contract_sequence
        ;

postfixing_abstract_declarator:
          parameter_postfixing_abstract_declarator
        /* The following two rules implement K&R headers! */
        | '(' 
          ')'
          KnR_parameter_header
        {
          $$=$1;
          set($$, ID_code);
          stack_type($$).subtype()=typet(ID_abstract);
          stack_type($$).add(ID_parameters);
          stack_type($$).set(ID_C_KnR, true);
        }
        | '('
          {
            // Use last declarator (i.e., function name) to name
            // the scope.
            PARSER.new_scope(
              id2string(PARSER.current_scope().last_declarator)+"::");
          }
          KnR_parameter_list
          ')'
          KnR_parameter_header_opt
        {
          $$=$1;
          set($$, ID_code);
          stack_type($$).subtype()=typet(ID_abstract);
          stack_type($$).add(ID_parameters).get_sub().
            swap((irept::subt &)(to_type_with_subtypes(stack_type($3)).subtypes()));
          PARSER.pop_scope();
          adjust_KnR_parameters(parser_stack($$).add(ID_parameters), parser_stack($5));
          parser_stack($$).set(ID_C_KnR, true);
        }
        ;

parameter_postfixing_abstract_declarator:
          array_abstract_declarator
        | '(' ')'
          cprover_function_contract_sequence_opt
        {
          set($1, ID_code);
          stack_type($1).add(ID_parameters);
          stack_type($1).subtype()=typet(ID_abstract);
          $$ = merge($3, $1);
        }
        | '('
          {
            // Use last declarator (i.e., function name) to name
            // the scope.
            PARSER.new_scope(
              id2string(PARSER.current_scope().last_declarator)+"::");
          }
          parameter_type_list
          ')'
          KnR_parameter_header_opt
          cprover_function_contract_sequence_opt
        {
          set($1, ID_code);
          stack_type($1).subtype()=typet(ID_abstract);
          stack_type($1).add(ID_parameters).get_sub().
            swap((irept::subt &)(to_type_with_subtypes(stack_type($3)).subtypes()));
          PARSER.pop_scope();

          if(parser_stack($5).is_not_nil())
          {
            adjust_KnR_parameters(parser_stack($$).add(ID_parameters), parser_stack($5));
            parser_stack($$).set(ID_C_KnR, true);
          }

          $$ = merge($6, $1);
        }
        ;

array_abstract_declarator:
          '[' ']'
        {
          $$=$1;
          set($$, ID_array);
          stack_type($$).subtype()=typet(ID_abstract);
          stack_type($$).add(ID_size).make_nil();
        }
        | '[' attribute_type_qualifier_storage_class_list ']'
        {
          // this is C99: e.g., restrict, const, etc
          // The type qualifier belongs to the array, not the
          // contents of the array, nor the size.
          set($1, ID_array);
          stack_type($1).subtype()=typet(ID_abstract);
          stack_type($1).add(ID_size).make_nil();
          $$=merge($2, $1);
        }
        | '[' '*' ']'
        {
          // these should be allowed in prototypes only
          $$=$1;
          set($$, ID_array);
          stack_type($$).subtype()=typet(ID_abstract);
          stack_type($$).add(ID_size).make_nil();
        }
        | '[' constant_expression ']'
        {
          $$=$1;
          set($$, ID_array);
          stack_type($$).add(ID_size).swap(parser_stack($2));
          stack_type($$).subtype()=typet(ID_abstract);
        }
        | '[' attribute_type_qualifier_storage_class_list constant_expression ']'
        {
          // The type qualifier belongs to the array, not the
          // contents of the array, nor the size.
          set($1, ID_array);
          stack_type($1).add(ID_size).swap(parser_stack($3));
          stack_type($1).subtype()=typet(ID_abstract);
          $$=merge($2, $1); // dest=$2
        }
        | array_abstract_declarator '[' constant_expression ']'
        {
          // we need to push this down
          $$=$1;
          set($2, ID_array);
          stack_type($2).add(ID_size).swap(parser_stack($3));
          stack_type($2).subtype()=typet(ID_abstract);
          make_subtype($1, $2);
        }
        | array_abstract_declarator '[' '*' ']'
        {
          // these should be allowed in prototypes only
          // we need to push this down
          $$=$1;
          set($2, ID_array);
          stack_type($2).add(ID_size).make_nil();
          stack_type($2).subtype()=typet(ID_abstract);
          make_subtype($1, $2);
        }
        ;

unary_abstract_declarator:
          '*'
        {
          $$=$1;
          // The below is deliberately not using pointer_type();
          // the width is added during conversion.
          stack_type($$).id(ID_frontend_pointer);
          stack_type($$).subtype()=typet(ID_abstract);
        }
        | '*' attribute_type_qualifier_list
        {
          // The type_qualifier_list belongs to the pointer,
          // not to the (missing) abstract declarator.
          // The below is deliberately not using pointer_type();
          // the width is added during conversion.
          stack_type($1).id(ID_frontend_pointer);
          stack_type($1).subtype()=typet(ID_abstract);
          $$=merge($2, $1);
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
          // The below is deliberately not using pointer_type();
          // the width is added during conversion.
          stack_type($1).id(ID_frontend_pointer);
          stack_type($1).subtype()=typet(ID_abstract);
          $2=merge($2, $1); // dest=$2
          make_subtype($3, $2); // dest=$3
          $$=$3;
        }
        | '^'
        {
          // This is an Apple extension to C/C++/Objective C.
          // http://en.wikipedia.org/wiki/Blocks_(C_language_extension)
          $$=$1;
          set($$, ID_block_pointer);
          stack_type($$).subtype()=typet(ID_abstract);
        }
        ;

parameter_unary_abstract_declarator:
          '*'
        {
          $$=$1;
          // The below is deliberately not using pointer_type();
          // the width is added during conversion.
          stack_type($$).id(ID_frontend_pointer);
          stack_type($$).subtype()=typet(ID_abstract);
        }
        | '*' attribute_type_qualifier_list
        {
          // The type_qualifier_list belongs to the pointer,
          // not to the (missing) abstract declarator.
          // The below is deliberately not using pointer_type();
          // the width is added during conversion.
          stack_type($1).id(ID_frontend_pointer);
          stack_type($1).subtype()=typet(ID_abstract);
          $$=merge($2, $1);
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
          // The below is deliberately not using pointer_type();
          // the width is added during conversion.
          stack_type($1).id(ID_frontend_pointer);
          stack_type($1).subtype()=typet(ID_abstract);
          $2=merge($2, $1); // dest=$2
          make_subtype($3, $2); // dest=$3
          $$=$3;
        }
        | '^'
        {
          // This is an Apple extension to C/C++/Objective C.
          // http://en.wikipedia.org/wiki/Blocks_(C_language_extension)
          $$=$1;
          set($$, ID_block_pointer);
          stack_type($$).subtype()=typet(ID_abstract);
        }
        ;

postfix_abstract_declarator:
          '(' unary_abstract_declarator ')'
        { $$ = $2; }
        | '(' postfix_abstract_declarator ')'
        { $$ = $2; }
        | '(' postfixing_abstract_declarator ')'
        { $$ = $2; }
        | '(' postfix_abstract_declarator ')' postfixing_abstract_declarator
        {
          /* note: this is a pointer ($2) to a function or array ($4) */
          $$=$2;
          make_subtype($$, $4);
        }
        | '(' unary_abstract_declarator ')' postfixing_abstract_declarator
        {
          /* note: this is a pointer ($2) to a function or array ($4) */
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
