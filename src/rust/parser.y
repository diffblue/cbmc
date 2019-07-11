%{
/*
Copied and modified from the Rust Github:
https://github.com/rust-lang/rust

Copyright:
The Rust Project is dual-licensed under Apache 2.0 and MIT
terms.
*/

#define YYERROR_VERBOSE
#define YYSTYPE unsigned int
#define PARSER rust_parser
#define YYSTYPE_IS_TRIVIAL 1

#include <util/std_expr.h>
#include <util/c_types.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <ansi-c/literals/convert_float_literal.h>
#include <ansi-c/gcc_types.h>
#include <ansi-c/literals/parse_float.h>
#include "rust_parser.h"
#include "rust_parseassert.h"
#include "rust_types.h"

// Make sure this matches the #define for YY_DECL in scanner.l
extern int yylex(unsigned int* yylval);
extern void yyerror(char const *s);
extern char const* yyrusttext;

symbol_exprt symbol_exprt_typeless_empty(irep_idt const& id)
{
  return symbol_exprt(id, typet(ID_empty));
}
%}

%language "c++"
%debug

%token SHL
%token SHR
%token LE
%token EQEQ
%token NE
%token GE
%token ANDAND
%token OROR
%token SHLEQ
%token SHREQ
%token MINUSEQ
%token ANDEQ
%token OREQ
%token PLUSEQ
%token STAREQ
%token SLASHEQ
%token CARETEQ
%token PERCENTEQ
%token DOTDOT
%token DOTDOTDOT
%token MOD_SEP
%token RARROW
%token LARROW
%token FAT_ARROW
%token LIT_BYTE
%token LIT_CHAR
%token LIT_INTEGER
%token LIT_FLOAT
%token LIT_STR
%token LIT_STR_RAW
%token LIT_BYTE_STR
%token LIT_BYTE_STR_RAW
%token IDENT
%token UNDERSCORE
%token LIFETIME

// keywords
%token SELF
%token STATIC
%token ABSTRACT
%token ALIGNOF
%token AS
%token BECOME
%token BREAK
%token CATCH
%token CRATE
%token DO
%token ELSE
%token ENUM
%token EXTERN
%token FALSE
%token FINAL
%token FN
%token FOR
%token IF
%token IMPL
%token IN
%token LET
%token LOOP
%token MACRO
%token MATCH
%token MOD
%token MOVE
%token MUT
%token OFFSETOF
%token OVERRIDE
%token PRIV
%token PUB
%token PURE
%token REF
%token RETURN
%token SIZEOF
%token STRUCT
%token SUPER
%token UNION
%token UNSIZED
%token TRUE
%token TRAIT
%token TYPE
%token UNSAFE
%token VIRTUAL
%token YIELD
%token DEFAULT
%token USE
%token WHILE
%token CONTINUE
%token PROC
%token BOX
%token CONST
%token WHERE
%token TYPEOF
%token INNER_DOC_COMMENT
%token OUTER_DOC_COMMENT

%token SHEBANG
%token SHEBANG_LINE
%token STATIC_LIFETIME

 /*
   Quoting from the Bison manual:

   "Finally, the resolution of conflicts works by comparing the precedence
   of the rule being considered with that of the lookahead token. If the
   token's precedence is higher, the choice is to shift. If the rule's
   precedence is higher, the choice is to reduce. If they have equal
   precedence, the choice is made based on the associativity of that
   precedence level. The verbose output file made by ‘-v’ (see Invoking
   Bison) says how each conflict was resolved"
 */

// We expect no shift/reduce or reduce/reduce conflicts in this grammar;
// all potential ambiguities are scrutinized and eliminated manually.
%expect 0

// fake-precedence symbol to cause '|' bars in lambda context to parse
// at low precedence, permit things like |x| foo = bar, where '=' is
// otherwise lower-precedence than '|'. Also used for proc() to cause
// things like proc() a + b to parse as proc() { a + b }.
%precedence LAMBDA

%precedence SELF

// MUT should be lower precedence than IDENT so that in the pat rule,
// "& MUT pat" has higher precedence than "binding_mode ident [@ pat]"
%precedence MUT

// IDENT needs to be lower than '{' so that 'foo {' is shifted when
// trying to decide if we've got a struct-construction expr (esp. in
// contexts like 'if foo { .')
//
// IDENT also needs to be lower precedence than '<' so that '<' in
// 'foo:bar . <' is shifted (in a trait reference occurring in a
// bounds list), parsing as foo:(bar<baz>) rather than (foo:bar)<baz>.
%precedence IDENT
 // Put the weak keywords that can be used as idents here as well
%precedence CATCH
%precedence DEFAULT
%precedence UNION

// A couple fake-precedence symbols to use in rules associated with +
// and < in trailing type contexts. These come up when you have a type
// in the RHS of operator-AS, such as "foo as bar<baz>". The "<" there
// has to be shifted so the parser keeps trying to parse a type, even
// though it might well consider reducing the type "bar" and then
// going on to "<" as a subsequent binop. The "+" case is with
// trailing type-bounds ("foo as bar:A+B"), for the same reason.
%precedence SHIFTPLUS

%precedence MOD_SEP
%precedence RARROW ':'

// In where clauses, "for" should have greater precedence when used as
// a higher ranked constraint than when used as the beginning of a
// for_in_type (which is a ty)
%precedence FORTYPE
%precedence FOR

// Binops & unops, and their precedences
%precedence '?'
%precedence BOX
%nonassoc DOTDOT

// RETURN needs to be lower-precedence than tokens that start
// prefix_exprs
%precedence RETURN YIELD

%right '=' SHLEQ SHREQ MINUSEQ ANDEQ OREQ PLUSEQ STAREQ SLASHEQ CARETEQ PERCENTEQ
%right LARROW
%left OROR
%left ANDAND
%left EQEQ NE
%left '<' '>' LE GE
%left '|'
%left '^'
%left '&'
%left SHL SHR
%left '+' '-'
%precedence AS
%left '*' '/' '%'
%precedence '!'

%precedence '{' '[' '(' '.'

%precedence RANGE

%start crate

%%

////////////////////////////////////////////////////////////////////////
// Part 1: Items and attributes
////////////////////////////////////////////////////////////////////////

crate
: maybe_shebang inner_attrs maybe_mod_items  { /*{o}{td}mk_node("crate", 2, $2, $3);*/ }
| maybe_shebang maybe_mod_items  { /*{o}{td}mk_node("crate", 1, $2);*/ }
;

maybe_shebang
: SHEBANG_LINE
| %empty
;

maybe_inner_attrs
: inner_attrs
| %empty                   { /*{o}$$ = mk_none();*/ }
;

inner_attrs
: inner_attr               { /*{o}$$ = mk_node("InnerAttrs", 1, $1);*/ }
| inner_attrs inner_attr   { /*{o}$$ = ext_node($1, 1, $2);*/ }
;

inner_attr
: SHEBANG '[' meta_item ']'   { /*{o}$$ = mk_node("InnerAttr", 1, $3);*/ }
| INNER_DOC_COMMENT           { /*{o}$$ = mk_node("InnerAttr", 1, mk_node("doc-comment", 1, mk_atom(yyrusttext)));*/ }
;

maybe_outer_attrs
: outer_attrs
| %empty                   { /*{o}$$ = mk_none();*/ }
;

outer_attrs
: outer_attr               { /*{o}$$ = mk_node("OuterAttrs", 1, $1);*/ }
| outer_attrs outer_attr   { /*{o}$$ = ext_node($1, 1, $2);*/ }
;

outer_attr
: '#' '[' meta_item ']'    { /*{o}$$ = $3;*/ }
| OUTER_DOC_COMMENT        { /*{o}$$ = mk_node("doc-comment", 1, mk_atom(yyrusttext));*/ }
;

meta_item
: ident                      { /*{o}$$ = mk_node("MetaWord", 1, $1);*/ }
| ident '=' lit              { /*{o}$$ = mk_node("MetaNameValue", 2, $1, $3);*/ }
| ident '(' meta_seq ')'     { /*{o}$$ = mk_node("MetaList", 2, $1, $3);*/ }
| ident '(' meta_seq ',' ')' { /*{o}$$ = mk_node("MetaList", 2, $1, $3);*/ }
;

meta_seq
: %empty                   { /*{o}$$ = mk_none();*/ }
| meta_item                { /*{o}$$ = mk_node("MetaItems", 1, $1);*/ }
| meta_seq ',' meta_item   { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

maybe_mod_items
: mod_items
| %empty             { /*{o}$$ = mk_none();*/ }
;

mod_items
: mod_item                               { /*{o}$$ = mk_node("Items", 1, $1);*/ }
| mod_items mod_item                     { /*{o}$$ = ext_node($1, 1, $2);*/ }
;

attrs_and_vis
: maybe_outer_attrs visibility           { /*{o}$$ = mk_node("AttrsAndVis", 2, $1, $2);*/ }
;

mod_item
: attrs_and_vis item    { /*{o}$$ = mk_node("Item", 2, $1, $2);*/ }
;

// items that can appear outside of a fn block
item
: stmt_item
| item_macro
;

// items that can appear in "stmts"
stmt_item
: item_static
| item_const
| item_type
| block_item
| view_item
;

item_static
: STATIC ident ':' ty '=' expr ';'  { /*{o}$$ = mk_node("ItemStatic", 3, $2, $4, $6);*/ }
| STATIC MUT ident ':' ty '=' expr ';'  { /*{o}$$ = mk_node("ItemStatic", 3, $3, $5, $7);*/ }
;

item_const
: CONST ident ':' ty '=' expr ';'  { /*{o}$$ = mk_node("ItemConst", 3, $2, $4, $6);*/ }
;

item_macro
: path_expr '!' maybe_ident parens_delimited_token_trees ';'  { /*{o}$$ = mk_node("ItemMacro", 3, $1, $3, $4);*/ }
| path_expr '!' maybe_ident braces_delimited_token_trees      { /*{o}$$ = mk_node("ItemMacro", 3, $1, $3, $4);*/ }
| path_expr '!' maybe_ident brackets_delimited_token_trees ';'{ /*{o}$$ = mk_node("ItemMacro", 3, $1, $3, $4);*/ }
;

view_item
: use_item
| extern_fn_item
| EXTERN CRATE ident ';'                      { /*{o}$$ = mk_node("ViewItemExternCrate", 1, $3);*/ }
| EXTERN CRATE ident AS ident ';'             { /*{o}$$ = mk_node("ViewItemExternCrate", 2, $3, $5);*/ }
;

extern_fn_item
: EXTERN maybe_abi item_fn                    { /*{o}$$ = mk_node("ViewItemExternFn", 2, $2, $3);*/ }
;

use_item
: USE view_path ';'                           { /*{o}$$ = mk_node("ViewItemUse", 1, $2);*/ }
;

view_path
: path_no_types_allowed                                    { /*{o}$$ = mk_node("ViewPathSimple", 1, $1);*/ }
| path_no_types_allowed MOD_SEP '{'                '}'     { /*{o}$$ = mk_node("ViewPathList", 2, $1, mk_atom("ViewPathListEmpty"));*/ }
|                       MOD_SEP '{'                '}'     { /*{o}$$ = mk_node("ViewPathList", 1, mk_atom("ViewPathListEmpty"));*/ }
| path_no_types_allowed MOD_SEP '{' idents_or_self '}'     { /*{o}$$ = mk_node("ViewPathList", 2, $1, $4);*/ }
|                       MOD_SEP '{' idents_or_self '}'     { /*{o}$$ = mk_node("ViewPathList", 1, $3);*/ }
| path_no_types_allowed MOD_SEP '{' idents_or_self ',' '}' { /*{o}$$ = mk_node("ViewPathList", 2, $1, $4);*/ }
|                       MOD_SEP '{' idents_or_self ',' '}' { /*{o}$$ = mk_node("ViewPathList", 1, $3);*/ }
| path_no_types_allowed MOD_SEP '*'                        { /*{o}$$ = mk_node("ViewPathGlob", 1, $1);*/ }
|                       MOD_SEP '*'                        { /*{o}$$ = mk_atom("ViewPathGlob");*/ }
|                               '*'                        { /*{o}$$ = mk_atom("ViewPathGlob");*/ }
|                               '{'                '}'     { /*{o}$$ = mk_atom("ViewPathListEmpty");*/ }
|                               '{' idents_or_self '}'     { /*{o}$$ = mk_node("ViewPathList", 1, $2);*/ }
|                               '{' idents_or_self ',' '}' { /*{o}$$ = mk_node("ViewPathList", 1, $2);*/ }
| path_no_types_allowed AS ident                           { /*{o}$$ = mk_node("ViewPathSimple", 2, $1, $3);*/ }
;

block_item
: item_fn
| item_unsafe_fn
| item_mod
| item_foreign_mod          { /*{o}$$ = mk_node("ItemForeignMod", 1, $1);*/ }
| item_struct
| item_enum
| item_union
| item_trait
| item_impl
;

maybe_ty_ascription
: ':' ty_sum { $$ = $2; }
| %empty     { newstack($$) = exprt("ID_emptytyascript"); }
;

maybe_init_expr
: '=' expr { $$ = $2; }
| %empty   { newstack($$) = exprt("ID_emptyinitexpr"); }
;

// structs
item_struct
: STRUCT ident generic_params maybe_where_clause struct_decl_args
{
  /*{o}$$ = mk_node("ItemStruct", 4, $2, $3, $4, $5);*/
}
| STRUCT ident generic_params struct_tuple_args maybe_where_clause ';'
{
  /*{o}$$ = mk_node("ItemStruct", 4, $2, $3, $4, $5);*/
}
| STRUCT ident generic_params maybe_where_clause ';'
{
  /*{o}$$ = mk_node("ItemStruct", 3, $2, $3, $4);*/
}
;

struct_decl_args
: '{' struct_decl_fields '}'                  { /*{o}$$ = $2;*/ }
| '{' struct_decl_fields ',' '}'              { /*{o}$$ = $2;*/ }
;

struct_tuple_args
: '(' struct_tuple_fields ')'                 { /*{o}$$ = $2;*/ }
| '(' struct_tuple_fields ',' ')'             { /*{o}$$ = $2;*/ }
;

struct_decl_fields
: struct_decl_field                           { /*{o}$$ = mk_node("StructFields", 1, $1);*/ }
| struct_decl_fields ',' struct_decl_field    { /*{o}$$ = ext_node($1, 1, $3);*/ }
| %empty                                      { /*{o}$$ = mk_none();*/ }
;

struct_decl_field
: attrs_and_vis ident ':' ty_sum              { /*{o}$$ = mk_node("StructField", 3, $1, $2, $4);*/ }
;

struct_tuple_fields
: struct_tuple_field                          { /*{o}$$ = mk_node("StructFields", 1, $1);*/ }
| struct_tuple_fields ',' struct_tuple_field  { /*{o}$$ = ext_node($1, 1, $3);*/ }
| %empty                                      { /*{o}$$ = mk_none();*/ }
;

struct_tuple_field
: attrs_and_vis ty_sum                    { /*{o}$$ = mk_node("StructField", 2, $1, $2);*/ }
;

// enums
item_enum
: ENUM ident generic_params maybe_where_clause '{' enum_defs '}'     { /*{o}$$ = mk_node("ItemEnum", 0);*/ }
| ENUM ident generic_params maybe_where_clause '{' enum_defs ',' '}' { /*{o}$$ = mk_node("ItemEnum", 0);*/ }
;

enum_defs
: enum_def               { /*{o}$$ = mk_node("EnumDefs", 1, $1);*/ }
| enum_defs ',' enum_def { /*{o}$$ = ext_node($1, 1, $3);*/ }
| %empty                 { /*{o}$$ = mk_none();*/ }
;

enum_def
: attrs_and_vis ident enum_args { /*{o}$$ = mk_node("EnumDef", 3, $1, $2, $3);*/ }
;

enum_args
: '{' struct_decl_fields '}'     { /*{o}$$ = mk_node("EnumArgs", 1, $2);*/ }
| '{' struct_decl_fields ',' '}' { /*{o}$$ = mk_node("EnumArgs", 1, $2);*/ }
| '(' maybe_ty_sums ')'          { /*{o}$$ = mk_node("EnumArgs", 1, $2);*/ }
| '=' expr                       { /*{o}$$ = mk_node("EnumArgs", 1, $2);*/ }
| %empty                         { /*{o}$$ = mk_none();*/ }
;

// unions
item_union
: UNION ident generic_params maybe_where_clause '{' struct_decl_fields '}'     { /*{o}$$ = mk_node("ItemUnion", 0);*/ }
| UNION ident generic_params maybe_where_clause '{' struct_decl_fields ',' '}' { /*{o}$$ = mk_node("ItemUnion", 0);*/ }

item_mod
: MOD ident ';'                                 { /*{o}$$ = mk_node("ItemMod", 1, $2);*/ }
| MOD ident '{' maybe_mod_items '}'             { /*{o}$$ = mk_node("ItemMod", 2, $2, $4);*/ }
| MOD ident '{' inner_attrs maybe_mod_items '}' { /*{o}$$ = mk_node("ItemMod", 3, $2, $4, $5);*/ }
;

item_foreign_mod
: EXTERN maybe_abi '{' maybe_foreign_items '}'             { /*{o}$$ = mk_node("ItemForeignMod", 1, $4);*/ }
| EXTERN maybe_abi '{' inner_attrs maybe_foreign_items '}' { /*{o}$$ = mk_node("ItemForeignMod", 2, $4, $5);*/ }
;

maybe_abi
: str
| %empty { /*{o}$$ = mk_none();*/ }
;

maybe_foreign_items
: foreign_items
| %empty { /*{o}$$ = mk_none();*/ }
;

foreign_items
: foreign_item               { /*{o}$$ = mk_node("ForeignItems", 1, $1);*/ }
| foreign_items foreign_item { /*{o}$$ = ext_node($1, 1, $2);*/ }
;

foreign_item
: attrs_and_vis STATIC item_foreign_static { /*{o}$$ = mk_node("ForeignItem", 2, $1, $3);*/ }
| attrs_and_vis item_foreign_fn            { /*{o}$$ = mk_node("ForeignItem", 2, $1, $2);*/ }
| attrs_and_vis UNSAFE item_foreign_fn     { /*{o}$$ = mk_node("ForeignItem", 2, $1, $3);*/ }
;

item_foreign_static
: maybe_mut ident ':' ty ';'               { /*{o}$$ = mk_node("StaticItem", 3, $1, $2, $4);*/ }
;

item_foreign_fn
: FN ident generic_params fn_decl_allow_variadic maybe_where_clause ';' { /*{o}$$ = mk_node("ForeignFn", 4, $2, $3, $4, $5);*/ }
;

fn_decl_allow_variadic
: fn_params_allow_variadic ret_ty { /*{o}$$ = mk_node("FnDecl", 2, $1, $2);*/ }
;

fn_params_allow_variadic
: '(' ')'                      { /*{o}$$ = mk_none();*/ }
| '(' params ')'               { /*{o}$$ = $2;*/ }
| '(' params ',' ')'           { /*{o}$$ = $2;*/ }
| '(' params ',' DOTDOTDOT ')' { /*{o}$$ = $2;*/ }
;

visibility
: PUB      { /*{o}$$ = mk_atom("Public");*/ }
| %empty   { /*{o}$$ = mk_atom("Inherited");*/ }
;

idents_or_self
: ident_or_self                    { /*{o}$$ = mk_node("IdentsOrSelf", 1, $1);*/ }
| idents_or_self AS ident          { /*{o}$$ = mk_node("IdentsOrSelf", 2, $1, $3);*/ }
| idents_or_self ',' ident_or_self { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

ident_or_self
: ident
| SELF  { /*{o}$$ = mk_atom(yyrusttext);*/ }
;

item_type
: TYPE ident generic_params maybe_where_clause '=' ty_sum ';'  { /*{o}$$ = mk_node("ItemTy", 4, $2, $3, $4, $6);*/ }
;

for_sized
: FOR '?' ident { /*{o}$$ = mk_node("ForSized", 1, $3);*/ }
| FOR ident '?' { /*{o}$$ = mk_node("ForSized", 1, $2);*/ }
| %empty        { /*{o}$$ = mk_none();*/ }
;

item_trait
: maybe_unsafe TRAIT ident generic_params for_sized maybe_ty_param_bounds maybe_where_clause '{' maybe_trait_items '}'
{
  /*{o}$$ = mk_node("ItemTrait", 7, $1, $3, $4, $5, $6, $7, $9);*/
}
;

maybe_trait_items
: trait_items
| %empty { /*{o}$$ = mk_none();*/ }
;

trait_items
: trait_item               { /*{o}$$ = mk_node("TraitItems", 1, $1);*/ }
| trait_items trait_item   { /*{o}$$ = ext_node($1, 1, $2);*/ }
;

trait_item
: trait_const
| trait_type
| trait_method
| maybe_outer_attrs item_macro { /*{o}$$ = mk_node("TraitMacroItem", 2, $1, $2);*/ }
;

trait_const
: maybe_outer_attrs CONST ident maybe_ty_ascription maybe_const_default ';' { /*{o}$$ = mk_node("ConstTraitItem", 4, $1, $3, $4, $5);*/ }
;

maybe_const_default
: '=' expr { /*{o}$$ = mk_node("ConstDefault", 1, $2);*/ }
| %empty   { /*{o}$$ = mk_none();*/ }
;

trait_type
: maybe_outer_attrs TYPE ty_param ';' { /*{o}$$ = mk_node("TypeTraitItem", 2, $1, $3);*/ }
;

maybe_unsafe
: UNSAFE { /*{o}$$ = mk_atom("Unsafe");*/ }
| %empty { /*{o}$$ = mk_none();*/ }
;

maybe_default_maybe_unsafe
: DEFAULT UNSAFE { /*{o}$$ = mk_atom("DefaultUnsafe");*/ }
| DEFAULT        { /*{o}$$ = mk_atom("Default");*/ }
|         UNSAFE { /*{o}$$ = mk_atom("Unsafe");*/ }
| %empty { /*{o}$$ = mk_none();*/ }

trait_method
: type_method { /*{o}$$ = mk_node("Required", 1, $1);*/ }
| method      { /*{o}$$ = mk_node("Provided", 1, $1);*/ }
;

type_method
: maybe_outer_attrs maybe_unsafe FN ident generic_params fn_decl_with_self_allow_anon_params maybe_where_clause ';'
{
  /*{o}$$ = mk_node("TypeMethod", 6, $1, $2, $4, $5, $6, $7);*/
}
| maybe_outer_attrs CONST maybe_unsafe FN ident generic_params fn_decl_with_self_allow_anon_params maybe_where_clause ';'
{
  /*{o}$$ = mk_node("TypeMethod", 6, $1, $3, $5, $6, $7, $8);*/
}
| maybe_outer_attrs maybe_unsafe EXTERN maybe_abi FN ident generic_params fn_decl_with_self_allow_anon_params maybe_where_clause ';'
{
  /*{o}$$ = mk_node("TypeMethod", 7, $1, $2, $4, $6, $7, $8, $9);*/
}
;

method
: maybe_outer_attrs maybe_unsafe FN ident generic_params fn_decl_with_self_allow_anon_params maybe_where_clause inner_attrs_and_block
{
  /*{o}$$ = mk_node("Method", 7, $1, $2, $4, $5, $6, $7, $8);*/
}
| maybe_outer_attrs CONST maybe_unsafe FN ident generic_params fn_decl_with_self_allow_anon_params maybe_where_clause inner_attrs_and_block
{
  /*{o}$$ = mk_node("Method", 7, $1, $3, $5, $6, $7, $8, $9);*/
}
| maybe_outer_attrs maybe_unsafe EXTERN maybe_abi FN ident generic_params fn_decl_with_self_allow_anon_params maybe_where_clause inner_attrs_and_block
{
  /*{o}$$ = mk_node("Method", 8, $1, $2, $4, $6, $7, $8, $9, $10);*/
}
;

impl_method
: attrs_and_vis maybe_default maybe_unsafe FN ident generic_params fn_decl_with_self maybe_where_clause inner_attrs_and_block
{
  /*{o}$$ = mk_node("Method", 8, $1, $2, $3, $5, $6, $7, $8, $9);*/
}
| attrs_and_vis maybe_default CONST maybe_unsafe FN ident generic_params fn_decl_with_self maybe_where_clause inner_attrs_and_block
{
  /*{o}$$ = mk_node("Method", 8, $1, $2, $4, $6, $7, $8, $9, $10);*/
}
| attrs_and_vis maybe_default maybe_unsafe EXTERN maybe_abi FN ident generic_params fn_decl_with_self maybe_where_clause inner_attrs_and_block
{
  /*{o}$$ = mk_node("Method", 9, $1, $2, $3, $5, $7, $8, $9, $10, $11);*/
}
;

// There are two forms of impl:
//
// impl (<...>)? TY { ... }
// impl (<...>)? TRAIT for TY { ... }
//
// Unfortunately since TY can begin with '<' itself -- as part of a
// TyQualifiedPath type -- there's an s/r conflict when we see '<' after IMPL:
// should we reduce one of the early rules of TY (such as maybe_once)
// or shall we continue shifting into the generic_params list for the
// impl?
//
// The production parser disambiguates a different case here by
// permitting / requiring the user to provide parens around types when
// they are ambiguous with traits. We do the same here, regrettably,
// by splitting ty into ty and ty_prim.
item_impl
: maybe_default_maybe_unsafe IMPL generic_params ty_prim_sum maybe_where_clause '{' maybe_inner_attrs maybe_impl_items '}'
{
  /*{o}$$ = mk_node("ItemImpl", 6, $1, $3, $4, $5, $7, $8);*/
}
| maybe_default_maybe_unsafe IMPL generic_params '(' ty ')' maybe_where_clause '{' maybe_inner_attrs maybe_impl_items '}'
{
  /*{o}$$ = mk_node("ItemImpl", 6, $1, $3, 5, $6, $9, $10);*/
}
| maybe_default_maybe_unsafe IMPL generic_params trait_ref FOR ty_sum maybe_where_clause '{' maybe_inner_attrs maybe_impl_items '}'
{
  /*{o}$$ = mk_node("ItemImpl", 6, $3, $4, $6, $7, $9, $10);*/
}
| maybe_default_maybe_unsafe IMPL generic_params '!' trait_ref FOR ty_sum maybe_where_clause '{' maybe_inner_attrs maybe_impl_items '}'
{
  /*{o}$$ = mk_node("ItemImplNeg", 7, $1, $3, $5, $7, $8, $10, $11);*/
}
| maybe_default_maybe_unsafe IMPL generic_params trait_ref FOR DOTDOT '{' '}'
{
  /*{o}$$ = mk_node("ItemImplDefault", 3, $1, $3, $4);*/
}
| maybe_default_maybe_unsafe IMPL generic_params '!' trait_ref FOR DOTDOT '{' '}'
{
  /*{o}$$ = mk_node("ItemImplDefaultNeg", 3, $1, $3, $4);*/
}
;

maybe_impl_items
: impl_items
| %empty { /*{o}$$ = mk_none();*/ }
;

impl_items
: impl_item               { /*{o}$$ = mk_node("ImplItems", 1, $1);*/ }
| impl_item impl_items    { /*{o}$$ = ext_node($1, 1, $2);*/ }
;

impl_item
: impl_method
| attrs_and_vis item_macro { /*{o}$$ = mk_node("ImplMacroItem", 2, $1, $2);*/ }
| impl_const
| impl_type
;

maybe_default
: DEFAULT { /*{o}$$ = mk_atom("Default");*/ }
| %empty { /*{o}$$ = mk_none();*/ }
;

impl_const
: attrs_and_vis maybe_default item_const { /*{o}$$ = mk_node("ImplConst", 3, $1, $2, $3);*/ }
;

impl_type
: attrs_and_vis maybe_default TYPE ident generic_params '=' ty_sum ';'  { /*{o}$$ = mk_node("ImplType", 5, $1, $2, $4, $5, $7);*/ }
;

item_fn
: FN ident generic_params fn_decl maybe_where_clause inner_attrs_and_block
{
  /*{o}$$ = mk_node("ItemFn", 5, $2, $3, $4, $5, $6);*/
  // implied return value
  // if function has a return type
  if(parser_stack($4).type().id() != ID_empty)
  {
    code_blockt& body = to_code_block(to_code(parser_stack($6)));
    codet& last_statement = to_code(body.operands().back());
    irep_idt statement = last_statement.get_statement();
    if(statement == ID_expression)
    {
      body.operands().back() = code_returnt(to_code_expression(last_statement).expression());
    }
    else if(statement == ID_block)
    {
      side_effect_exprt rhs(ID_statement_expression, exprt::operandst(), typet(), source_locationt());
      rhs.add_to_operands(to_code_block(last_statement));
      body.operands().back() = code_returnt(rhs);
    }
  }

  // actual function definition
  code_function_callt x(parser_stack($2), code_function_callt::argumentst(parser_stack($4).operands()));
  x.type() = parser_stack($4).type();
  newstack($$).swap(x);

  //TODO_main: This might not belong here long-term, if crates need packaging up especially
  rust_declarationt a;
  code_typet::parameterst params;
  Forall_operands(it, parser_stack($4))
  {
    symbol_exprt& symbol = to_symbol_expr(*it);
    params.push_back(code_typet::parametert(symbol.type()));
    params.back().set_identifier(symbol.get_identifier());
  }
  parser_stack($2).type() = code_typet(params, parser_stack($4).type());
  a.add_declarator(to_symbol_expr(parser_stack($2)));
  a.add_value(to_code_block(to_code(parser_stack($6))));
  PARSER.parse_tree.items.push_back(std::move(a));
}
| CONST FN ident generic_params fn_decl maybe_where_clause inner_attrs_and_block
{
  /*{o}$$ = mk_node("ItemFn", 5, $3, $4, $5, $6, $7);*/
}
;

item_unsafe_fn
: UNSAFE FN ident generic_params fn_decl maybe_where_clause inner_attrs_and_block
{
  /*{o}$$ = mk_node("ItemUnsafeFn", 5, $3, $4, $5, $6, $7);*/
}
| CONST UNSAFE FN ident generic_params fn_decl maybe_where_clause inner_attrs_and_block
{
  /*{o}$$ = mk_node("ItemUnsafeFn", 5, $4, $5, $6, $7, $8);*/
}
| UNSAFE EXTERN maybe_abi FN ident generic_params fn_decl maybe_where_clause inner_attrs_and_block
{
  /*{o}$$ = mk_node("ItemUnsafeFn", 6, $3, $5, $6, $7, $8, $9);*/
}
;

fn_decl
: fn_params ret_ty   { parser_stack($1).type() = parser_stack($2).type();
                       $$ = $1; }
;

fn_decl_with_self
: fn_params_with_self ret_ty   { /*{o}$$ = mk_node("FnDecl", 2, $1, $2);*/ }
;

fn_decl_with_self_allow_anon_params
: fn_anon_params_with_self ret_ty   { /*{o}$$ = mk_node("FnDecl", 2, $1, $2);*/ }
;

fn_params
: '(' maybe_params ')'  { $$ = $2; }
;

fn_anon_params
: '(' anon_param anon_params_allow_variadic_tail ')' { /*{o}$$ = ext_node($2, 1, $3);*/ }
| '(' ')'                                            { /*{o}$$ = mk_none();*/ }
;

fn_params_with_self
: '(' maybe_mut SELF maybe_ty_ascription maybe_comma_params ')'              { /*{o}$$ = mk_node("SelfLower", 3, $2, $4, $5);*/ }
| '(' '&' maybe_mut SELF maybe_ty_ascription maybe_comma_params ')'          { /*{o}$$ = mk_node("SelfRegion", 3, $3, $5, $6);*/ }
| '(' '&' lifetime maybe_mut SELF maybe_ty_ascription maybe_comma_params ')' { /*{o}$$ = mk_node("SelfRegion", 4, $3, $4, $6, $7);*/ }
| '(' maybe_params ')'                                                       { /*{o}$$ = mk_node("SelfStatic", 1, $2);*/ }
;

fn_anon_params_with_self
: '(' maybe_mut SELF maybe_ty_ascription maybe_comma_anon_params ')'              { /*{o}$$ = mk_node("SelfLower", 3, $2, $4, $5);*/ }
| '(' '&' maybe_mut SELF maybe_ty_ascription maybe_comma_anon_params ')'          { /*{o}$$ = mk_node("SelfRegion", 3, $3, $5, $6);*/ }
| '(' '&' lifetime maybe_mut SELF maybe_ty_ascription maybe_comma_anon_params ')' { /*{o}$$ = mk_node("SelfRegion", 4, $3, $4, $6, $7);*/ }
| '(' maybe_anon_params ')'                                                       { /*{o}$$ = mk_node("SelfStatic", 1, $2);*/ }
;

maybe_params
: params      { $$ = $1; }
| params ','  { $$ = $1; }
| %empty      { newstack($$) = multi_ary_exprt(ID_parameters, exprt::operandst(), typet()); }
;

params
: param                { exprt::operandst params;
                         params.push_back(parser_stack($1));
                         newstack($$) = multi_ary_exprt(ID_parameters, params, typet()); }
| params ',' param     { parser_stack($1).operands().push_back(parser_stack($3)); }
;

param
: pat ':' ty_sum   { parser_stack($1).type() = parser_stack($3).type();
                     $$ = $1; }
;

inferrable_params
: inferrable_param                       { /*{o}$$ = mk_node("InferrableParams", 1, $1);*/ }
| inferrable_params ',' inferrable_param { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

inferrable_param
: pat maybe_ty_ascription { /*{o}$$ = mk_node("InferrableParam", 2, $1, $2);*/ }
;

maybe_comma_params
: ','            { /*{o}$$ = mk_none();*/ }
| ',' params     { /*{o}$$ = $2;*/ }
| ',' params ',' { /*{o}$$ = $2;*/ }
| %empty         { /*{o}$$ = mk_none();*/ }
;

maybe_comma_anon_params
: ','                 { /*{o}$$ = mk_none();*/ }
| ',' anon_params     { /*{o}$$ = $2;*/ }
| ',' anon_params ',' { /*{o}$$ = $2;*/ }
| %empty              { /*{o}$$ = mk_none();*/ }
;

maybe_anon_params
: anon_params
| anon_params ','
| %empty      { /*{o}$$ = mk_none();*/ }
;

anon_params
: anon_param                 { /*{o}$$ = mk_node("Args", 1, $1);*/ }
| anon_params ',' anon_param { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

// anon means it's allowed to be anonymous (type-only), but it can
// still have a name
anon_param
: named_arg ':' ty   { /*{o}$$ = mk_node("Arg", 2, $1, $3);*/ }
| ty
;

anon_params_allow_variadic_tail
: ',' DOTDOTDOT                                  { /*{o}$$ = mk_none();*/ }
| ',' anon_param anon_params_allow_variadic_tail { /*{o}$$ = mk_node("Args", 2, $2, $3);*/ }
| %empty                                         { /*{o}$$ = mk_none();*/ }
;

named_arg
: ident
| UNDERSCORE        { /*{o}$$ = mk_atom("PatWild");*/ }
| '&' ident         { /*{o}$$ = $2;*/ }
| '&' UNDERSCORE    { /*{o}$$ = mk_atom("PatWild");*/ }
| ANDAND ident      { /*{o}$$ = $2;*/ }
| ANDAND UNDERSCORE { /*{o}$$ = mk_atom("PatWild");*/ }
| MUT ident         { /*{o}$$ = $2;*/ }
;

ret_ty
: RARROW '!'         { newstack($$) = symbol_exprt_typeless_empty(""); }
| RARROW ty          { $$ = $2; }
| %prec IDENT %empty { newstack($$) = symbol_exprt_typeless_empty(""); }
;

generic_params
: '<' '>'                             { /*{o}$$ = mk_node("Generics", 2, mk_none(), mk_none());*/ }
| '<' lifetimes '>'                   { /*{o}$$ = mk_node("Generics", 2, $2, mk_none());*/ }
| '<' lifetimes ',' '>'               { /*{o}$$ = mk_node("Generics", 2, $2, mk_none());*/ }
| '<' lifetimes SHR                   { /*{o}push_back('>'); $$ = mk_node("Generics", 2, $2, mk_none());*/ }
| '<' lifetimes ',' SHR               { /*{o}push_back('>'); $$ = mk_node("Generics", 2, $2, mk_none());*/ }
| '<' lifetimes ',' ty_params '>'     { /*{o}$$ = mk_node("Generics", 2, $2, $4);*/ }
| '<' lifetimes ',' ty_params ',' '>' { /*{o}$$ = mk_node("Generics", 2, $2, $4);*/ }
| '<' lifetimes ',' ty_params SHR     { /*{o}push_back('>'); $$ = mk_node("Generics", 2, $2, $4);*/ }
| '<' lifetimes ',' ty_params ',' SHR { /*{o}push_back('>'); $$ = mk_node("Generics", 2, $2, $4);*/ }
| '<' ty_params '>'                   { /*{o}$$ = mk_node("Generics", 2, mk_none(), $2);*/ }
| '<' ty_params ',' '>'               { /*{o}$$ = mk_node("Generics", 2, mk_none(), $2);*/ }
| '<' ty_params SHR                   { /*{o}push_back('>'); $$ = mk_node("Generics", 2, mk_none(), $2);*/ }
| '<' ty_params ',' SHR               { /*{o}push_back('>'); $$ = mk_node("Generics", 2, mk_none(), $2);*/ }
| %empty                              { newstack($$); }
;

maybe_where_clause
: %empty                              { /*{o}$$ = mk_none();*/ }
| where_clause
;

where_clause
: WHERE where_predicates              { /*{o}$$ = mk_node("WhereClause", 1, $2);*/ }
| WHERE where_predicates ','          { /*{o}$$ = mk_node("WhereClause", 1, $2);*/ }
;

where_predicates
: where_predicate                      { /*{o}$$ = mk_node("WherePredicates", 1, $1);*/ }
| where_predicates ',' where_predicate { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

where_predicate
: maybe_for_lifetimes lifetime ':' bounds    { /*{o}$$ = mk_node("WherePredicate", 3, $1, $2, $4);*/ }
| maybe_for_lifetimes ty ':' ty_param_bounds { /*{o}$$ = mk_node("WherePredicate", 3, $1, $2, $4);*/ }
;

maybe_for_lifetimes
: FOR '<' lifetimes '>' { /*{o}$$ = mk_none();*/ }
| %prec FORTYPE %empty  { /*{o}$$ = mk_none();*/ }

ty_params
: ty_param               { /*{o}$$ = mk_node("TyParams", 1, $1);*/ }
| ty_params ',' ty_param { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

// A path with no type parameters; e.g. `foo::bar::Baz`
//
// These show up in 'use' view-items, because these are processed
// without respect to types.
path_no_types_allowed
: ident                               { /*{o}$$ = mk_node("ViewPath", 1, $1);*/ }
| MOD_SEP ident                       { /*{o}$$ = mk_node("ViewPath", 1, $2);*/ }
| SELF                                { /*{o}$$ = mk_node("ViewPath", 1, mk_atom("Self"));*/ }
| MOD_SEP SELF                        { /*{o}$$ = mk_node("ViewPath", 1, mk_atom("Self"));*/ }
| SUPER                               { /*{o}$$ = mk_node("ViewPath", 1, mk_atom("Super"));*/ }
| MOD_SEP SUPER                       { /*{o}$$ = mk_node("ViewPath", 1, mk_atom("Super"));*/ }
| path_no_types_allowed MOD_SEP ident { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

// A path with a lifetime and type parameters, with no double colons
// before the type parameters; e.g. `foo::bar<'a>::Baz<T>`
//
// These show up in "trait references", the components of
// type-parameter bounds lists, as well as in the prefix of the
// path_generic_args_and_bounds rule, which is the full form of a
// named typed expression.
//
// They do not have (nor need) an extra '::' before '<' because
// unlike in expr context, there are no "less-than" type exprs to
// be ambiguous with.
path_generic_args_without_colons
: %prec IDENT ident                                                           { /*{o}$$ = mk_node("components", 1, $1);*/
                                                                                $$ = $1; }
| %prec IDENT ident generic_args                                              { /*{o}$$ = mk_node("components", 2, $1, $2);*/ }
| %prec IDENT ident '(' maybe_ty_sums ')' ret_ty                              { /*{o}$$ = mk_node("components", 2, $1, $3);*/ }
| %prec IDENT path_generic_args_without_colons MOD_SEP ident                  { /*{o}$$ = ext_node($1, 1, $3);*/ }
| %prec IDENT path_generic_args_without_colons MOD_SEP ident generic_args     { /*{o}$$ = ext_node($1, 2, $3, $4);*/ }
| %prec IDENT path_generic_args_without_colons MOD_SEP ident '(' maybe_ty_sums ')' ret_ty
                                                                              { /*{o}$$ = ext_node($1, 2, $3, $5);*/ }
;

generic_args
: '<' generic_values '>'   { /*{o}$$ = $2;*/ }
| '<' generic_values SHR   { /*{o}push_back('>'); $$ = $2;*/ }
| '<' generic_values GE    { /*{o}push_back('='); $$ = $2;*/ }
| '<' generic_values SHREQ { /*{o}push_back('>'); push_back('='); $$ = $2;*/ }
// If generic_args starts with "<<", the first arg must be a
// TyQualifiedPath because that's the only type that can start with a
// '<'. This rule parses that as the first ty_sum and then continues
// with the rest of generic_values.
| SHL ty_qualified_path_and_generic_values '>'   { /*{o}$$ = $2;*/ }
| SHL ty_qualified_path_and_generic_values SHR   { /*{o}push_back('>'); $$ = $2;*/ }
| SHL ty_qualified_path_and_generic_values GE    { /*{o}push_back('='); $$ = $2;*/ }
| SHL ty_qualified_path_and_generic_values SHREQ { /*{o}push_back('>'); push_back('='); $$ = $2;*/ }
;

generic_values
: maybe_ty_sums_and_or_bindings { /*{o}$$ = mk_node("GenericValues", 1, $1);*/ }
;

maybe_ty_sums_and_or_bindings
: ty_sums
| ty_sums ','
| ty_sums ',' bindings { /*{o}$$ = mk_node("TySumsAndBindings", 2, $1, $3);*/ }
| bindings
| bindings ','
| %empty               { /*{o}$$ = mk_none();*/ }
;

maybe_bindings
: ',' bindings { /*{o}$$ = $2;*/ }
| %empty       { /*{o}$$ = mk_none();*/ }
;

////////////////////////////////////////////////////////////////////////
// Part 2: Patterns
////////////////////////////////////////////////////////////////////////

pat
: UNDERSCORE                                      { /*{o}$$ = mk_atom("PatWild");*/ }
| '&' pat                                         { /*{o}$$ = mk_node("PatRegion", 1, $2);*/ }
| '&' MUT pat                                     { /*{o}$$ = mk_node("PatRegion", 1, $3);*/ }
| ANDAND pat                                      { /*{o}$$ = mk_node("PatRegion", 1, mk_node("PatRegion", 1, $2));*/ }
| '(' ')'                                         { /*{o}$$ = mk_atom("PatUnit");*/ }
| '(' pat_tup ')'                                 { /*{o}$$ = mk_node("PatTup", 1, $2);*/ }
| '[' pat_vec ']'                                 { /*{o}$$ = mk_node("PatVec", 1, $2);*/ }
| lit_or_path
| lit_or_path DOTDOTDOT lit_or_path               { /*{o}$$ = mk_node("PatRange", 2, $1, $3);*/ }
| path_expr '{' pat_struct '}'                    { /*{o}$$ = mk_node("PatStruct", 2, $1, $3);*/ }
| path_expr '(' ')'                               { /*{o}$$ = mk_node("PatEnum", 2, $1, mk_none());*/ }
| path_expr '(' pat_tup ')'                       { /*{o}$$ = mk_node("PatEnum", 2, $1, $3);*/ }
| path_expr '!' maybe_ident delimited_token_trees { /*{o}$$ = mk_node("PatMac", 3, $1, $3, $4);*/ }
| binding_mode ident                              { /*{o}$$ = mk_node("PatIdent", 2, $1, $2);*/
                                                    //TODO: ignoring mut. if other binding modes are important, add them
                                                    $$ = $2; }
|              ident '@' pat                      { /*{o}$$ = mk_node("PatIdent", 3, mk_node("BindByValue", 1, mk_atom("MutImmutable")), $1, $3);*/ }
| binding_mode ident '@' pat                      { /*{o}$$ = mk_node("PatIdent", 3, $1, $2, $4);*/ }
| BOX pat                                         { /*{o}$$ = mk_node("PatUniq", 1, $2);*/ }
| '<' ty_sum maybe_as_trait_ref '>' MOD_SEP ident { /*{o}$$ = mk_node("PatQualifiedPath", 3, $2, $3, $6);*/ }
| SHL ty_sum maybe_as_trait_ref '>' MOD_SEP ident maybe_as_trait_ref '>' MOD_SEP ident
{
  /*{o}$$ = mk_node("PatQualifiedPath", 3, mk_node("PatQualifiedPath", 3, $2, $3, $6), $7, $10);*/
}
;

pats_or
: pat              { /*{o}$$ = mk_node("Pats", 1, $1);*/ }
| pats_or '|' pat  { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

binding_mode
: REF         { /*{o}$$ = mk_node("BindByRef", 1, mk_atom("MutImmutable"));*/ }
| REF MUT     { /*{o}$$ = mk_node("BindByRef", 1, mk_atom("MutMutable"));*/ }
| MUT         { /*{o}$$ = mk_node("BindByValue", 1, mk_atom("MutMutable"));*/ }
;

lit_or_path
: path_expr    { $$ = $1; }
| lit          { $$ = $1; }
| '-' lit      { /*{o}$$ = mk_node("PatLit", 1, $2);*/ }
;

pat_field
:                  ident        { /*{o}$$ = mk_node("PatField", 1, $1);*/ }
|     binding_mode ident        { /*{o}$$ = mk_node("PatField", 2, $1, $2);*/ }
| BOX              ident        { /*{o}$$ = mk_node("PatField", 2, mk_atom("box"), $2);*/ }
| BOX binding_mode ident        { /*{o}$$ = mk_node("PatField", 3, mk_atom("box"), $2, $3);*/ }
|              ident ':' pat    { /*{o}$$ = mk_node("PatField", 2, $1, $3);*/ }
| binding_mode ident ':' pat    { /*{o}$$ = mk_node("PatField", 3, $1, $2, $4);*/ }
|        LIT_INTEGER ':' pat    { /*{o}$$ = mk_node("PatField", 2, mk_atom(yyrusttext), $3);*/ }
;

pat_fields
: pat_field                  { /*{o}$$ = mk_node("PatFields", 1, $1);*/ }
| pat_fields ',' pat_field   { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

pat_struct
: pat_fields                 { /*{o}$$ = mk_node("PatStruct", 2, $1, mk_atom("false"));*/ }
| pat_fields ','             { /*{o}$$ = mk_node("PatStruct", 2, $1, mk_atom("false"));*/ }
| pat_fields ',' DOTDOT      { /*{o}$$ = mk_node("PatStruct", 2, $1, mk_atom("true"));*/ }
| DOTDOT                     { /*{o}$$ = mk_node("PatStruct", 1, mk_atom("true"));*/ }
| %empty                     { /*{o}$$ = mk_node("PatStruct", 1, mk_none());*/ }
;

pat_tup
: pat_tup_elts                                  { /*{o}$$ = mk_node("PatTup", 2, $1, mk_none());*/ }
| pat_tup_elts                             ','  { /*{o}$$ = mk_node("PatTup", 2, $1, mk_none());*/ }
| pat_tup_elts     DOTDOT                       { /*{o}$$ = mk_node("PatTup", 2, $1, mk_none());*/ }
| pat_tup_elts ',' DOTDOT                       { /*{o}$$ = mk_node("PatTup", 2, $1, mk_none());*/ }
| pat_tup_elts     DOTDOT ',' pat_tup_elts      { /*{o}$$ = mk_node("PatTup", 2, $1, $4);*/ }
| pat_tup_elts     DOTDOT ',' pat_tup_elts ','  { /*{o}$$ = mk_node("PatTup", 2, $1, $4);*/ }
| pat_tup_elts ',' DOTDOT ',' pat_tup_elts      { /*{o}$$ = mk_node("PatTup", 2, $1, $5);*/ }
| pat_tup_elts ',' DOTDOT ',' pat_tup_elts ','  { /*{o}$$ = mk_node("PatTup", 2, $1, $5);*/ }
|                  DOTDOT ',' pat_tup_elts      { /*{o}$$ = mk_node("PatTup", 2, mk_none(), $3);*/ }
|                  DOTDOT ',' pat_tup_elts ','  { /*{o}$$ = mk_node("PatTup", 2, mk_none(), $3);*/ }
|                  DOTDOT                       { /*{o}$$ = mk_node("PatTup", 2, mk_none(), mk_none());*/ }
;

pat_tup_elts
: pat                    { /*{o}$$ = mk_node("PatTupElts", 1, $1);*/ }
| pat_tup_elts ',' pat   { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

pat_vec
: pat_vec_elts                                  { /*{o}$$ = mk_node("PatVec", 2, $1, mk_none());*/ }
| pat_vec_elts                             ','  { /*{o}$$ = mk_node("PatVec", 2, $1, mk_none());*/ }
| pat_vec_elts     DOTDOT                       { /*{o}$$ = mk_node("PatVec", 2, $1, mk_none());*/ }
| pat_vec_elts ',' DOTDOT                       { /*{o}$$ = mk_node("PatVec", 2, $1, mk_none());*/ }
| pat_vec_elts     DOTDOT ',' pat_vec_elts      { /*{o}$$ = mk_node("PatVec", 2, $1, $4);*/ }
| pat_vec_elts     DOTDOT ',' pat_vec_elts ','  { /*{o}$$ = mk_node("PatVec", 2, $1, $4);*/ }
| pat_vec_elts ',' DOTDOT ',' pat_vec_elts      { /*{o}$$ = mk_node("PatVec", 2, $1, $5);*/ }
| pat_vec_elts ',' DOTDOT ',' pat_vec_elts ','  { /*{o}$$ = mk_node("PatVec", 2, $1, $5);*/ }
|                  DOTDOT ',' pat_vec_elts      { /*{o}$$ = mk_node("PatVec", 2, mk_none(), $3);*/ }
|                  DOTDOT ',' pat_vec_elts ','  { /*{o}$$ = mk_node("PatVec", 2, mk_none(), $3);*/ }
|                  DOTDOT                       { /*{o}$$ = mk_node("PatVec", 2, mk_none(), mk_none());*/ }
| %empty                                        { /*{o}$$ = mk_node("PatVec", 2, mk_none(), mk_none());*/ }
;

pat_vec_elts
: pat                    { /*{o}$$ = mk_node("PatVecElts", 1, $1);*/ }
| pat_vec_elts ',' pat   { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

////////////////////////////////////////////////////////////////////////
// Part 3: Types
////////////////////////////////////////////////////////////////////////

ty
: ty_prim
| ty_closure
| '<' ty_sum maybe_as_trait_ref '>' MOD_SEP ident                                      { /*{o}$$ = mk_node("TyQualifiedPath", 3, $2, $3, $6);*/ }
| SHL ty_sum maybe_as_trait_ref '>' MOD_SEP ident maybe_as_trait_ref '>' MOD_SEP ident { /*{o}$$ = mk_node("TyQualifiedPath", 3, mk_node("TyQualifiedPath", 3, $2, $3, $6), $7, $10);*/ }
| '(' ty_sums ')'                                                                      { /*{o}$$ = mk_node("TyTup", 1, $2);*/ }
| '(' ty_sums ',' ')'                                                                  { /*{o}$$ = mk_node("TyTup", 1, $2);*/ }
| '(' ')'                                                                              { /*{o}$$ = mk_atom("TyNil");*/ }
;

ty_prim
: %prec IDENT path_generic_args_without_colons                           { irep_idt type_name(to_symbol_expr(parser_stack($1)).get_identifier());
                                                                           newstack($$) = exprt("ID_type_carrier", rusttype_to_ctype(type_name)); }
| %prec IDENT MOD_SEP path_generic_args_without_colons                   { /*{o}$$ = mk_node("TyPath", 2, mk_node("global", 1, mk_atom("true")), $2);*/ }
| %prec IDENT SELF MOD_SEP path_generic_args_without_colons              { /*{o}$$ = mk_node("TyPath", 2, mk_node("self", 1, mk_atom("true")), $3);*/ }
| %prec IDENT
  path_generic_args_without_colons '!' maybe_ident delimited_token_trees { /*{o}$$ = mk_node("TyMacro", 3, $1, $3, $4);*/ }
| %prec IDENT MOD_SEP
  path_generic_args_without_colons '!' maybe_ident delimited_token_trees { /*{o}$$ = mk_node("TyMacro", 3, $2, $4, $5);*/ }
| BOX ty                                                                 { /*{o}$$ = mk_node("TyBox", 1, $2);*/ }
| '*' maybe_mut_or_const ty                                              { newstack($$) = exprt("ID_type_carrier", pointer_type(parser_stack($3).type())); }
| '&' ty                                                                 { newstack($$) = exprt("ID_type_carrier", parser_stack($2).type()); }
| '&' MUT ty                                                             { newstack($$) = exprt("ID_type_carrier", parser_stack($3).type()); }
| ANDAND ty                                                              { /*{o}$$ = mk_node("TyRptr", 1, mk_node("TyRptr", 2, mk_atom("MutImmutable"), $2));*/ }
| ANDAND MUT ty                                                          { /*{o}$$ = mk_node("TyRptr", 1, mk_node("TyRptr", 2, mk_atom("MutMutable"), $3));*/ }
| '&' lifetime maybe_mut ty                                              { /*{o}$$ = mk_node("TyRptr", 3, $2, $3, $4);*/ }
| ANDAND lifetime maybe_mut ty                                           { /*{o}$$ = mk_node("TyRptr", 1, mk_node("TyRptr", 3, $2, $3, $4));*/ }
| '[' ty ']'                                                             { /*{o}$$ = mk_node("TyVec", 1, $2);*/ }
| '[' ty ',' DOTDOT expr ']'                                             { /*{o}$$ = mk_node("TyFixedLengthVec", 2, $2, $5);*/ }
| '[' ty ';' expr ']'                                                    { /*{o}$$ = mk_node("TyFixedLengthVec", 2, $2, $4);*/ }
| TYPEOF '(' expr ')'                                                    { /*{o}$$ = mk_node("TyTypeof", 1, $3);*/ }
| UNDERSCORE                                                             { /*{o}$$ = mk_atom("TyInfer");*/ }
| ty_bare_fn
| for_in_type
;

ty_bare_fn
:                         FN ty_fn_decl { /*{o}$$ = $2;*/ }
| UNSAFE                  FN ty_fn_decl { /*{o}$$ = $3;*/ }
|        EXTERN maybe_abi FN ty_fn_decl { /*{o}$$ = $4;*/ }
| UNSAFE EXTERN maybe_abi FN ty_fn_decl { /*{o}$$ = $5;*/ }
;

ty_fn_decl
: generic_params fn_anon_params ret_ty { /*{o}$$ = mk_node("TyFnDecl", 3, $1, $2, $3);*/ }
;

ty_closure
: UNSAFE '|' anon_params '|' maybe_bounds ret_ty { /*{o}$$ = mk_node("TyClosure", 3, $3, $5, $6);*/ }
|        '|' anon_params '|' maybe_bounds ret_ty { /*{o}$$ = mk_node("TyClosure", 3, $2, $4, $5);*/ }
| UNSAFE OROR maybe_bounds ret_ty                { /*{o}$$ = mk_node("TyClosure", 2, $3, $4);*/ }
|        OROR maybe_bounds ret_ty                { /*{o}$$ = mk_node("TyClosure", 2, $2, $3);*/ }
;

for_in_type
: FOR '<' maybe_lifetimes '>' for_in_type_suffix { /*{o}$$ = mk_node("ForInType", 2, $3, $5);*/ }
;

for_in_type_suffix
: ty_bare_fn
| trait_ref
| ty_closure
;

maybe_mut
: MUT              { /*{o}$$ = mk_atom("MutMutable");*/ }
| %prec MUT %empty { /*{o}$$ = mk_atom("MutImmutable");*/ }
;

maybe_mut_or_const
: MUT    { /*{o}$$ = mk_atom("MutMutable");*/ }
| CONST  { /*{o}$$ = mk_atom("MutImmutable");*/ }
| %empty { /*{o}$$ = mk_atom("MutImmutable");*/ }
;

ty_qualified_path_and_generic_values
: ty_qualified_path maybe_bindings
{
  /*{o}$$ = mk_node("GenericValues", 3, mk_none(), mk_node("TySums", 1, mk_node("TySum", 1, $1)), $2);*/
}
| ty_qualified_path ',' ty_sums maybe_bindings
{
  /*{o}$$ = mk_node("GenericValues", 3, mk_none(), mk_node("TySums", 2, $1, $3), $4);*/
}
;

ty_qualified_path
: ty_sum AS trait_ref '>' MOD_SEP ident                     { /*{o}$$ = mk_node("TyQualifiedPath", 3, $1, $3, $6);*/ }
| ty_sum AS trait_ref '>' MOD_SEP ident '+' ty_param_bounds { /*{o}$$ = mk_node("TyQualifiedPath", 3, $1, $3, $6);*/ }
;

maybe_ty_sums
: ty_sums
| ty_sums ','
| %empty { /*{o}$$ = mk_none();*/ }
;

ty_sums
: ty_sum             { /*{o}$$ = mk_node("TySums", 1, $1);*/ }
| ty_sums ',' ty_sum { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

ty_sum
: ty_sum_elt            { /*{o}$$ = mk_node("TySum", 1, $1);*/
                          $$ = $1; }
| ty_sum '+' ty_sum_elt { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

ty_sum_elt
: ty
| lifetime
;

ty_prim_sum
: ty_prim_sum_elt                 { /*{o}$$ = mk_node("TySum", 1, $1);*/ }
| ty_prim_sum '+' ty_prim_sum_elt { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

ty_prim_sum_elt
: ty_prim
| lifetime
;

maybe_ty_param_bounds
: ':' ty_param_bounds { /*{o}$$ = $2;*/ }
| %empty              { /*{o}$$ = mk_none();*/ }
;

ty_param_bounds
: boundseq
| %empty { /*{o}$$ = mk_none();*/ }
;

boundseq
: polybound
| boundseq '+' polybound { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

polybound
: FOR '<' maybe_lifetimes '>' bound { /*{o}$$ = mk_node("PolyBound", 2, $3, $5);*/ }
| bound
| '?' FOR '<' maybe_lifetimes '>' bound { /*{o}$$ = mk_node("PolyBound", 2, $4, $6);*/ }
| '?' bound { /*{o}$$ = $2;*/ }
;

bindings
: binding              { /*{o}$$ = mk_node("Bindings", 1, $1);*/ }
| bindings ',' binding { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

binding
: ident '=' ty { /*{o}mk_node("Binding", 2, $1, $3);*/ }
;

ty_param
: ident maybe_ty_param_bounds maybe_ty_default           { /*{o}$$ = mk_node("TyParam", 3, $1, $2, $3);*/ }
| ident '?' ident maybe_ty_param_bounds maybe_ty_default { /*{o}$$ = mk_node("TyParam", 4, $1, $3, $4, $5);*/ }
;

maybe_bounds
: %prec SHIFTPLUS
  ':' bounds             { /*{o}$$ = $2;*/ }
| %prec SHIFTPLUS %empty { /*{o}$$ = mk_none();*/ }
;

bounds
: bound            { /*{o}$$ = mk_node("bounds", 1, $1);*/ }
| bounds '+' bound { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

bound
: lifetime
| trait_ref
;

maybe_ltbounds
: %prec SHIFTPLUS
  ':' ltbounds       { /*{o}$$ = $2;*/ }
| %empty             { /*{o}$$ = mk_none();*/ }
;

ltbounds
: lifetime              { /*{o}$$ = mk_node("ltbounds", 1, $1);*/ }
| ltbounds '+' lifetime { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

maybe_ty_default
: '=' ty_sum { /*{o}$$ = mk_node("TyDefault", 1, $2);*/ }
| %empty     { /*{o}$$ = mk_none();*/ }
;

maybe_lifetimes
: lifetimes
| lifetimes ','
| %empty { /*{o}$$ = mk_none();*/ }
;

lifetimes
: lifetime_and_bounds               { /*{o}$$ = mk_node("Lifetimes", 1, $1);*/ }
| lifetimes ',' lifetime_and_bounds { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

lifetime_and_bounds
: LIFETIME maybe_ltbounds         { /*{o}$$ = mk_node("lifetime", 2, mk_atom(yyrusttext), $2);*/ }
| STATIC_LIFETIME                 { /*{o}$$ = mk_atom("static_lifetime");*/ }
;

lifetime
: LIFETIME         { /*{o}$$ = mk_node("lifetime", 1, mk_atom(yyrusttext));*/ }
| STATIC_LIFETIME  { /*{o}$$ = mk_atom("static_lifetime");*/ }
;

trait_ref
: %prec IDENT path_generic_args_without_colons
| %prec IDENT MOD_SEP path_generic_args_without_colons { /*{o}$$ = $2;*/ }
;

////////////////////////////////////////////////////////////////////////
// Part 4: Blocks, statements, and expressions
////////////////////////////////////////////////////////////////////////

inner_attrs_and_block
: '{' maybe_inner_attrs maybe_stmts '}'
  {
    /*{o}$$ = mk_node("ExprBlock", 2, $2, $3);*/
    code_blockt a = to_code_block(to_code(parser_stack($3)));
    newstack($$).swap(a);
  }
;

block
: '{' maybe_stmts '}'
  {
    /*{o}$$ = mk_node("ExprBlock", 1, $2);*/
    $$ = $2;
  }
;

maybe_stmts
: stmts
| stmts nonblock_expr { /*{o}$$ = ext_node($1, 1, $2);*/
                        code_blockt a;
                        a.append(to_code_block(to_code(parser_stack($1))));
                        if(parser_stack($2).id() == ID_code)
                          a.add(to_code(parser_stack($2)));
                        else
                          a.add(code_expressiont(parser_stack($2)));
                        newstack($$).swap(a); }
| nonblock_expr       { code_blockt a;
                        if(parser_stack($1).id() == ID_code)
                          a.add(to_code(parser_stack($1)));
                        else
                          a.add(code_expressiont(parser_stack($1)));
                        newstack($$).swap(a); }
| %empty              { /*{o}$$ = mk_none();*/
                        newstack($$) = code_blockt(); }
;

// There are two sub-grammars within a "stmts: exprs" derivation
// depending on whether each stmt-expr is a block-expr form; this is to
// handle the "semicolon rule" for stmt sequencing that permits
// writing
//
//     if foo { bar } 10
//
// as a sequence of two stmts (one if-expr stmt, one lit-10-expr
// stmt). Unfortunately by permitting juxtaposition of exprs in
// sequence like that, the non-block expr grammar has to have a
// second limited sub-grammar that excludes the prefix exprs that
// are ambiguous with binops. That is to say:
//
//     {10} - 1
//
// should parse as (progn (progn 10) (- 1)) not (- (progn 10) 1), that
// is to say, two statements rather than one, at least according to
// the mainline rust parser.
//
// So we wind up with a 3-way split in exprs that occur in stmt lists:
// block, nonblock-prefix, and nonblock-nonprefix.
//
// In non-stmts contexts, expr can relax this trichotomy.

stmts
: stmt           { code_blockt a;
                   a.add(to_code(parser_stack($1)));
                   newstack($$).swap(a); }
| stmts stmt     { code_blockt a = to_code_block(to_code(parser_stack($1)));
                   a.add(to_code(parser_stack($2)));
                   newstack($$).swap(a); }
;

stmt
: maybe_outer_attrs let
{
  /*{o}$$ = $2;*/
  /*TODO: Handle maybe_outer_attrs(#[...]s)*/
  // pass along the let statement
  $$ = $2;
}
|                 stmt_item
|             PUB stmt_item { /*{o}$$ = $2;*/ }
| outer_attrs     stmt_item { /*{o}$$ = $2;*/ }
| outer_attrs PUB stmt_item { /*{o}$$ = $3;*/ }
| full_block_expr
| maybe_outer_attrs block   { /*{o}$$ = $2;*/
                              $$ = $2; }
|         nonblock_expr ';' { $$ = $1; }

| outer_attrs nonblock_expr ';' { /*{o}$$ = $2;*/ }
| ';'                   { /*{o}$$ = mk_none();*/ }
;

maybe_exprs
: exprs
| exprs ','
| %empty { /*{o}$$ = mk_none();*/
           newstack($$) = exprt(); }
;

maybe_expr
: expr
| %empty { /*{o}$$ = mk_none();*/ 
           newstack($$) = exprt(); }
;

exprs
: expr                   { multi_ary_exprt a("ID_onlyexpr", exprt::operandst(), typet());
                           a.add_to_operands(parser_stack($1));
                           newstack($$).swap(a); }
| exprs ',' expr         { parser_stack($1).add_to_operands(parser_stack($3));
                           $$ = $1; }
;

path_expr
: path_generic_args_with_colons
| MOD_SEP path_generic_args_with_colons      { /*{o}$$ = $2;*/ }
| SELF MOD_SEP path_generic_args_with_colons { /*{o}$$ = mk_node("SelfPath", 1, $3);*/ }
;

// A path with a lifetime and type parameters with double colons before
// the type parameters; e.g. `foo::bar::<'a>::Baz::<T>`
//
// These show up in expr context, in order to disambiguate from "less-than"
// expressions.
path_generic_args_with_colons
: ident                                              { /*{o}$$ = mk_node("components", 1, $1);*/
                                                       $$ = $1; }
| SUPER                                              { /*{o}$$ = mk_atom("Super");*/ }
| path_generic_args_with_colons MOD_SEP ident        { /*{o}$$ = ext_node($1, 1, $3);*/ }
| path_generic_args_with_colons MOD_SEP SUPER        { /*{o}$$ = ext_node($1, 1, mk_atom("Super"));*/ }
| path_generic_args_with_colons MOD_SEP generic_args { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

// the braces-delimited macro is a block_expr so it doesn't appear here
macro_expr
: path_expr '!' maybe_ident parens_delimited_token_trees
                {
                  // special case for asserts
                  if(to_symbol_expr(parser_stack($1)).get_identifier() == "assert")
                  {
                    // condition is always first parameter
                    exprt condition = parse_token_tree(to_multi_ary_expr(parser_stack($4)));
                    newstack($$) = create_fatal_assertion(condition, source_locationt());
                  }
                  else if(to_symbol_expr(parser_stack($1)).get_identifier() == "panic")
                  {
                    newstack($$) = create_fatal_assertion(false_exprt(), source_locationt());
                  }
                  // TODO: Normal macro
                  else
                  {
                  }
                }
| path_expr '!' maybe_ident brackets_delimited_token_trees { /*{o}$$ = mk_node("MacroExpr", 3, $1, $3, $4);*/ }
;

nonblock_expr
: lit                                              { $$ = $1; }
| %prec IDENT path_expr                            { $$ = $1; }
| SELF                                             { /*{o}$$ = mk_node("ExprPath", 1, mk_node("ident", 1, mk_atom("self")));*/ }
| macro_expr                                       { $$ = $1; }
| path_expr '{' struct_expr_fields '}'             { /*{o}$$ = mk_node("ExprStruct", 2, $1, $3);*/ }
| nonblock_expr '?'                                { /*{o}$$ = mk_node("ExprTry", 1, $1);*/ }
| nonblock_expr '.' path_generic_args_with_colons  { /*{o}$$ = mk_node("ExprField", 2, $1, $3);*/ }
| nonblock_expr '.' LIT_INTEGER                    { /*{o}$$ = mk_node("ExprTupleIndex", 1, $1);*/ }
| nonblock_expr '[' maybe_expr ']'                 { /*{o}$$ = mk_node("ExprIndex", 2, $1, $3);*/ }
| nonblock_expr '(' maybe_exprs ')'                { // assumes parser_stack($1) is a symbol
                                                     symbol_exprt a = to_symbol_expr(parser_stack($1));
                                                     code_typet::parameterst params;
                                                     Forall_operands(it, parser_stack($3))
                                                     {
                                                       params.push_back(code_typet::parametert((*it).type()));
                                                       params.back().add_to_operands((*it));
                                                     }
                                                     a.type() = code_typet(params, typet());
                                                     newstack($$) = code_expressiont(
                                                                       side_effect_expr_function_callt(a,
                                                                                                       parser_stack($3).operands(),
                                                                                                       typet(),
                                                                                                       source_locationt())); }
| '[' vec_expr ']'                                { /*{o}$$ = mk_node("ExprVec", 1, $2);*/ }
| '(' maybe_exprs ')'                             { multi_ary_exprt& a = to_multi_ary_expr(parser_stack($2));
                                                    code_blockt b;
                                                    for(exprt::operandst::iterator it=(a).operands().begin(); it!=(a).operands().end(); ++it)
                                                    {
                                                      if((*it).id() == ID_code)
                                                        b.add_to_operands(to_code(*it));
                                                      else
                                                      {
                                                        code_expressiont c(*it);
                                                        c.type() = (*it).type();
                                                        b.add_to_operands(c);
                                                      }
                                                    }
                                                    //TODO: right now only one operand  has been important, I don't know what multiple would be used for yet
                                                    if(b.operands().size() == 1)
                                                      newstack($$).swap(b.op0());
                                                    else
                                                      newstack($$).swap(b); }
| CONTINUE                                        { /*{o}$$ = mk_node("ExprAgain", 0);*/ }
| CONTINUE lifetime                               { /*{o}$$ = mk_node("ExprAgain", 1, $2);*/ }
| RETURN                                          { newstack($$) = code_returnt(); }
| RETURN expr                                     { newstack($$) = code_returnt(parser_stack($2)); }
| BREAK                                           { newstack($$) = code_breakt(); }
| BREAK lifetime                                  { /*{o}$$ = mk_node("ExprBreak", 1, $2);*/ }
| YIELD                                           { /*{o}$$ = mk_node("ExprYield", 0);*/ }
| YIELD expr                                      { /*{o}$$ = mk_node("ExprYield", 1, $2);*/ }
| nonblock_expr '=' expr                          { newstack($$) = code_assignt(parser_stack($1), parser_stack($3)); }
| nonblock_expr SHLEQ expr                        { shl_exprt a(parser_stack($1), parser_stack($3));
                                                    newstack($$) = code_assignt(parser_stack($1), a); }
| nonblock_expr SHREQ expr                        { lshr_exprt a(parser_stack($1), parser_stack($3));
                                                    newstack($$) = code_assignt(parser_stack($1), a); }
| nonblock_expr MINUSEQ expr                      { minus_exprt a(parser_stack($1), parser_stack($3));
                                                    newstack($$) = code_assignt(parser_stack($1), a); }
| nonblock_expr ANDEQ expr                        { bitand_exprt a(parser_stack($1), parser_stack($3));
                                                    newstack($$) = code_assignt(parser_stack($1), a); }
| nonblock_expr OREQ expr                         { bitor_exprt a(parser_stack($1), parser_stack($3));
                                                    newstack($$) = code_assignt(parser_stack($1), a); }
| nonblock_expr PLUSEQ expr                       { plus_exprt a(parser_stack($1), parser_stack($3));
                                                    newstack($$) = code_assignt(parser_stack($1), a); }
| nonblock_expr STAREQ expr                       { mult_exprt a(parser_stack($1), parser_stack($3));
                                                    newstack($$) = code_assignt(parser_stack($1), a); }
| nonblock_expr SLASHEQ expr                      { div_exprt a(parser_stack($1), parser_stack($3));
                                                    newstack($$) = code_assignt(parser_stack($1), a); }
| nonblock_expr CARETEQ expr                      { bitxor_exprt a(parser_stack($1), parser_stack($3));
                                                    newstack($$) = code_assignt(parser_stack($1), a); }
| nonblock_expr PERCENTEQ expr                    { mod_exprt a(parser_stack($1), parser_stack($3));
                                                    newstack($$) = code_assignt(parser_stack($1), a); }
| nonblock_expr OROR expr                         { newstack($$) = or_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr ANDAND expr                       { newstack($$) = and_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr EQEQ expr                         { newstack($$) = equal_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr NE expr                           { newstack($$) = notequal_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr '<' expr                          { newstack($$) = binary_relation_exprt(parser_stack($1), ID_lt, parser_stack($3)); }
| nonblock_expr '>' expr                          { newstack($$) = binary_relation_exprt(parser_stack($1), ID_gt, parser_stack($3)); }
| nonblock_expr LE expr                           { newstack($$) = binary_relation_exprt(parser_stack($1), ID_le, parser_stack($3)); }
| nonblock_expr GE expr                           { newstack($$) = binary_relation_exprt(parser_stack($1), ID_ge, parser_stack($3)); }
| nonblock_expr '|' expr                          { newstack($$) = bitor_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr '^' expr                          { newstack($$) = bitxor_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr '&' expr                          { newstack($$) = bitand_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr SHL expr                          { newstack($$) = shl_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr SHR expr                          { newstack($$) = lshr_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr '+' expr                          { newstack($$) = plus_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr '-' expr                          { newstack($$) = minus_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr '*' expr                          { newstack($$) = mult_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr '/' expr                          { newstack($$) = div_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr '%' expr                          { newstack($$) = mod_exprt(parser_stack($1), parser_stack($3)); }
| nonblock_expr DOTDOT                            { /*{o}$$ = mk_node("ExprRange", 2, $1, mk_none());*/ }
| nonblock_expr DOTDOT expr                       { /*{o}$$ = mk_node("ExprRange", 2, $1, $3);*/ }
|               DOTDOT expr                       { /*{o}$$ = mk_node("ExprRange", 2, mk_none(), $2);*/ }
|               DOTDOT                            { /*{o}$$ = mk_node("ExprRange", 2, mk_none(), mk_none());*/ }
| nonblock_expr AS ty                             { /*{o}$$ = mk_node("ExprCast", 2, $1, $3);*/ }
| nonblock_expr ':' ty                            { /*{o}$$ = mk_node("ExprTypeAscr", 2, $1, $3);*/ }
| BOX expr                                        { /*{o}$$ = mk_node("ExprBox", 1, $2);*/ }
| expr_qualified_path
| nonblock_prefix_expr
;

expr
: lit                                        { $$ = $1; }
| %prec IDENT path_expr                      { /*{o}$$ = mk_node("ExprPath", 1, $1);*/ }
| SELF                                       { /*{o}$$ = mk_node("ExprPath", 1, mk_node("ident", 1, mk_atom("self")));*/ }
| macro_expr                                 { /*{o}$$ = mk_node("ExprMac", 1, $1);*/ }
| path_expr '{' struct_expr_fields '}'       { /*{o}$$ = mk_node("ExprStruct", 2, $1, $3);*/ }
| expr '?'                                   { /*{o}$$ = mk_node("ExprTry", 1, $1);*/ }
| expr '.' path_generic_args_with_colons     { /*{o}$$ = mk_node("ExprField", 2, $1, $3);*/ }
| expr '.' LIT_INTEGER                       { /*{o}$$ = mk_node("ExprTupleIndex", 1, $1);*/ }
| expr '[' maybe_expr ']'                    { /*{o}$$ = mk_node("ExprIndex", 2, $1, $3);*/ }
| expr '(' maybe_exprs ')'                   { // assumes parser_stack($1) is a symbol
                                               symbol_exprt a = to_symbol_expr(parser_stack($1));
                                               code_typet::parameterst params;
                                               Forall_operands(it, parser_stack($3))
                                               {
                                                 params.push_back(code_typet::parametert((*it).type()));
                                                 params.back().add_to_operands((*it));
                                               }
                                               a.type() = code_typet(params, typet());
                                               newstack($$) = code_expressiont(
                                                                 side_effect_expr_function_callt(a,
                                                                                                 parser_stack($3).operands(),
                                                                                                 typet(),
                                                                                                 source_locationt())); }
| '(' maybe_exprs ')'                        { //TODO: assumes expressions in parentheses will reduce to a single expression. If not the case, fix this
                                               newstack($$).swap(parser_stack($2).op0()); }
| '[' vec_expr ']'                           { /*{o}$$ = mk_node("ExprVec", 1, $2);*/ }
| CONTINUE                                   { /*{o}$$ = mk_node("ExprAgain", 0);*/ }
| CONTINUE ident                             { /*{o}$$ = mk_node("ExprAgain", 1, $2);*/ }
| RETURN                                     { /*{o}$$ = mk_node("ExprRet", 0);*/ }
| RETURN expr                                { /*{o}$$ = mk_node("ExprRet", 1, $2);*/ }
| BREAK                                      { /*{o}$$ = mk_node("ExprBreak", 0);*/ }
| BREAK ident                                { /*{o}$$ = mk_node("ExprBreak", 1, $2);*/ }
| YIELD                                      { /*{o}$$ = mk_node("ExprYield", 0);*/ }
| YIELD expr                                 { /*{o}$$ = mk_node("ExprYield", 1, $2);*/ }
| expr '=' expr                              { newstack($$) = code_assignt(parser_stack($1), parser_stack($3)); }
| expr SHLEQ expr                            { /*{o}$$ = mk_node("ExprAssignShl", 2, $1, $3);*/
                                               shl_exprt a(parser_stack($1), parser_stack($3));
                                               newstack($$) = code_assignt(parser_stack($1), a); }
| expr SHREQ expr                            { /*{o}$$ = mk_node("ExprAssignShr", 2, $1, $3);*/
                                               lshr_exprt a(parser_stack($1), parser_stack($3));
                                               newstack($$) = code_assignt(parser_stack($1), a); }
| expr MINUSEQ expr                          { /*{o}$$ = mk_node("ExprAssignSub", 2, $1, $3);*/
                                               minus_exprt a(parser_stack($1), parser_stack($3));
                                               newstack($$) = code_assignt(parser_stack($1), a); }
| expr ANDEQ expr                            { /*{o}$$ = mk_node("ExprAssignBitAnd", 2, $1, $3);*/ 
                                               bitand_exprt a(parser_stack($1), parser_stack($3));
                                               newstack($$) = code_assignt(parser_stack($1), a); }
| expr OREQ expr                             { /*{o}$$ = mk_node("ExprAssignBitOr", 2, $1, $3);*/ 
                                               bitor_exprt a(parser_stack($1), parser_stack($3));
                                               newstack($$) = code_assignt(parser_stack($1), a); }
| expr PLUSEQ expr                           { /*{o}$$ = mk_node("ExprAssignAdd", 2, $1, $3);*/
                                               plus_exprt a(parser_stack($1), parser_stack($3));
                                               newstack($$) = code_assignt(parser_stack($1), a); }
| expr STAREQ expr                           { /*{o}$$ = mk_node("ExprAssignMul", 2, $1, $3);*/
                                               mult_exprt a(parser_stack($1), parser_stack($3));
                                               newstack($$) = code_assignt(parser_stack($1), a); }
| expr SLASHEQ expr                          { /*{o}$$ = mk_node("ExprAssignDiv", 2, $1, $3);*/
                                               div_exprt a(parser_stack($1), parser_stack($3));
                                               newstack($$) = code_assignt(parser_stack($1), a); }
| expr CARETEQ expr                          { /*{o}$$ = mk_node("ExprAssignBitXor", 2, $1, $3);*/ 
                                               bitxor_exprt a(parser_stack($1), parser_stack($3));
                                               newstack($$) = code_assignt(parser_stack($1), a); }
| expr PERCENTEQ expr                        { /*{o}$$ = mk_node("ExprAssignRem", 2, $1, $3);*/ 
                                               mod_exprt a(parser_stack($1), parser_stack($3));
                                               newstack($$) = code_assignt(parser_stack($1), a); }
| expr OROR expr                             { newstack($$) = or_exprt(parser_stack($1), parser_stack($3)); }
| expr ANDAND expr                           { newstack($$) = and_exprt(parser_stack($1), parser_stack($3)); }
| expr EQEQ expr                             { newstack($$) = equal_exprt(parser_stack($1), parser_stack($3)); }
| expr NE expr                               { newstack($$) = notequal_exprt(parser_stack($1), parser_stack($3)); }
| expr '<' expr                              { newstack($$) = binary_relation_exprt(parser_stack($1), ID_lt, parser_stack($3)); }
| expr '>' expr                              { newstack($$) = binary_relation_exprt(parser_stack($1), ID_gt, parser_stack($3)); }
| expr LE expr                               { newstack($$) = binary_relation_exprt(parser_stack($1), ID_le, parser_stack($3)); }
| expr GE expr                               { newstack($$) = binary_relation_exprt(parser_stack($1), ID_ge, parser_stack($3)); }
| expr '|' expr                              { newstack($$) = bitor_exprt(parser_stack($1), parser_stack($3)); }
| expr '^' expr                              { newstack($$) = bitxor_exprt(parser_stack($1), parser_stack($3)); }
| expr '&' expr                              { newstack($$) = bitand_exprt(parser_stack($1), parser_stack($3)); }
| expr SHL expr                              { newstack($$) = shl_exprt(parser_stack($1), parser_stack($3)); }
| expr SHR expr                              { newstack($$) = lshr_exprt(parser_stack($1), parser_stack($3)); }
| expr '+' expr                              { newstack($$) = plus_exprt(parser_stack($1), parser_stack($3)); }
| expr '-' expr                              { newstack($$) = minus_exprt(parser_stack($1), parser_stack($3)); }
| expr '*' expr                              { newstack($$) = mult_exprt(parser_stack($1), parser_stack($3)); }
| expr '/' expr                              { newstack($$) = div_exprt(parser_stack($1), parser_stack($3)); }
| expr '%' expr                              { newstack($$) = mod_exprt(parser_stack($1), parser_stack($3)); }
| expr DOTDOT                                { /*{o}$$ = mk_node("ExprRange", 2, $1, mk_none());*/ }
| expr DOTDOT expr                           { /*{o}$$ = mk_node("ExprRange", 2, $1, $3);*/ }
|      DOTDOT expr                           { /*{o}$$ = mk_node("ExprRange", 2, mk_none(), $2);*/ }
|      DOTDOT                                { /*{o}$$ = mk_node("ExprRange", 2, mk_none(), mk_none());*/ }
| expr AS ty                                 { /*{o}$$ = mk_node("ExprCast", 2, $1, $3);*/ }
| expr ':' ty                                { /*{o}$$ = mk_node("ExprTypeAscr", 2, $1, $3);*/ }
| BOX expr                                   { /*{o}$$ = mk_node("ExprBox", 1, $2);*/ }
| expr_qualified_path
| block_expr
| block
| nonblock_prefix_expr
;

expr_nostruct
: lit                                                 { /*{o}$$ = mk_node("ExprLit", 1, $1);*/
                                                        $$ = $1; }
| %prec IDENT
  path_expr                                           { /*{o}$$ = mk_node("ExprPath", 1, $1);*/ }
| SELF                                                { /*{o}$$ = mk_node("ExprPath", 1, mk_node("ident", 1, mk_atom("self")));*/ }
| macro_expr                                          { /*{o}$$ = mk_node("ExprMac", 1, $1);*/ }
| expr_nostruct '?'                                   { /*{o}$$ = mk_node("ExprTry", 1, $1);*/ }
| expr_nostruct '.' path_generic_args_with_colons     { /*{o}$$ = mk_node("ExprField", 2, $1, $3);*/ }
| expr_nostruct '.' LIT_INTEGER                       { /*{o}$$ = mk_node("ExprTupleIndex", 1, $1);*/ }
| expr_nostruct '[' maybe_expr ']'                    { /*{o}$$ = mk_node("ExprIndex", 2, $1, $3);*/ }
| expr_nostruct '(' maybe_exprs ')'                   { /*{o}$$ = mk_node("ExprCall", 2, $1, $3);*/ }
| '[' vec_expr ']'                                    { /*{o}$$ = mk_node("ExprVec", 1, $2);*/ }
| '(' maybe_exprs ')'                                 { /*{o}$$ = mk_node("ExprParen", 1, $2);*/
                                                        //TODO: assumes expressions in parentheses will reduce to a single expression. If not the case, fix this
                                                        newstack($$).swap(parser_stack($2).op0()); }
| CONTINUE                                            { /*{o}$$ = mk_node("ExprAgain", 0);*/ }
| CONTINUE ident                                      { /*{o}$$ = mk_node("ExprAgain", 1, $2);*/ }
| RETURN                                              { /*{o}$$ = mk_node("ExprRet", 0);*/ }
| RETURN expr                                         { /*{o}$$ = mk_node("ExprRet", 1, $2);*/ }
| BREAK                                               { /*{o}$$ = mk_node("ExprBreak", 0);*/ }
| BREAK ident                                         { /*{o}$$ = mk_node("ExprBreak", 1, $2);*/ }
| YIELD                                               { /*{o}$$ = mk_node("ExprYield", 0);*/ }
| YIELD expr                                          { /*{o}$$ = mk_node("ExprYield", 1, $2);*/ }
| expr_nostruct '=' expr_nostruct                     { /*{o}$$ = mk_node("ExprAssign", 2, $1, $3);*/ }
| expr_nostruct SHLEQ expr_nostruct                   { /*{o}$$ = mk_node("ExprAssignShl", 2, $1, $3);*/
                                                        shl_exprt a(parser_stack($1), parser_stack($3));
                                                        newstack($$) = code_assignt(parser_stack($1), a); }
| expr_nostruct SHREQ expr_nostruct                   { /*{o}$$ = mk_node("ExprAssignShr", 2, $1, $3);*/
                                                        lshr_exprt a(parser_stack($1), parser_stack($3));
                                                        newstack($$) = code_assignt(parser_stack($1), a); }
| expr_nostruct MINUSEQ expr_nostruct                 { /*{o}$$ = mk_node("ExprAssignSub", 2, $1, $3);*/
                                                        minus_exprt a(parser_stack($1), parser_stack($3));
                                                        newstack($$) = code_assignt(parser_stack($1), a); }
| expr_nostruct ANDEQ expr_nostruct                   { /*{o}$$ = mk_node("ExprAssignBitAnd", 2, $1, $3);*/ 
                                                        bitand_exprt a(parser_stack($1), parser_stack($3));
                                                        newstack($$) = code_assignt(parser_stack($1), a); }
| expr_nostruct OREQ expr_nostruct                    { /*{o}$$ = mk_node("ExprAssignBitOr", 2, $1, $3);*/ 
                                                        bitor_exprt a(parser_stack($1), parser_stack($3));
                                                        newstack($$) = code_assignt(parser_stack($1), a); }
| expr_nostruct PLUSEQ expr_nostruct                  { /*{o}$$ = mk_node("ExprAssignAdd", 2, $1, $3);*/
                                                        plus_exprt a(parser_stack($1), parser_stack($3));
                                                        newstack($$) = code_assignt(parser_stack($1), a); }
| expr_nostruct STAREQ expr_nostruct                  { /*{o}$$ = mk_node("ExprAssignMul", 2, $1, $3);*/
                                                        mult_exprt a(parser_stack($1), parser_stack($3));
                                                        newstack($$) = code_assignt(parser_stack($1), a); }
| expr_nostruct SLASHEQ expr_nostruct                 { /*{o}$$ = mk_node("ExprAssignDiv", 2, $1, $3);*/
                                                        div_exprt a(parser_stack($1), parser_stack($3));
                                                        newstack($$) = code_assignt(parser_stack($1), a); }
| expr_nostruct CARETEQ expr_nostruct                 { /*{o}$$ = mk_node("ExprAssignBitXor", 2, $1, $3);*/ 
                                                        bitxor_exprt a(parser_stack($1), parser_stack($3));
                                                        newstack($$) = code_assignt(parser_stack($1), a); }
| expr_nostruct PERCENTEQ expr_nostruct               { /*{o}$$ = mk_node("ExprAssignRem", 2, $1, $3);*/ 
                                                        mod_exprt a(parser_stack($1), parser_stack($3));
                                                        newstack($$) = code_assignt(parser_stack($1), a); }
| expr_nostruct OROR expr_nostruct                    { newstack($$) = or_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct ANDAND expr_nostruct                  { newstack($$) = and_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct EQEQ expr_nostruct                    { newstack($$) = equal_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct NE expr_nostruct                      { newstack($$) = notequal_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct '<' expr_nostruct                     { newstack($$) = binary_relation_exprt(parser_stack($1), ID_lt, parser_stack($3)); }
| expr_nostruct '>' expr_nostruct                     { newstack($$) = binary_relation_exprt(parser_stack($1), ID_gt, parser_stack($3)); }
| expr_nostruct LE expr_nostruct                      { newstack($$) = binary_relation_exprt(parser_stack($1), ID_le, parser_stack($3)); }
| expr_nostruct GE expr_nostruct                      { newstack($$) = binary_relation_exprt(parser_stack($1), ID_ge, parser_stack($3)); }
| expr_nostruct '|' expr_nostruct                     { newstack($$) = bitor_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct '^' expr_nostruct                     { newstack($$) = bitxor_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct '&' expr_nostruct                     { newstack($$) = bitand_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct SHL expr_nostruct                     { newstack($$) = shl_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct SHR expr_nostruct                     { newstack($$) = lshr_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct '+' expr_nostruct                     { newstack($$) = plus_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct '-' expr_nostruct                     { newstack($$) = minus_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct '*' expr_nostruct                     { newstack($$) = mult_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct '/' expr_nostruct                     { newstack($$) = div_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct '%' expr_nostruct                     { newstack($$) = mod_exprt(parser_stack($1), parser_stack($3)); }
| expr_nostruct DOTDOT               %prec RANGE      { /*{o}$$ = mk_node("ExprRange", 2, $1, mk_none());*/ }
| expr_nostruct DOTDOT expr_nostruct                  { /*{o}$$ = mk_node("ExprRange", 2, $1, $3);*/ }
|               DOTDOT expr_nostruct                  { /*{o}$$ = mk_node("ExprRange", 2, mk_none(), $2);*/ }
|               DOTDOT                                { /*{o}$$ = mk_node("ExprRange", 2, mk_none(), mk_none());*/ }
| expr_nostruct AS ty                                 { /*{o}$$ = mk_node("ExprCast", 2, $1, $3);*/ }
| expr_nostruct ':' ty                                { /*{o}$$ = mk_node("ExprTypeAscr", 2, $1, $3);*/ }
| BOX expr                                            { /*{o}$$ = mk_node("ExprBox", 1, $2);*/ }
| expr_qualified_path
| block_expr
| block
| nonblock_prefix_expr_nostruct
;

nonblock_prefix_expr_nostruct
: '-' expr_nostruct                         { newstack($$) = unary_minus_exprt(parser_stack($2), parser_stack($2).type()); }
| '!' expr_nostruct                         { newstack($$) = bitnot_exprt(parser_stack($2)); }
| '*' expr_nostruct                         { newstack($$) = dereference_exprt(parser_stack($2), parser_stack($2).type()); }
| '&' maybe_mut expr_nostruct               { //TODO: handle maybe_mut if necessary. It might not be: the actual Rust compiler should stop altering of non-mut things without CBMC
                                              pointer_typet p_type = pointer_type(parser_stack($3).type());
                                              newstack($$) = address_of_exprt(parser_stack($3), p_type); }
| ANDAND maybe_mut expr_nostruct            { /*{o}$$ = mk_node("ExprAddrOf", 1, mk_node("ExprAddrOf", 2, $2, $3));*/ }
| lambda_expr_nostruct
| MOVE lambda_expr_nostruct                 { /*{o}$$ = $2;*/ }
;

nonblock_prefix_expr
: '-' expr                         { newstack($$) = unary_minus_exprt(parser_stack($2), parser_stack($2).type()); }
| '!' expr                         { newstack($$) = bitnot_exprt(parser_stack($2)); }
| '*' expr                         { newstack($$) = dereference_exprt(parser_stack($2), parser_stack($2).type()); }
| '&' maybe_mut expr               { //TODO: handle maybe_mut if necessary. It might not be: the actual Rust compiler should stop altering of non-mut things without CBMC
                                     pointer_typet p_type = pointer_type(parser_stack($3).type());
                                     newstack($$) = address_of_exprt(parser_stack($3), p_type); }
| ANDAND maybe_mut expr            { /*{o}$$ = mk_node("ExprAddrOf", 1, mk_node("ExprAddrOf", 2, $2, $3));*/ }
| lambda_expr
| MOVE lambda_expr                 { /*{o}$$ = $2;*/ }
;

expr_qualified_path
: '<' ty_sum maybe_as_trait_ref '>' MOD_SEP ident maybe_qpath_params
{
  /*{o}$$ = mk_node("ExprQualifiedPath", 4, $2, $3, $6, $7);*/
}
| SHL ty_sum maybe_as_trait_ref '>' MOD_SEP ident maybe_as_trait_ref '>' MOD_SEP ident
{
  /*{o}$$ = mk_node("ExprQualifiedPath", 3, mk_node("ExprQualifiedPath", 3, $2, $3, $6), $7, $10);*/
}
| SHL ty_sum maybe_as_trait_ref '>' MOD_SEP ident generic_args maybe_as_trait_ref '>' MOD_SEP ident
{
  /*{o}$$ = mk_node("ExprQualifiedPath", 3, mk_node("ExprQualifiedPath", 4, $2, $3, $6, $7), $8, $11);*/
}
| SHL ty_sum maybe_as_trait_ref '>' MOD_SEP ident maybe_as_trait_ref '>' MOD_SEP ident generic_args
{
  /*{o}$$ = mk_node("ExprQualifiedPath", 4, mk_node("ExprQualifiedPath", 3, $2, $3, $6), $7, $10, $11);*/
}
| SHL ty_sum maybe_as_trait_ref '>' MOD_SEP ident generic_args maybe_as_trait_ref '>' MOD_SEP ident generic_args
{
  /*{o}$$ = mk_node("ExprQualifiedPath", 4, mk_node("ExprQualifiedPath", 4, $2, $3, $6, $7), $8, $11, $12);*/
}

maybe_qpath_params
: MOD_SEP generic_args { /*{o}$$ = $2;*/ }
| %empty               { /*{o}$$ = mk_none();*/ }
;

maybe_as_trait_ref
: AS trait_ref { /*{o}$$ = $2;*/ }
| %empty       { /*{o}$$ = mk_none();*/ }
;

lambda_expr
: %prec LAMBDA
  OROR ret_ty expr                                    { /*{o}$$ = mk_node("ExprFnBlock", 3, mk_none(), $2, $3);*/ }
| %prec LAMBDA
  '|' '|' ret_ty expr                                 { /*{o}$$ = mk_node("ExprFnBlock", 3, mk_none(), $3, $4);*/ }
| %prec LAMBDA
  '|' inferrable_params '|' ret_ty expr               { /*{o}$$ = mk_node("ExprFnBlock", 3, $2, $4, $5);*/ }
| %prec LAMBDA
  '|' inferrable_params OROR lambda_expr_no_first_bar { /*{o}$$ = mk_node("ExprFnBlock", 3, $2, mk_none(), $4);*/ }
;

lambda_expr_no_first_bar
: %prec LAMBDA
  '|' ret_ty expr                                 { /*{o}$$ = mk_node("ExprFnBlock", 3, mk_none(), $2, $3);*/ }
| %prec LAMBDA
  inferrable_params '|' ret_ty expr               { /*{o}$$ = mk_node("ExprFnBlock", 3, $1, $3, $4);*/ }
| %prec LAMBDA
  inferrable_params OROR lambda_expr_no_first_bar { /*{o}$$ = mk_node("ExprFnBlock", 3, $1, mk_none(), $3);*/ }
;

lambda_expr_nostruct
: %prec LAMBDA
  OROR expr_nostruct                                           { /*{o}$$ = mk_node("ExprFnBlock", 2, mk_none(), $2);*/ }
| %prec LAMBDA
  '|' '|' ret_ty expr_nostruct                                 { /*{o}$$ = mk_node("ExprFnBlock", 3, mk_none(), $3, $4);*/ }
| %prec LAMBDA
  '|' inferrable_params '|' expr_nostruct                      { /*{o}$$ = mk_node("ExprFnBlock", 2, $2, $4);*/ }
| %prec LAMBDA
  '|' inferrable_params OROR lambda_expr_nostruct_no_first_bar { /*{o}$$ = mk_node("ExprFnBlock", 3, $2, mk_none(), $4);*/ }
;

lambda_expr_nostruct_no_first_bar
: %prec LAMBDA
  '|' ret_ty expr_nostruct                                 { /*{o}$$ = mk_node("ExprFnBlock", 3, mk_none(), $2, $3);*/ }
| %prec LAMBDA
  inferrable_params '|' ret_ty expr_nostruct               { /*{o}$$ = mk_node("ExprFnBlock", 3, $1, $3, $4);*/ }
| %prec LAMBDA
  inferrable_params OROR lambda_expr_nostruct_no_first_bar { /*{o}$$ = mk_node("ExprFnBlock", 3, $1, mk_none(), $3);*/ }
;

vec_expr
: maybe_exprs
| exprs ';' expr { /*{o}$$ = mk_node("VecRepeat", 2, $1, $3);*/ }
;

struct_expr_fields
: field_inits
| field_inits ','
| maybe_field_inits default_field_init { /*{o}$$ = ext_node($1, 1, $2);*/ }
| %empty                               { /*{o}$$ = mk_none();*/ }
;

maybe_field_inits
: field_inits
| field_inits ','
| %empty { /*{o}$$ = mk_none();*/ }
;

field_inits
: field_init                 { /*{o}$$ = mk_node("FieldInits", 1, $1);*/ }
| field_inits ',' field_init { /*{o}$$ = ext_node($1, 1, $3);*/ }
;

field_init
: ident                { /*{o}$$ = mk_node("FieldInit", 1, $1);*/ }
| ident ':' expr       { /*{o}$$ = mk_node("FieldInit", 2, $1, $3);*/ }
| LIT_INTEGER ':' expr { /*{o}$$ = mk_node("FieldInit", 2, mk_atom(yyrusttext), $3);*/ }
;

default_field_init
: DOTDOT expr   { /*{o}$$ = mk_node("DefaultFieldInit", 1, $2);*/ }
;

block_expr
: expr_match
| expr_if
| expr_if_let
| expr_while
| expr_while_let
| expr_loop
| expr_for
| UNSAFE block                                           { //TODO_unsafe: can unsafe be ignored? maybe.
                                                           $$ = $2; }
| path_expr '!' maybe_ident braces_delimited_token_trees { /*{o}$$ = mk_node("Macro", 3, $1, $3, $4);*/ }
;

full_block_expr
: block_expr
| block_expr_dot
;

block_expr_dot
: block_expr     '.' path_generic_args_with_colons %prec IDENT         { /*{o}$$ = mk_node("ExprField", 2, $1, $3);*/ }
| block_expr_dot '.' path_generic_args_with_colons %prec IDENT         { /*{o}$$ = mk_node("ExprField", 2, $1, $3);*/ }
| block_expr     '.' path_generic_args_with_colons '[' maybe_expr ']'  { /*{o}$$ = mk_node("ExprIndex", 3, $1, $3, $5);*/ }
| block_expr_dot '.' path_generic_args_with_colons '[' maybe_expr ']'  { /*{o}$$ = mk_node("ExprIndex", 3, $1, $3, $5);*/ }
| block_expr     '.' path_generic_args_with_colons '(' maybe_exprs ')' { /*{o}$$ = mk_node("ExprCall", 3, $1, $3, $5);*/ }
| block_expr_dot '.' path_generic_args_with_colons '(' maybe_exprs ')' { /*{o}$$ = mk_node("ExprCall", 3, $1, $3, $5);*/ }
| block_expr     '.' LIT_INTEGER                                       { /*{o}$$ = mk_node("ExprTupleIndex", 1, $1);*/ }
| block_expr_dot '.' LIT_INTEGER                                       { /*{o}$$ = mk_node("ExprTupleIndex", 1, $1);*/ }
;

expr_match
: MATCH expr_nostruct '{' '}'                                     { /*{o}$$ = mk_node("ExprMatch", 1, $2);*/ }
| MATCH expr_nostruct '{' match_clauses                       '}' { /*{o}$$ = mk_node("ExprMatch", 2, $2, $4);*/ }
| MATCH expr_nostruct '{' match_clauses nonblock_match_clause '}' { /*{o}$$ = mk_node("ExprMatch", 2, $2, ext_node($4, 1, $5));*/ }
| MATCH expr_nostruct '{'               nonblock_match_clause '}' { /*{o}$$ = mk_node("ExprMatch", 2, $2, mk_node("Arms", 1, $4));*/ }
;

match_clauses
: match_clause               { /*{o}$$ = mk_node("Arms", 1, $1);*/ }
| match_clauses match_clause { /*{o}$$ = ext_node($1, 1, $2);*/ }
;

match_clause
: nonblock_match_clause ','
| block_match_clause
| block_match_clause ','
;

nonblock_match_clause
: maybe_outer_attrs pats_or maybe_guard FAT_ARROW nonblock_expr  { /*{o}$$ = mk_node("ArmNonblock", 4, $1, $2, $3, $5);*/ }
| maybe_outer_attrs pats_or maybe_guard FAT_ARROW block_expr_dot { /*{o}$$ = mk_node("ArmNonblock", 4, $1, $2, $3, $5);*/ }
;

block_match_clause
: maybe_outer_attrs pats_or maybe_guard FAT_ARROW block      { /*{o}$$ = mk_node("ArmBlock", 4, $1, $2, $3, $5);*/ }
| maybe_outer_attrs pats_or maybe_guard FAT_ARROW block_expr { /*{o}$$ = mk_node("ArmBlock", 4, $1, $2, $3, $5);*/ }
;

maybe_guard
: IF expr_nostruct           { /*{o}$$ = $2;*/ }
| %empty                     { /*{o}$$ = mk_none();*/ }
;

expr_if
: IF expr_nostruct block                    { /*{o}$$ = mk_node("ExprIf", 2, $2, $3);*/
                                              newstack($$) = code_ifthenelset(parser_stack($2), to_code(parser_stack($3))); }
| IF expr_nostruct block ELSE block_or_if   { /*{o}$$ = mk_node("ExprIf", 3, $2, $3, $5);*/
                                              newstack($$) = code_ifthenelset(parser_stack($2), to_code(parser_stack($3)), to_code(parser_stack($5))); }
;

expr_if_let
: IF LET pat '=' expr_nostruct block                  { /*{o}$$ = mk_node("ExprIfLet", 3, $3, $5, $6);*/ }
| IF LET pat '=' expr_nostruct block ELSE block_or_if { /*{o}$$ = mk_node("ExprIfLet", 4, $3, $5, $6, $8);*/ }
;

block_or_if
: block
| expr_if
| expr_if_let
;

expr_while
: maybe_label WHILE expr_nostruct block               { /*{o}$$ = mk_node("ExprWhile", 3, $1, $3, $4);*/
                                                        newstack($$) = code_whilet(parser_stack($3), to_code(parser_stack($4)));  }
;

expr_while_let
: maybe_label WHILE LET pat '=' expr_nostruct block   { /*{o}$$ = mk_node("ExprWhileLet", 4, $1, $4, $6, $7);*/ }
;

expr_loop
: maybe_label LOOP block                              { /*{o}$$ = mk_node("ExprLoop", 2, $1, $3);*/
                                                        newstack($$) = code_whilet(true_exprt(), to_code(parser_stack($3))); }
;

expr_for
: maybe_label FOR pat IN expr_nostruct block          { /*{o}$$ = mk_node("ExprForLoop", 4, $1, $3, $5, $6);*/ }
;

maybe_label
: lifetime ':'
| %empty { /*{o}$$ = mk_none();*/ }
;

let
: LET pat maybe_ty_ascription maybe_init_expr ';'
  {
    /*{o}$$ = mk_node("DeclLocal", 3, $2, $3, $4);*/
    
    if(parser_stack($4).id() != "ID_emptyinitexpr") // if given assignment expression
    {
      codet declblock(ID_decl_block);
      codet decl(ID_decl);

      // if type ascription given
      if(parser_stack($3).id() != "ID_emptytyascript") 
      {
        irep_idt symbolName(to_symbol_expr(parser_stack($2)).get_identifier());
        symbol_exprt symbol(symbol_exprt(symbolName, parser_stack($3).type()));

        decl.add_to_operands(symbol);
      }
      else // no type ascription given
      {
        decl.add_to_operands(parser_stack($2));
      }

      // if assignment is a code expression
      if(parser_stack($4).id() == ID_code) 
      {
        codet& code = to_code(parser_stack($4));
        irep_idt statement = code.get_statement();
        side_effect_exprt rhs(ID_statement_expression, exprt::operandst(), typet(), source_locationt());
        if(statement == ID_block)
        {
          rhs.add_to_operands(to_code_block(code));
        }
        // if already a wrapped side effect(namely function calls)
        else if(statement == ID_expression && code.op0().id() == ID_side_effect)
        {
          rhs = to_side_effect_expr(code.op0());
        }
        else // general case
        {
          code_blockt wrapper_block;
          wrapper_block.add_to_operands(code);
          rhs.add_to_operands(wrapper_block);
        }
        code_assignt assignment(parser_stack($2), rhs);
        declblock.add_to_operands(decl);
        declblock.add_to_operands(assignment);
      }
      else
      {
        code_assignt assignment(parser_stack($2), parser_stack($4));
        declblock.add_to_operands(decl);
        declblock.add_to_operands(assignment);
      }
      
      newstack($$).swap(declblock);
    }
    else // if assignment was not specified, type must have been
    {
      irep_idt symbolName(to_symbol_expr(parser_stack($2)).get_identifier());
      symbol_exprt symbol(symbol_exprt(symbolName, parser_stack($3).type()));
      code_declt decl(symbol);
      newstack($$).swap(decl);
    }
  }
;

////////////////////////////////////////////////////////////////////////
// Part 5: Macros and misc. rules
////////////////////////////////////////////////////////////////////////

lit
: LIT_BYTE      { /*{o}$$ = mk_node("LitByte", 1, mk_atom(yyrusttext));*/ }
| LIT_CHAR      { /*{o}$$ = mk_node("LitChar", 1, mk_atom(yyrusttext));*/
                  constant_exprt a(yyrusttext, char_type());
                  newstack($$).swap(a); }
| LIT_INTEGER   { newstack($$) = from_integer(string2integer(yyrusttext), unsigned_int_type()); }
| LIT_FLOAT     { /*{o}$$ = mk_node("LitFloat", 1, mk_atom(yyrusttext));*/
                  parse_floatt parsed_float(yyrusttext);
                  floatbv_typet type = float_type();
                  ieee_floatt a(type);
                  a.from_base10(parsed_float.significand, parsed_float.exponent);
                  constant_exprt result = a.to_expr();
                  result.type() = type;
                  newstack($$).swap(result); }
| TRUE          { /*{o}$$ = mk_node("LitBool", 1, mk_atom(yyrusttext));*/
                  newstack($$) = true_exprt(); }
| FALSE         { /*{o}$$ = mk_node("LitBool", 1, mk_atom(yyrusttext));*/
                  newstack($$) = false_exprt(); }
| str
;

str
: LIT_STR                    { /*{o}$$ = mk_node("LitStr", 1, mk_atom(yyrusttext), mk_atom("CookedStr"));*/ }
| LIT_STR_RAW                { /*{o}$$ = mk_node("LitStr", 1, mk_atom(yyrusttext), mk_atom("RawStr"));*/ }
| LIT_BYTE_STR                 { /*{o}$$ = mk_node("LitByteStr", 1, mk_atom(yyrusttext), mk_atom("ByteStr"));*/ }
| LIT_BYTE_STR_RAW             { /*{o}$$ = mk_node("LitByteStr", 1, mk_atom(yyrusttext), mk_atom("RawByteStr"));*/ }
;

maybe_ident
: %empty { newstack($$) = symbol_exprt_typeless_empty(""); }
| ident
;

ident
: IDENT                      { newstack($$) = symbol_exprt_typeless_empty(yyrusttext); }
// Weak keywords that can be used as identifiers
| CATCH                      { /*{o}$$ = mk_node("ident", 1, mk_atom(yyrusttext));*/ }
| DEFAULT                    { /*{o}$$ = mk_node("ident", 1, mk_atom(yyrusttext));*/ }
| UNION                      { /*{o}$$ = mk_node("ident", 1, mk_atom(yyrusttext));*/ }
;

// TODO: IDs to use can be found at line 477 in src/jsil/parser.y
unpaired_token 
: SHL                        { newstack($$) = symbol_exprt(yyrusttext, typet(ID_shl)); }
| SHR                        { newstack($$) = symbol_exprt(yyrusttext, typet(ID_shr)); }
| LE                         { newstack($$) = symbol_exprt(yyrusttext, typet(ID_le)); }
| EQEQ                       { newstack($$) = symbol_exprt(yyrusttext, typet(ID_equal)); }
| NE                         { newstack($$) = symbol_exprt(yyrusttext, typet(ID_notequal)); }
| GE                         { newstack($$) = symbol_exprt(yyrusttext, typet(ID_ge)); }
| ANDAND                     { newstack($$) = symbol_exprt(yyrusttext, typet(ID_and)); }
| OROR                       { newstack($$) = symbol_exprt(yyrusttext, typet(ID_or)); }
| LARROW                     { /*{o}$$ = mk_atom(yyrusttext);*/ }
| SHLEQ                      { newstack($$) = symbol_exprt_typeless_empty(yyrusttext); }
| SHREQ                      { newstack($$) = symbol_exprt_typeless_empty(yyrusttext); }
| MINUSEQ                    { newstack($$) = symbol_exprt_typeless_empty(yyrusttext); }
| ANDEQ                      { newstack($$) = symbol_exprt_typeless_empty(yyrusttext); }
| OREQ                       { newstack($$) = symbol_exprt_typeless_empty(yyrusttext); }
| PLUSEQ                     { newstack($$) = symbol_exprt_typeless_empty(yyrusttext); }
| STAREQ                     { newstack($$) = symbol_exprt_typeless_empty(yyrusttext); }
| SLASHEQ                    { newstack($$) = symbol_exprt_typeless_empty(yyrusttext); }
| CARETEQ                    { newstack($$) = symbol_exprt_typeless_empty(yyrusttext); }
| PERCENTEQ                  { newstack($$) = symbol_exprt_typeless_empty(yyrusttext); }
| DOTDOT                     { /*{o}$$ = mk_atom(yyrusttext);*/ }
| DOTDOTDOT                  { /*{o}$$ = mk_atom(yyrusttext);*/ }
| MOD_SEP                    { /*{o}$$ = mk_atom(yyrusttext);*/ }
| RARROW                     { /*{o}$$ = mk_atom(yyrusttext);*/ }
| FAT_ARROW                  { /*{o}$$ = mk_atom(yyrusttext);*/ }
| LIT_BYTE                   { /*{o}$$ = mk_atom(yyrusttext);*/ }
| LIT_CHAR                   { newstack($$) = symbol_exprt(yyrusttext, char_type()); }
| LIT_INTEGER                { newstack($$) = symbol_exprt(yyrusttext, signed_int_type()); }
| LIT_FLOAT                  { newstack($$) = symbol_exprt(yyrusttext, float_type()); }
| LIT_STR                    { /*{o}$$ = mk_atom(yyrusttext);*/ }
| LIT_STR_RAW                { /*{o}$$ = mk_atom(yyrusttext);*/ }
| LIT_BYTE_STR               { /*{o}$$ = mk_atom(yyrusttext);*/ }
| LIT_BYTE_STR_RAW           { /*{o}$$ = mk_atom(yyrusttext);*/ }
| IDENT                      { newstack($$) = symbol_exprt_typeless_empty(yyrusttext); }
| UNDERSCORE                 { /*{o}$$ = mk_atom(yyrusttext);*/ }
| LIFETIME                   { /*{o}$$ = mk_atom(yyrusttext);*/ }
| SELF                       { /*{o}$$ = mk_atom(yyrusttext);*/ }
| STATIC                     { /*{o}$$ = mk_atom(yyrusttext);*/ }
| ABSTRACT                   { /*{o}$$ = mk_atom(yyrusttext);*/ }
| ALIGNOF                    { /*{o}$$ = mk_atom(yyrusttext);*/ }
| AS                         { /*{o}$$ = mk_atom(yyrusttext);*/ }
| BECOME                     { /*{o}$$ = mk_atom(yyrusttext);*/ }
| BREAK                      { newstack($$) = symbol_exprt(yyrusttext, c_bool_type());  }
| CATCH                      { /*{o}$$ = mk_atom(yyrusttext);*/ }
| CRATE                      { /*{o}$$ = mk_atom(yyrusttext);*/ }
| DEFAULT                    { /*{o}$$ = mk_atom(yyrusttext);*/ }
| DO                         { /*{o}$$ = mk_atom(yyrusttext);*/ }
| ELSE                       { /*{o}$$ = mk_atom(yyrusttext);*/ }
| ENUM                       { /*{o}$$ = mk_atom(yyrusttext);*/ }
| EXTERN                     { /*{o}$$ = mk_atom(yyrusttext);*/ }
| FALSE                      { newstack($$) = symbol_exprt(yyrusttext, c_bool_type()); }
| FINAL                      { /*{o}$$ = mk_atom(yyrusttext);*/ }
| FN                         { /*{o}$$ = mk_atom(yyrusttext);*/ }
| FOR                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| IF                         { /*{o}$$ = mk_atom(yyrusttext);*/ }
| IMPL                       { /*{o}$$ = mk_atom(yyrusttext);*/ }
| IN                         { /*{o}$$ = mk_atom(yyrusttext);*/ }
| LET                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| LOOP                       { newstack($$) = symbol_exprt_typeless_empty(yyrusttext); }
| MACRO                      { /*{o}$$ = mk_atom(yyrusttext);*/ }
| MATCH                      { /*{o}$$ = mk_atom(yyrusttext);*/ }
| MOD                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| MOVE                       { /*{o}$$ = mk_atom(yyrusttext);*/ }
| MUT                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| OFFSETOF                   { /*{o}$$ = mk_atom(yyrusttext);*/ }
| OVERRIDE                   { /*{o}$$ = mk_atom(yyrusttext);*/ }
| PRIV                       { /*{o}$$ = mk_atom(yyrusttext);*/ }
| PUB                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| PURE                       { /*{o}$$ = mk_atom(yyrusttext);*/ }
| REF                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| RETURN                     { /*{o}$$ = mk_atom(yyrusttext);*/ }
| STRUCT                     { /*{o}$$ = mk_atom(yyrusttext);*/ }
| SIZEOF                     { /*{o}$$ = mk_atom(yyrusttext);*/ }
| SUPER                      { /*{o}$$ = mk_atom(yyrusttext);*/ }
| TRUE                       { newstack($$) = symbol_exprt(yyrusttext, c_bool_type()); }
| TRAIT                      { /*{o}$$ = mk_atom(yyrusttext);*/ }
| TYPE                       { /*{o}$$ = mk_atom(yyrusttext);*/ }
| UNION                      { /*{o}$$ = mk_atom(yyrusttext);*/ }
| UNSAFE                     { /*{o}$$ = mk_atom(yyrusttext);*/ }
| UNSIZED                    { /*{o}$$ = mk_atom(yyrusttext);*/ }
| USE                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| VIRTUAL                    { /*{o}$$ = mk_atom(yyrusttext);*/ }
| WHILE                      { newstack($$) = symbol_exprt_typeless_empty(yyrusttext);  }
| YIELD                      { /*{o}$$ = mk_atom(yyrusttext);*/ }
| CONTINUE                   { /*{o}$$ = mk_atom(yyrusttext);*/ }
| PROC                       { /*{o}$$ = mk_atom(yyrusttext);*/ }
| BOX                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| CONST                      { /*{o}$$ = mk_atom(yyrusttext);*/ }
| WHERE                      { /*{o}$$ = mk_atom(yyrusttext);*/ }
| TYPEOF                     { /*{o}$$ = mk_atom(yyrusttext);*/ }
| INNER_DOC_COMMENT          { /*{o}$$ = mk_atom(yyrusttext);*/ }
| OUTER_DOC_COMMENT          { /*{o}$$ = mk_atom(yyrusttext);*/ }
| SHEBANG                    { /*{o}$$ = mk_atom(yyrusttext);*/ }
| STATIC_LIFETIME            { /*{o}$$ = mk_atom(yyrusttext);*/ }
| ';'                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| ','                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| '.'                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| '@'                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| '#'                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| '~'                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| ':'                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| '$'                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| '='                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| '?'                        { /*{o}$$ = mk_atom(yyrusttext);*/ }
| '!'                        { newstack($$) = symbol_exprt(yyrusttext, typet(ID_bitnot)); }
| '<'                        { newstack($$) = symbol_exprt(yyrusttext, typet(ID_lt)); }
| '>'                        { newstack($$) = symbol_exprt(yyrusttext, typet(ID_gt)); }
| '-'                        { newstack($$) = symbol_exprt(yyrusttext, typet(ID_minus)); }
| '&'                        { newstack($$) = symbol_exprt(yyrusttext, typet(ID_bitand)); }
| '|'                        { newstack($$) = symbol_exprt(yyrusttext, typet(ID_bitor)); }
| '+'                        { newstack($$) = symbol_exprt(yyrusttext, typet(ID_plus)); }
| '*'                        { newstack($$) = symbol_exprt(yyrusttext, typet(ID_mult)); }
| '/'                        { newstack($$) = symbol_exprt(yyrusttext, typet(ID_div)); }
| '^'                        { newstack($$) = symbol_exprt(yyrusttext, typet(ID_bitxor)); }
| '%'                        { newstack($$) = symbol_exprt(yyrusttext, typet(ID_mod)); }
;

token_trees
: %empty                     { /*{o}$$ = mk_node("TokenTrees", 0);*/
                               multi_ary_exprt empty("ID_token_tree", exprt::operandst(), typet());
                               newstack($$).swap(empty); }
| token_trees token_tree     { /*{o}$$ = ext_node($1, 1, $2);*/
                               multi_ary_exprt tokTree = to_multi_ary_expr(parser_stack($1));
                               tokTree.add_to_operands(parser_stack($2));
                               newstack($$).swap(tokTree); }
;

token_tree
: delimited_token_trees
| unpaired_token         { /*{o}$$ = mk_node("TTTok", 1, $1);*/
                           $$ = $1; }
;

delimited_token_trees
: parens_delimited_token_trees
| braces_delimited_token_trees
| brackets_delimited_token_trees
;

parens_delimited_token_trees
: '(' token_trees ')'
{
  /*{o}$$ = mk_node("TTDelim", 3, mk_node("TTTok", 1, mk_atom("(")), $2, mk_node("TTTok", 1, mk_atom(")")));*/
  multi_ary_exprt parenthesized("ID_token_tree", exprt::operandst(), typet());
  parenthesized.add_to_operands(symbol_exprt_typeless_empty("("));
  parenthesized.add_to_operands(parser_stack($2));
  parenthesized.add_to_operands(symbol_exprt_typeless_empty(")"));
  newstack($$).swap(parenthesized);
}
;

braces_delimited_token_trees
: '{' token_trees '}'
{
  /*{o}$$ = mk_node("TTDelim", 3, mk_node("TTTok", 1, mk_atom("{")), $2, mk_node("TTTok", 1, mk_atom("}")));*/
}
;

brackets_delimited_token_trees
: '[' token_trees ']'
{
  /*{o}$$ = mk_node("TTDelim", 3, mk_node("TTTok", 1, mk_atom("[")), $2, mk_node("TTTok", 1, mk_atom("]")));*/
}
;
