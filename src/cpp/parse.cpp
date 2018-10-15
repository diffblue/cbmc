/*******************************************************************\

Module: C++ Language Parsing

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Parsing

#include "cpp_parser.h"

#include <cassert>
#include <map>

#include <util/c_types.h>
#include <util/expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <ansi-c/ansi_c_y.tab.h>
#include <ansi-c/merged_type.h>

#include "cpp_token_buffer.h"
#include "cpp_member_spec.h"
#include "cpp_enum_type.h"

#ifdef DEBUG
#include <iostream>

static unsigned __indent;

struct indenter // NOLINT(readability/identifiers)
{
  indenter() { __indent+=2; }
  ~indenter() { __indent-=2; }
};

#define TOK_TEXT \
{ \
  cpp_tokent _tk; \
  lex.LookAhead(0, _tk); \
  std::cout << std::string(__indent, ' ') << "Text [" << _tk.line_no << "]: " \
    << _tk.text << '\n'; \
}
#endif

class new_scopet
{
public:
  new_scopet():kind(kindt::NONE), anon_count(0), parent(nullptr)
  {
  }

  enum class kindt
  {
    NONE,
    TEMPLATE,
    MEMBER,
    FUNCTION,
    VARIABLE,
    TYPEDEF,
    TAG,
    NAMESPACE,
    CLASS_TEMPLATE,
    MEMBER_TEMPLATE,
    FUNCTION_TEMPLATE,
    BLOCK,
    NON_TYPE_TEMPLATE_PARAMETER,
    TYPE_TEMPLATE_PARAMETER,
    TEMPLATE_TEMPLATE_PARAMETER
  };

  kindt kind;
  irep_idt id;

  bool is_type() const
  {
    return kind==kindt::TYPEDEF ||
           kind==kindt::TYPE_TEMPLATE_PARAMETER ||
           kind==kindt::TAG ||
           kind==kindt::CLASS_TEMPLATE;
  }

  bool is_template() const
  {
    return kind==kindt::FUNCTION_TEMPLATE ||
           kind==kindt::CLASS_TEMPLATE ||
           kind==kindt::MEMBER_TEMPLATE;
  }

  bool is_named_scope() const
  {
    return kind==kindt::NAMESPACE ||
           kind==kindt::TAG ||
           kind==kindt::TYPE_TEMPLATE_PARAMETER;
  }

  static const char *kind2string(kindt kind)
  {
    switch(kind)
    {
    case kindt::NONE:
      return "?";
    case kindt::TEMPLATE:
      return "TEMPLATE";
    case kindt::MEMBER:
      return "MEMBER";
    case kindt::FUNCTION:
      return "FUNCTION";
    case kindt::VARIABLE:
      return "VARIABLE";
    case kindt::TYPEDEF:
      return "TYPEDEF";
    case kindt::TAG:
      return "TAG";
    case kindt::NAMESPACE:
      return "NAMESPACE";
    case kindt::CLASS_TEMPLATE:
      return "CLASS_TEMPLATE";
    case kindt::MEMBER_TEMPLATE:
      return "MEMBER_TEMPLATE";
    case kindt::FUNCTION_TEMPLATE:
      return "FUNCTION_TEMPLATE";
    case kindt::BLOCK:
      return "BLOCK";
    case kindt::NON_TYPE_TEMPLATE_PARAMETER:
      return "NON_TYPE_TEMPLATE_PARAMETER";
    case kindt::TYPE_TEMPLATE_PARAMETER:
      return "TYPE_TEMPLATE_PARAMETER";
    case kindt::TEMPLATE_TEMPLATE_PARAMETER:
      return "TEMPLATE_TEMPLATE_PARAMETER";
    default:
      return "";
    }
  }

  typedef std::map<irep_idt, new_scopet> id_mapt;
  id_mapt id_map;

  std::size_t anon_count;

  new_scopet *parent;

  inline void print(std::ostream &out) const
  {
    print_rec(out, 0);
  }

  irep_idt get_anon_id()
  {
    ++anon_count;
    return "#anon"+std::to_string(anon_count);
  }

  std::string full_name() const
  {
    return (parent==nullptr?"":(parent->full_name()+"::"))+
           id2string(id);
  }

protected:
  void print_rec(std::ostream &, unsigned indent) const;
};

class save_scopet
{
public:
  explicit save_scopet(new_scopet *&_scope):
    scope_ptr(_scope), old_scope(_scope)
  {
  }

  inline ~save_scopet()
  {
    scope_ptr=old_scope;
  }

protected:
  new_scopet *&scope_ptr;
  new_scopet *old_scope;
};

void new_scopet::print_rec(std::ostream &out, unsigned indent) const
{
  for(id_mapt::const_iterator
      it=id_map.begin();
      it!=id_map.end();
      it++)
  {
    out << std::string(indent, ' ')
        << it->first << ": "
        << kind2string(it->second.kind)
        << "\n";
    it->second.print_rec(out, indent+2);
  }
}

class Parser // NOLINT(readability/identifiers)
{
public:
  explicit Parser(cpp_parsert &_cpp_parser):
    lex(_cpp_parser.token_buffer),
    parser(_cpp_parser),
    max_errors(10)
  {
    root_scope.kind=new_scopet::kindt::NAMESPACE;
    current_scope=&root_scope;
  }

  bool operator()();

protected:
  cpp_token_buffert &lex;
  cpp_parsert &parser;

  // scopes
  new_scopet root_scope;
  new_scopet *current_scope;
  new_scopet &add_id(const irept &name, new_scopet::kindt);
  new_scopet &add_id(const irep_idt &, new_scopet::kindt);
  void make_sub_scope(const irept &name, new_scopet::kindt);
  void make_sub_scope(const irep_idt &, new_scopet::kindt);

  enum DeclKind { kDeclarator, kArgDeclarator, kCastDeclarator };
  enum TemplateDeclKind { tdk_unknown, tdk_decl, tdk_instantiation,
                          tdk_specialization, num_tdks };

  // rules
  bool rProgram(cpp_itemt &item);

  bool SyntaxError();

  bool rDefinition(cpp_itemt &);
  bool rNullDeclaration(cpp_declarationt &);
  bool rTypedef(cpp_declarationt &);
  bool rTypedefUsing(cpp_declarationt &);
  bool rTypedefStatement(codet &);
  bool rTypeSpecifier(typet &, bool);
  bool isTypeSpecifier();
  bool rLinkageSpec(cpp_linkage_spect &);
  bool rNamespaceSpec(cpp_namespace_spect &);
  bool rUsing(cpp_usingt &);
  bool rStaticAssert(cpp_static_assertt &);
  bool rLinkageBody(cpp_linkage_spect::itemst &);
  bool rTemplateDecl(cpp_declarationt &);
  bool rTemplateDecl2(typet &, TemplateDeclKind &kind);
  bool rTempArgList(irept &);
  bool rTempArgDeclaration(cpp_declarationt &);
  bool rExternTemplateDecl(cpp_declarationt &);

  bool rDeclaration(cpp_declarationt &);
  bool rIntegralDeclaration(
    cpp_declarationt &,
    cpp_storage_spect &,
    cpp_member_spect &,
    typet &,
    typet &);
  bool rConstDeclaration(cpp_declarationt &);
  bool rOtherDeclaration(
    cpp_declarationt &,
    cpp_storage_spect &,
    cpp_member_spect &,
    typet &);
  bool rCondition(exprt &);
  bool rSimpleDeclaration(cpp_declarationt &);

  bool isConstructorDecl();
  bool isPtrToMember(int);
  bool optMemberSpec(cpp_member_spect &);
  bool optStorageSpec(cpp_storage_spect &);
  bool optCvQualify(typet &);
  bool optAlignas(typet &);
  bool rAttribute(typet &);
  bool optAttribute(typet &);
  bool optIntegralTypeOrClassSpec(typet &);
  bool rConstructorDecl(
    cpp_declaratort &,
    typet &,
    typet &trailing_return_type);
  bool optThrowDecl(irept &);

  bool rDeclarators(cpp_declarationt::declaratorst &, bool, bool=false);
  bool rDeclaratorWithInit(cpp_declaratort &, bool, bool);
  bool rDeclarator(cpp_declaratort &, DeclKind, bool, bool);
  bool rDeclaratorQualifier();
  bool optPtrOperator(typet &);
  bool rMemberInitializers(irept &);
  bool rMemberInit(exprt &);

  bool rName(irept &);
  bool rOperatorName(irept &);
  bool rCastOperatorName(irept &);
  bool rPtrToMember(irept &);
  bool rTemplateArgs(irept &);

  bool rArgDeclListOrInit(exprt &, bool&, bool);
  bool rArgDeclList(irept &);
  bool rArgDeclaration(cpp_declarationt &);

  bool rFunctionArguments(exprt &);
  bool rInitializeExpr(exprt &);

  bool rEnumSpec(typet &);
  bool rEnumBody(irept &);
  bool rClassSpec(typet &);
  bool rBaseSpecifiers(irept &);
  bool rClassBody(exprt &);
  bool rClassMember(cpp_itemt &);
  bool rAccessDecl(cpp_declarationt &);

  bool rCommaExpression(exprt &);

  bool rExpression(exprt &, bool);
  bool rConditionalExpr(exprt &, bool);
  bool rLogicalOrExpr(exprt &, bool);
  bool rLogicalAndExpr(exprt &, bool);
  bool rInclusiveOrExpr(exprt &, bool);
  bool rExclusiveOrExpr(exprt &, bool);
  bool rAndExpr(exprt &, bool);
  bool rEqualityExpr(exprt &, bool);
  bool rRelationalExpr(exprt &, bool);
  bool rShiftExpr(exprt &, bool);
  bool rAdditiveExpr(exprt &);
  bool rMultiplyExpr(exprt &);
  bool rPmExpr(exprt &);
  bool rCastExpr(exprt &);
  bool rTypeName(typet &);
  bool rTypeNameOrFunctionType(typet &);
  bool rUnaryExpr(exprt &);
  bool rThrowExpr(exprt &);
  bool rNoexceptExpr(exprt &);
  bool rSizeofExpr(exprt &);
  bool rTypeidExpr(exprt &);
  bool rAlignofExpr(exprt &);
  bool isAllocateExpr(int);
  bool rAllocateExpr(exprt &);
  bool rAllocateType(exprt &, typet &, exprt &);
  bool rNewDeclarator(typet &);
  bool rAllocateInitializer(exprt &);
  bool rPostfixExpr(exprt &);
  bool rPrimaryExpr(exprt &);
  bool rVarName(exprt &);
  bool rVarNameCore(exprt &);
  bool maybeTemplateArgs();

  bool rFunctionBody(cpp_declaratort &);
  bool rCompoundStatement(codet &);
  bool rStatement(codet &);
  bool rIfStatement(codet &);
  bool rSwitchStatement(codet &);
  bool rWhileStatement(codet &);
  bool rDoStatement(codet &);
  bool rForStatement(codet &);
  bool rTryStatement(codet &);

  bool rExprStatement(codet &);
  bool rDeclarationStatement(codet &);
  bool rIntegralDeclStatement(codet &, cpp_storage_spect &, typet &, typet &);
  bool rOtherDeclStatement(codet &, cpp_storage_spect &, typet &);

  bool MaybeTypeNameOrClassTemplate(cpp_tokent &);
  void SkipTo(int token);
  bool moreVarName();

  bool rString(cpp_tokent &tk);

  // GCC extensions
  bool rGCCAsmStatement(codet &);

  // MSC extensions
  bool rMSC_tryStatement(codet &);
  bool rMSC_leaveStatement(codet &);
  bool rMSCAsmStatement(codet &);
  bool rMSC_if_existsStatement(codet &);
  bool rTypePredicate(exprt &);
  bool rMSCuuidof(exprt &);
  bool rMSC_if_existsExpr(exprt &);

  std::size_t number_of_errors;
  irep_idt current_function;

  void merge_types(const typet &src, typet &dest);

  void set_location(irept &dest, const cpp_tokent &token)
  {
    source_locationt &source_location=
      static_cast<source_locationt &>(dest.add(ID_C_source_location));
    source_location.set_file(token.filename);
    source_location.set_line(token.line_no);
    if(!current_function.empty())
      source_location.set_function(current_function);
  }

  void make_subtype(const typet &src, typet &dest)
  {
    typet *p=&dest;

    while(!p->id().empty() && p->is_not_nil())
    {
      if(p->id()==ID_merged_type)
      {
        auto &merged_type = to_merged_type(*p);
        p = &merged_type.last_type();
      }
      else
        p=&p->subtype();
    }

    *p=src;
  }

  unsigned int max_errors;
};

new_scopet &Parser::add_id(const irept &cpp_name, new_scopet::kindt kind)
{
  irep_idt id;

  if(cpp_name.get_sub().size()==1 &&
     cpp_name.get_sub().front().id()==ID_name)
    id=cpp_name.get_sub().front().get(ID_identifier);
  else
    id=current_scope->get_anon_id();

  return add_id(id, kind);
}

new_scopet &Parser::add_id(const irep_idt &id, new_scopet::kindt kind)
{
  new_scopet &s=current_scope->id_map[id];

  s.kind=kind;
  s.id=id;
  s.parent=current_scope;

  return s;
}

void Parser::make_sub_scope(const irept &cpp_name, new_scopet::kindt kind)
{
  new_scopet &s=add_id(cpp_name, kind);
  current_scope=&s;
}

void Parser::make_sub_scope(const irep_idt &id, new_scopet::kindt kind)
{
  new_scopet &s=add_id(id, kind);
  current_scope=&s;
}

bool Parser::rString(cpp_tokent &tk)
{
  if(lex.get_token(tk)!=TOK_STRING)
    return false;

  return true;
}

void Parser::merge_types(const typet &src, typet &dest)
{
  if(src.is_nil())
    return;

  if(dest.is_nil())
    dest=src;
  else
  {
    if(dest.id()!=ID_merged_type)
    {
      source_locationt location=dest.source_location();
      merged_typet tmp;
      tmp.move_to_subtypes(dest);
      tmp.add_source_location()=location;
      dest=tmp;
    }

    // the end of the subtypes container needs to stay the same,
    // since several analysis functions traverse via the end for
    // merged_types
    auto &sub = to_type_with_subtypes(dest).subtypes();
    sub.emplace(sub.begin(), src);
  }
}

bool Parser::SyntaxError()
{
  #define ERROR_TOKENS 4

  cpp_tokent t[ERROR_TOKENS];

  for(std::size_t i=0; i<ERROR_TOKENS; i++)
    lex.LookAhead(i, t[i]);

  if(t[0].kind!='\0')
  {
    source_locationt source_location;
    source_location.set_file(t[0].filename);
    source_location.set_line(std::to_string(t[0].line_no));

    std::string message="parse error before `";

    for(std::size_t i=0; i<ERROR_TOKENS; i++)
      if(t[i].kind!='\0')
      {
        if(i!=0)
          message+=' ';
        message+=t[i].text;
      }

    message+="'";

    parser.error().source_location=source_location;
    parser.error() << message << messaget::eom;
  }

  return ++number_of_errors < max_errors;
}

bool Parser::rProgram(cpp_itemt &item)
{
  while(lex.LookAhead(0)!='\0')
    if(rDefinition(item))
      return true;
    else
    {
      cpp_tokent tk;

      if(!SyntaxError())
        return false;                // too many errors

      SkipTo(';');
      lex.get_token(tk);        // ignore ';'
    }

  return false;
}

/*
  definition
  : null.declaration
  | typedef
  | template.decl
  | linkage.spec
  | namespace.spec
  | using.declaration
  | extern.template.decl
  | declaration
*/
bool Parser::rDefinition(cpp_itemt &item)
{
  int t=lex.LookAhead(0);

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rDefinition 1 " << t
            << '\n';
  #endif

  if(t==';')
    return rNullDeclaration(item.make_declaration());
  else if(t==TOK_TYPEDEF)
    return rTypedef(item.make_declaration());
  else if(t==TOK_TEMPLATE)
    return rTemplateDecl(item.make_declaration());
  else if(t==TOK_EXTERN && lex.LookAhead(1)==TOK_STRING)
    return rLinkageSpec(item.make_linkage_spec());
  else if(t==TOK_EXTERN && lex.LookAhead(1)==TOK_TEMPLATE)
    return rExternTemplateDecl(item.make_declaration());
  else if(t==TOK_NAMESPACE)
    return rNamespaceSpec(item.make_namespace_spec());
  else if(t==TOK_INLINE && lex.LookAhead(1)==TOK_NAMESPACE)
    return rNamespaceSpec(item.make_namespace_spec());
  else if(t==TOK_USING &&
          lex.LookAhead(1)==TOK_IDENTIFIER &&
          lex.LookAhead(2)=='=')
    return rTypedefUsing(item.make_declaration());
  else if(t==TOK_USING)
    return rUsing(item.make_using());
  else if(t==TOK_STATIC_ASSERT)
    return rStaticAssert(item.make_static_assert());
  else
    return rDeclaration(item.make_declaration());
}

bool Parser::rNullDeclaration(cpp_declarationt &decl)
{
  cpp_tokent tk;

  if(lex.get_token(tk)!=';')
    return false;

  set_location(decl, tk);

  return true;
}

/*
  typedef
  : TYPEDEF type.specifier declarators ';'
*/
bool Parser::rTypedef(cpp_declarationt &declaration)
{
  cpp_tokent tk;

  if(lex.get_token(tk)!=TOK_TYPEDEF)
    return false;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rTypedef 1\n";
  #endif

  declaration=cpp_declarationt();
  set_location(declaration, tk);
  declaration.set_is_typedef();

  if(!rTypeSpecifier(declaration.type(), true))
    return false;

  if(!rDeclarators(declaration.declarators(), true))
    return false;

  return true;
}

/*
  USING Identifier '=' type.specifier ';'
*/
bool Parser::rTypedefUsing(cpp_declarationt &declaration)
{
  cpp_tokent tk;
  typet type_name;

  if(lex.get_token(tk)!=TOK_USING)
    return false;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rTypedefUsing 1\n";
  #endif

  declaration=cpp_declarationt();
  set_location(declaration, tk);

  declaration.type()=typet(ID_typedef);

  if(lex.get_token(tk)!=TOK_IDENTIFIER)
    return false;

  cpp_declaratort name;
  name.name()=cpp_namet(tk.data.get(ID_C_base_name));
  name.type().make_nil();

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rTypedefUsing 2\n";
  #endif

  if(lex.get_token(tk)!='=')
    return false;

  if(!rTypeNameOrFunctionType(type_name))
    return false;

  merge_types(type_name, declaration.type());

  declaration.declarators().push_back(name);

  if(lex.get_token(tk)!=';')
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rTypedefUsing 3\n";
  #endif

  return true;
}

bool Parser::rTypedefStatement(codet &statement)
{
  statement=codet(ID_decl);
  statement.operands().resize(1);
  return rTypedef((cpp_declarationt &)statement.op0());
}

/*
  type.specifier
  : {cv.qualify} (integral.or.class.spec | name) {cv.qualify}
*/
bool Parser::rTypeSpecifier(typet &tspec, bool check)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rTypeSpecifier 0\n";
  #endif

  typet cv_q;

  cv_q.make_nil();

  if(!optCvQualify(cv_q))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rTypeSpecifier 0.1\n";
  #endif

  if(!optIntegralTypeOrClassSpec(tspec))
    return false;

  if(tspec.is_nil())
  {
    cpp_tokent tk;
    lex.LookAhead(0, tk);

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rTypeSpecifier 1\n";
    #endif

    if(check)
      if(!MaybeTypeNameOrClassTemplate(tk))
        return false;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rTypeSpecifier 2\n";
    #endif

    if(!rName(tspec))
      return false;
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rTypeSpecifier 3\n";
  #endif

  if(!optCvQualify(cv_q))
    return false;

  merge_types(cv_q, tspec);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rTypeSpecifier 4\n";
  #endif

  return true;
}

// isTypeSpecifier() returns true if the next is probably a type specifier.

bool Parser::isTypeSpecifier()
{
  int t=lex.LookAhead(0);

  if(t==TOK_IDENTIFIER || t==TOK_SCOPE
       || t==TOK_CONSTEXPR || t==TOK_CONST || t==TOK_VOLATILE || t==TOK_RESTRICT
       || t==TOK_CHAR || t==TOK_INT || t==TOK_SHORT || t==TOK_LONG
       || t==TOK_CHAR16_T || t==TOK_CHAR32_T
       || t==TOK_WCHAR_T || t==TOK_COMPLEX // new !!!
       || t==TOK_SIGNED || t==TOK_UNSIGNED || t==TOK_FLOAT || t==TOK_DOUBLE
       || t==TOK_INT8 || t==TOK_INT16 || t==TOK_INT32 || t==TOK_INT64
       || t==TOK_GCC_INT128
       || t==TOK_PTR32 || t==TOK_PTR64
       || t==TOK_GCC_FLOAT80 || t==TOK_GCC_FLOAT128
       || t==TOK_VOID || t==TOK_BOOL || t==TOK_CPROVER_BOOL
       || t==TOK_CLASS || t==TOK_STRUCT || t==TOK_UNION || t==TOK_ENUM
       || t==TOK_INTERFACE
       || t==TOK_TYPENAME
       || t==TOK_TYPEOF
       || t==TOK_DECLTYPE
       || t==TOK_UNDERLYING_TYPE
     )
    return true;

  return false;
}

/*
  linkage.spec
  : EXTERN String definition
  |  EXTERN String linkage.body
*/
bool Parser::rLinkageSpec(cpp_linkage_spect &linkage_spec)
{
  cpp_tokent tk1, tk2;

  if(lex.get_token(tk1)!=TOK_EXTERN)
    return false;

  if(!rString(tk2))
    return false;

  linkage_spec=cpp_linkage_spect();
  set_location(linkage_spec, tk1);
  linkage_spec.linkage().swap(tk2.data);
  set_location(linkage_spec.linkage(), tk2);

  if(lex.LookAhead(0)=='{')
  {
    if(!rLinkageBody(linkage_spec.items()))
      return false;
  }
  else
  {
    cpp_itemt item;

    if(!rDefinition(item))
      return false;

    linkage_spec.items().push_back(item);
  }

  return true;
}

/*
  namespace.spec
  : { INLINE } NAMESPACE Identifier definition
  | { INLINE } NAMESPACE Identifier = name
  | { INLINE } NAMESPACE { Identifier } linkage.body
*/

bool Parser::rNamespaceSpec(cpp_namespace_spect &namespace_spec)
{
  cpp_tokent tk1, tk2;
  bool is_inline=false;

  if(lex.LookAhead(0)==TOK_INLINE)
  {
    lex.get_token(tk1);
    is_inline=true;
  }

  if(lex.get_token(tk1)!=TOK_NAMESPACE)
    return false;

  irep_idt name;

  if(lex.LookAhead(0)=='{')
    name=""; // an anonymous namespace
  else
  {
    if(lex.get_token(tk2)==TOK_IDENTIFIER)
      name=tk2.data.get(ID_C_base_name);
    else
      return false;
  }

  namespace_spec=cpp_namespace_spect();
  set_location(namespace_spec, tk1);
  namespace_spec.set_namespace(name);
  namespace_spec.set_is_inline(is_inline);

  // Tolerate constructs such as:
  // inline namespace __cxx11 __attribute__((__abi_tag__ ("cxx11"))) { }
  // which occurs in glibc. Obviously we need to better than just throw attribs
  // away like this in the future.
  if(lex.LookAhead(0)==TOK_GCC_ATTRIBUTE)
  {
    cpp_tokent tk;
    lex.get_token(tk);

    typet discard;
    if(!rAttribute(discard))
      return false;
  }

  switch(lex.LookAhead(0))
  {
  case '{':
    return rLinkageBody(namespace_spec.items());

  case '=': // namespace alias
    lex.get_token(tk2); // eat =
    return rName(namespace_spec.alias());

  default:
    namespace_spec.items().push_back(cpp_itemt());
    return rDefinition(namespace_spec.items().back());
  }
}

/*
  using.declaration : USING { NAMESPACE } name ';'
*/
bool Parser::rUsing(cpp_usingt &cpp_using)
{
  cpp_tokent tk;

  if(lex.get_token(tk)!=TOK_USING)
    return false;

  cpp_using=cpp_usingt();
  set_location(cpp_using, tk);

  if(lex.LookAhead(0)==TOK_NAMESPACE)
  {
    lex.get_token(tk);
    cpp_using.set_namespace(true);
  }

  if(!rName(cpp_using.name()))
    return false;

  if(lex.get_token(tk)!=';')
    return false;

  return true;
}

/*
  static_assert.declaration : STATIC_ASSERT ( expression , expression ) ';'
*/
bool Parser::rStaticAssert(cpp_static_assertt &cpp_static_assert)
{
  cpp_tokent tk;

  if(lex.get_token(tk)!=TOK_STATIC_ASSERT)
    return false;

  cpp_static_assert=cpp_static_assertt();
  set_location(cpp_static_assert, tk);

  if(lex.get_token(tk)!='(')
    return false;

  if(!rExpression(cpp_static_assert.cond(), false))
    return false;

  if(lex.get_token(tk)!=',')
    return false;

  if(!rExpression(cpp_static_assert.description(), false))
    return false;

  if(lex.get_token(tk)!=')')
    return false;

  if(lex.get_token(tk)!=';')
    return false;

  return true;
}

/*
  linkage.body : '{' (definition)* '}'

  Note: this is also used to construct namespace.spec
*/
bool Parser::rLinkageBody(cpp_linkage_spect::itemst &items)
{
  cpp_tokent op, cp;

  if(lex.get_token(op)!='{')
    return false;

  items.clear();
  while(lex.LookAhead(0)!='}')
  {
    cpp_itemt item;

    if(!rDefinition(item))
    {
      if(!SyntaxError())
        return false;                // too many errors

      SkipTo('}');
      lex.get_token(cp);
      items.push_back(item);
      return true;                // error recovery
    }

    items.push_back(item);
  }

  lex.get_token(cp);
  return true;
}

/*
  template.decl
  : TEMPLATE '<' temp.arg.list '>' declaration
  | TEMPLATE declaration
  | TEMPLATE '<' '>' declaration

  The second case is an explicit template instantiation.  declaration must
  be a class declaration.  For example,

      template class Foo<int, char>;

  explicitly instantiates the template Foo with int and char.

  The third case is a specialization of a function template.  declaration
  must be a function template.  For example,

      template <> int count(String x) { return x.length; }
*/
bool Parser::rTemplateDecl(cpp_declarationt &decl)
{
  TemplateDeclKind kind=tdk_unknown;

  make_sub_scope("#template", new_scopet::kindt::TEMPLATE);
  current_scope->id_map.clear();

  typet template_type;
  if(!rTemplateDecl2(template_type, kind))
    return false;

  cpp_declarationt body;
  if(lex.LookAhead(0)==TOK_USING)
  {
    if(!rTypedefUsing(body))
      return false;
  }
  else if(!rDeclaration(body))
    return false;

  // Repackage the decl and body depending upon what kind of template
  // declaration was observed.
  switch(kind)
  {
  case tdk_decl:
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "BODY: "
              << body.pretty() << '\n';
    std::cout << std::string(__indent, ' ') << "TEMPLATE_TYPE: "
              << template_type.pretty() << '\n';
    #endif
    body.add(ID_template_type).swap(template_type);
    body.set(ID_is_template, true);
    decl.swap(body);
    break;

  case tdk_instantiation:
    // Repackage the decl
    decl=body;
    break;

  case tdk_specialization:
    body.add(ID_template_type).swap(template_type);
    body.set(ID_is_template, true);
    decl.swap(body);
    break;

   default:
    UNREACHABLE;
    break;
  }

  return true;
}

bool Parser::rTemplateDecl2(typet &decl, TemplateDeclKind &kind)
{
  cpp_tokent tk;

  if(lex.get_token(tk)!=TOK_TEMPLATE)
    return false;

  decl=typet(ID_template);
  set_location(decl, tk);

  if(lex.LookAhead(0)!='<')
  {
    // template instantiation
    kind=tdk_instantiation;
    return true;        // ignore TEMPLATE
  }

  if(lex.get_token(tk)!='<')
    return false;

  irept &template_parameters=decl.add(ID_template_parameters);

  if(!rTempArgList(template_parameters))
    return false;

  if(lex.get_token(tk)!='>')
    return false;

  // ignore nested TEMPLATE
  while(lex.LookAhead(0)==TOK_TEMPLATE)
  {
    lex.get_token(tk);
    if(lex.LookAhead(0)!='<')
      break;

    lex.get_token(tk);
    irept dummy_args;
    if(!rTempArgList(dummy_args))
      return false;

    if(lex.get_token(tk)!='>')
      return false;
  }

  if(template_parameters.get_sub().empty())
    // template < > declaration
    kind=tdk_specialization;
  else
    // template < ... > declaration
    kind=tdk_decl;

  return true;
}

/*
  temp.arg.list
  : empty
  | temp.arg.declaration (',' temp.arg.declaration)*
*/
bool Parser::rTempArgList(irept &args)
{
  if(lex.LookAhead(0)=='>')
    return true;

  cpp_declarationt a;
  if(!rTempArgDeclaration(a))
    return false;

  args.get_sub().push_back(get_nil_irep());
  args.get_sub().back().swap(a);

  while(lex.LookAhead(0)==',')
  {
    cpp_tokent tk;

    lex.get_token(tk);
    if(!rTempArgDeclaration(a))
      return false;

    args.get_sub().push_back(get_nil_irep());
    args.get_sub().back().swap(a);
  }

  return true;
}

/*
  temp.arg.declaration
  : CLASS [Identifier] {'=' type.name}
  | CLASS Ellipsis [Identifier]
  | type.specifier arg.declarator {'=' conditional.expr}
  | template.decl2 CLASS Identifier {'=' type.name}
*/
bool Parser::rTempArgDeclaration(cpp_declarationt &declaration)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rTempArgDeclaration 0\n";
  #endif

  int t0=lex.LookAhead(0);

  if((t0==TOK_CLASS || t0==TOK_TYPENAME))
  {
    cpp_token_buffert::post pos=lex.Save();

    cpp_tokent tk1;
    lex.get_token(tk1);

    declaration=cpp_declarationt();
    set_location(declaration, tk1);

    declaration.set(ID_is_type, true);
    declaration.type()=typet("cpp-template-type");

    declaration.declarators().resize(1);
    cpp_declaratort &declarator=declaration.declarators().front();

    declarator=cpp_declaratort();
    declarator.name().make_nil();
    declarator.type().make_nil();
    set_location(declarator, tk1);

    bool has_ellipsis=false;

    if(lex.LookAhead(0)==TOK_ELLIPSIS)
    {
      cpp_tokent tk2;
      lex.get_token(tk2);

      has_ellipsis=true;
    }

    if(lex.LookAhead(0) == TOK_IDENTIFIER)
    {
      cpp_tokent tk2;
      lex.get_token(tk2);

      declarator.name() = cpp_namet(tk2.data.get(ID_C_base_name));
      set_location(declarator.name(), tk2);

      add_id(declarator.name(), new_scopet::kindt::TYPE_TEMPLATE_PARAMETER);

      if(has_ellipsis)
      {
        // TODO
      }
    }

    if(lex.LookAhead(0)=='=')
    {
      if(has_ellipsis)
        return false;

      typet default_type;

      lex.get_token(tk1);
      if(!rTypeName(default_type))
        return false;

      declarator.value()=exprt(ID_type);
      declarator.value().type().swap(default_type);
    }

    if(lex.LookAhead(0)==',' ||
       lex.LookAhead(0)=='>')
      return true;

    lex.Restore(pos);
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rTempArgDeclaration 1\n";
  #endif

  if(t0==TOK_TEMPLATE)
  {
    TemplateDeclKind kind;

    typet template_type;

    if(!rTemplateDecl2(template_type, kind))
      return false;

    // TODO

    cpp_tokent tk1, tk2;

    if(lex.get_token(tk1)!=TOK_CLASS ||
       lex.get_token(tk2)!=TOK_IDENTIFIER)
      return false;

    // Ptree cspec=new PtreeClassSpec(new LeafReserved(tk1),
    //                                  Ptree::Cons(new Leaf(tk2),nil),
    //                                  nil);
    // decl=Ptree::Snoc(decl, cspec);
    if(lex.LookAhead(0)=='=')
    {
      typet default_type;
      lex.get_token(tk1);
      if(!rTypeName(default_type))
          return false;

      // decl=Ptree::Nconc(decl, Ptree::List(new Leaf(tk1),
      //                                      default_type));
    }
  }
  else
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::rTempArgDeclaration 2\n";
    #endif

    declaration=cpp_declarationt();
    declaration.set(ID_is_type, false);

    if(!rTypeSpecifier(declaration.type(), true))
      return false;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::rTempArgDeclaration 3\n";
    #endif

    bool has_ellipsis=false;

    if(lex.LookAhead(0)==TOK_ELLIPSIS)
    {
      cpp_tokent tk2;
      lex.get_token(tk2);

      has_ellipsis=true;
    }

    declaration.declarators().resize(1);
    cpp_declaratort &declarator=declaration.declarators().front();

    if(!rDeclarator(declarator, kArgDeclarator, true, false))
      return false;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::rTempArgDeclaration 4\n";
    #endif

    add_id(declarator.name(), new_scopet::kindt::NON_TYPE_TEMPLATE_PARAMETER);

    if(has_ellipsis)
    {
      // TODO
    }

    exprt &value=declarator.value();

    if(lex.LookAhead(0)=='=')
    {
      if(has_ellipsis)
        return false;

      cpp_tokent tk;

      lex.get_token(tk);
      if(!rConditionalExpr(value, true))
        return false;
    }
    else
      value.make_nil();
  }

  return true;
}

/*
   extern.template.decl
   : EXTERN TEMPLATE declaration
*/
bool Parser::rExternTemplateDecl(cpp_declarationt &decl)
{
  cpp_tokent tk1, tk2;

  if(lex.get_token(tk1)!=TOK_EXTERN)
    return false;

  if(lex.get_token(tk2)!=TOK_TEMPLATE)
    return false;

  if(!rDeclaration(decl))
    return false;

  // decl=new PtreeExternTemplate(new Leaf(tk1),
  //                               Ptree::List(new Leaf(tk2), body));
  return true;
}

/*
  declaration
  : integral.declaration
  | const.declaration
  | other.declaration

  decl.head
  : {member.spec} {storage.spec} {member.spec} {cv.qualify}

  integral.declaration
  : integral.decl.head declarators (';' | function.body)
  | integral.decl.head ';'
  | integral.decl.head ':' expression ';'

  integral.decl.head
  : decl.head integral.or.class.spec {cv.qualify}

  other.declaration
  : decl.head name {cv.qualify} declarators (';' | function.body)
  | decl.head name constructor.decl (';' | function.body)
  | FRIEND name ';'

  const.declaration
  : cv.qualify {'*'} Identifier '=' expression {',' declarators} ';'

  Note: if you modify this function, look at declaration.statement, too.
  Note: this regards a statement like "T (a);" as a constructor
        declaration.  See isConstructorDecl().
*/

bool Parser::rDeclaration(cpp_declarationt &declaration)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rDeclaration 0.1  token: "
            << lex.LookAhead(0) << '\n';
  #endif

  if(!optAttribute(declaration.type()))
    return false;

  cpp_member_spect member_spec;
  if(!optMemberSpec(member_spec))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rDeclaration 0.2\n";
  #endif

  cpp_storage_spect storage_spec;
  if(!optStorageSpec(storage_spec))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rDeclaration 1\n";
  #endif

  if(member_spec.is_empty())
    if(!optMemberSpec(member_spec))
      return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rDeclaration 3\n";
  #endif

  typet cv_q, integral;
  cv_q.make_nil();

  if(!optCvQualify(cv_q))
    return false;

  // added these two to do "const static volatile int i=1;"
  if(!optStorageSpec(storage_spec))
    return false;

  if(!optCvQualify(cv_q))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rDeclaration 4\n";
  #endif

  if(!optIntegralTypeOrClassSpec(integral))
    return false;

  // added this one to do "void inline foo();"
  if(member_spec.is_empty())
    if(!optMemberSpec(member_spec))
      return false;

  if(integral.is_not_nil())
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rDeclaration 5\n";
    #endif
    return
      rIntegralDeclaration(
        declaration, storage_spec, member_spec, integral, cv_q);
  }
  else
  {
    int t=lex.LookAhead(0);

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rDeclaration 6 " << t
              << "\n";
    #endif

    if(cv_q.is_not_nil() &&
       ((t==TOK_IDENTIFIER && lex.LookAhead(1)=='=') || t=='*'))
      return rConstDeclaration(declaration);
    else
      return rOtherDeclaration(declaration, storage_spec, member_spec, cv_q);
  }
}

/* single declaration, for use in a condition (controlling
   expression of switch/while/if) */
bool Parser::rSimpleDeclaration(cpp_declarationt &declaration)
{
  typet cv_q, integral;

  /* no member specification permitted here, and no
     storage specifier:
        type-specifier ::=
           simple-type-specifier
           class-specifier
           enum-specifier
           elaborated-type-specifier
           cv-qualifier */

  cv_q.make_nil();

  if(!optCvQualify(cv_q))
    return false;

  if(!optIntegralTypeOrClassSpec(integral))
    return false;

  if(integral.is_nil() &&
     !rName(integral))
    return false;

  if(cv_q.is_not_nil() && integral.is_not_nil())
    merge_types(cv_q, integral);
  else if(cv_q.is_not_nil() && integral.is_nil())
    integral.swap(cv_q);

  /* no type-specifier so far -> can't be a declaration */
  if(integral.is_nil())
    return false;

  merge_types(cv_q, integral);

  declaration.type().swap(integral);

  cpp_declaratort declarator;
  if(!rDeclarator(declarator, kDeclarator, true, true))
    return false;

  // there really _has_ to be an initializer!

  if(lex.LookAhead(0)!='=')
    return false;

  cpp_tokent eqs;
  lex.get_token(eqs);

  if(!rExpression(declarator.value(), false))
    return false;

  declaration.declarators().push_back(declarator);

  return true;
}

bool Parser::rIntegralDeclaration(
  cpp_declarationt &declaration,
  cpp_storage_spect &storage_spec,
  cpp_member_spect &member_spec,
  typet &integral,
  typet &cv_q)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ')
            << "Parser::rIntegralDeclaration 1  token: "
            << static_cast<char>(lex.LookAhead(0)) << "\n";
  #endif

  if(!optCvQualify(cv_q))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rIntegralDeclaration 2\n";
  #endif

  merge_types(cv_q, integral);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rIntegralDeclaration 3\n";
  #endif

  declaration.type().swap(integral);
  declaration.storage_spec().swap(storage_spec);
  declaration.member_spec().swap(member_spec);

  cpp_tokent tk;

  switch(lex.LookAhead(0))
  {
  case ';':
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::rIntegralDeclaration 4\n";
    #endif

    lex.get_token(tk);
    return true;

  case ':':        // bit field
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::rIntegralDeclaration 5\n";
    #endif

    lex.get_token(tk);

    {
      exprt width;

      if(!rExpression(width, false))
        return false;

      if(lex.get_token(tk)!=';')
        return false;

      // TODO
    }
    return true;

  default:
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::rIntegralDeclaration 6 "
              << lex.LookAhead(0) << "\n";
    #endif

    if(!rDeclarators(declaration.declarators(), true))
      return false;

    // handle trailing return type
    if(
      declaration.type().id() == ID_auto &&
      declaration.declarators().size() == 1 &&
      declaration.declarators().front().type().id() == ID_function_type &&
      declaration.declarators().front().type().subtype().is_not_nil())
    {
      declaration.type() = declaration.declarators().front().type().subtype();
      declaration.declarators().front().type().subtype().make_nil();
    }

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::rIntegralDeclaration 7\n";
    #endif

    if(lex.LookAhead(0)==';')
    {
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ')
                << "Parser::rIntegralDeclaration 8 "
                << declaration.pretty() << '\n';
      #endif
      lex.get_token(tk);
      return true;
    }
    else
    {
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ')
                << "Parser::rIntegralDeclaration 9\n";
      #endif

      if(declaration.declarators().size()!=1)
        return false;

      if(!rFunctionBody(declaration.declarators().front()))
        return false;

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ')
                << "Parser::rIntegralDeclaration 10\n";
      #endif

      return true;
    }
  }
}

bool Parser::rConstDeclaration(cpp_declarationt &declaration)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rConstDeclaration\n";
  #endif

  if(!rDeclarators(declaration.declarators(), false))
    return false;

  if(lex.LookAhead(0)!=';')
    return false;

  cpp_tokent tk;
  lex.get_token(tk);

  return true;
}

bool Parser::rOtherDeclaration(
  cpp_declarationt &declaration,
  cpp_storage_spect &storage_spec,
  cpp_member_spect &member_spec,
  typet &cv_q)
{
  typet type_name;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclaration 1\n";
  #endif

  if(!rName(type_name))
    return false;

  merge_types(cv_q, type_name);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclaration 2\n";
  #endif

  // added this one to do "typename inline foo();"
  if(member_spec.is_empty())
    if(!optMemberSpec(member_spec))
      return false;

  // this allows "typename static foo();"
  if(storage_spec.is_empty())
    if(!optStorageSpec(storage_spec))
      return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclaration 3\n";
  #endif

  bool is_constructor = isConstructorDecl();
  bool is_operator = false;

  if(is_constructor)
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclaration 4\n";
    #endif

    assert(!type_name.get_sub().empty());

    for(std::size_t i=0; i < type_name.get_sub().size(); i++)
    {
      if(type_name.get_sub()[i].id() == ID_operator)
      {
        is_operator = true;
        break;
      }
    }
  }

  if(is_operator && is_constructor)
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclaration 5\n";
    #endif

    // it's a conversion operator
    typet type = type_name;
    type.get_sub().erase(type.get_sub().begin());

    cpp_declaratort conv_operator_declarator;
    typet trailing_return_type;
    if(!rConstructorDecl(
        conv_operator_declarator, type_name, trailing_return_type))
      return false;

    type_name=typet("cpp-cast-operator");

    declaration.declarators().push_back(conv_operator_declarator);
  }
  else if(cv_q.is_nil() && is_constructor)
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclaration 6\n";
    #endif

    assert(!type_name.get_sub().empty());

    bool is_destructor=false;
    forall_irep(it, type_name.get_sub())
      if(it->id()=="~")
      {
        is_destructor=true;
        break;
      }

    cpp_declaratort constructor_declarator;
    typet trailing_return_type;
    if(!rConstructorDecl(
        constructor_declarator, type_name, trailing_return_type))
      return false;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclaration 7\n";
    #endif

    // type_name above is the name declarator, not the return type
    if(storage_spec.is_auto())
      type_name=trailing_return_type;
    else
      type_name=typet(is_destructor?ID_destructor:ID_constructor);

    declaration.declarators().push_back(constructor_declarator);
  }
  else if(!member_spec.is_empty() && lex.LookAhead(0)==';')
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclaration 8\n";
    #endif

    // FRIEND name ';'
    // if(Ptree::Length(member_spec)==1 && member_spec->Car()->What()==FRIEND)
    {
      cpp_tokent tk;
      lex.get_token(tk);
      // statement=new PtreeDeclaration(head, Ptree::List(type_name,
      //                                                   new Leaf(tk)));
      return true;
    }
    // else
    //  return false;
  }
  else
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclaration 9\n";
    #endif

    if(!optCvQualify(cv_q))
      return false;

    merge_types(cv_q, type_name);

    if(!rDeclarators(declaration.declarators(), false))
      return false;
  }

  declaration.type().swap(type_name);
  declaration.storage_spec().swap(storage_spec);
  declaration.member_spec().swap(member_spec);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclaration 10\n";
  #endif

  if(lex.LookAhead(0)==';')
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclaration 11\n";
    #endif

    cpp_tokent tk;
    lex.get_token(tk);
  }
  else
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclaration 12\n";
    #endif

    if(declaration.declarators().size()!=1)
      return false;

    if(!rFunctionBody(declaration.declarators().front()))
      return false;
  }

  return true;
}

/*
  This returns true for an declaration like:
        T (a);
  even if a is not a type name.  This is a bug according to the ANSI
  specification, but I believe none says "T (a);" for a variable
  declaration.
*/
bool Parser::isConstructorDecl()
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::isConstructorDecl "
            << lex.LookAhead(0) << "  "<< lex.LookAhead(1) << "\n";
  #endif

  if(lex.LookAhead(0)!='(')
    return false;
  else
  {
    int t=lex.LookAhead(1);
    if(t=='*' || t=='&' || t=='(')
      return false;        // it's a declarator
    else if(t==TOK_STDCALL || t==TOK_FASTCALL || t==TOK_CLRCALL || t==TOK_CDECL)
      return false;        // it's a declarator
    else if(isPtrToMember(1))
      return false;        // declarator (::*)
    else if(t==TOK_IDENTIFIER)
    {
      // Ambiguous. Do some more look-ahead.
      if(lex.LookAhead(2)==')' &&
         lex.LookAhead(3)=='(')
        return false; // must be declarator (decl)(...)
    }

    // maybe constructor
    return true;
  }
}

/*
  ptr.to.member
  : {'::'} (identifier {'<' any* '>'} '::')+ '*'
*/
bool Parser::isPtrToMember(int i)
{
  int t0=lex.LookAhead(i++);

  if(t0==TOK_SCOPE)
      t0=lex.LookAhead(i++);

  while(t0==TOK_IDENTIFIER)
  {
    int t=lex.LookAhead(i++);
    if(t=='<')
    {
      int n=1;
      while(n > 0)
      {
        int u=lex.LookAhead(i++);
        if(u=='<')
          ++n;
        else if(u=='>')
          --n;
        else if(u=='(')
        {
          int m=1;
          while(m > 0)
          {
            int v=lex.LookAhead(i++);
            if(v=='(')
                ++m;
            else if(v==')')
                --m;
            else if(v=='\0' || v==';' || v=='}')
                return false;
          }
        }
        else if(u=='\0' || u==';' || u=='}')
          return false;
      }

      t=lex.LookAhead(i++);
    }

    if(t!=TOK_SCOPE)
      return false;

    t0=lex.LookAhead(i++);

    if(t0=='*')
      return true;
  }

  return false;
}

/*
  member.spec
  : (FRIEND | INLINE | VIRTUAL | EXPLICIT)+
*/
bool Parser::optMemberSpec(cpp_member_spect &member_spec)
{
  member_spec.clear();

  int t=lex.LookAhead(0);

  while(
    t == TOK_FRIEND || t == TOK_INLINE || t == TOK_VIRTUAL ||
    t == TOK_EXPLICIT || t == TOK_MSC_FORCEINLINE)
  {
    cpp_tokent tk;
    lex.get_token(tk);

    switch(t)
    {
    case TOK_INLINE:
    case TOK_MSC_FORCEINLINE:
      member_spec.set_inline(true);
      break;
    case TOK_VIRTUAL:  member_spec.set_virtual(true); break;
    case TOK_FRIEND:   member_spec.set_friend(true); break;
    case TOK_EXPLICIT: member_spec.set_explicit(true); break;
    default: UNREACHABLE;
    }

    t=lex.LookAhead(0);
  }

  return true;
}

/*
  storage.spec : STATIC | EXTERN | AUTO | REGISTER | MUTABLE | ASM |
                 THREAD_LOCAL
*/
bool Parser::optStorageSpec(cpp_storage_spect &storage_spec)
{
  int t=lex.LookAhead(0);

  if(t==TOK_STATIC ||
     t==TOK_EXTERN ||
     (t == TOK_AUTO && !ansi_c_parser.cpp11) ||
     t==TOK_REGISTER ||
     t==TOK_MUTABLE ||
     t==TOK_GCC_ASM ||
     t==TOK_THREAD_LOCAL)
  {
    cpp_tokent tk;
    lex.get_token(tk);

    switch(t)
    {
    case TOK_STATIC: storage_spec.set_static(); break;
    case TOK_EXTERN: storage_spec.set_extern(); break;
    case TOK_AUTO: storage_spec.set_auto(); break;
    case TOK_REGISTER: storage_spec.set_register(); break;
    case TOK_MUTABLE: storage_spec.set_mutable(); break;
    case TOK_GCC_ASM: storage_spec.set_asm(); break;
    case TOK_THREAD_LOCAL: storage_spec.set_thread_local(); break;
    default: UNREACHABLE;
    }

    set_location(storage_spec, tk);
  }

  return true;
}

/*
  cv.qualify : (CONSTEXPR | CONST | VOLATILE | RESTRICT)+
*/
bool Parser::optCvQualify(typet &cv)
{
  for(;;)
  {
    int t=lex.LookAhead(0);
    if(t==TOK_CONSTEXPR ||
       t==TOK_CONST || t==TOK_VOLATILE || t==TOK_RESTRICT ||
       t==TOK_PTR32 || t==TOK_PTR64 ||
       t==TOK_GCC_ATTRIBUTE || t==TOK_GCC_ASM)
    {
      cpp_tokent tk;
      lex.get_token(tk);
      typet p;

      switch(t)
      {
      case TOK_CONSTEXPR:
        p=typet(ID_constexpr);
        set_location(p, tk);
        merge_types(p, cv);
        break;

      case TOK_CONST:
        p=typet(ID_const);
        set_location(p, tk);
        merge_types(p, cv);
        break;

      case TOK_VOLATILE:
        p=typet(ID_volatile);
        set_location(p, tk);
        merge_types(p, cv);
        break;

      case TOK_RESTRICT:
        p=typet(ID_restrict);
        set_location(p, tk);
        merge_types(p, cv);
        break;

      case TOK_PTR32:
        p=typet(ID_ptr32);
        set_location(p, tk);
        merge_types(p, cv);
        break;

      case TOK_PTR64:
        p=typet(ID_ptr64);
        set_location(p, tk);
        merge_types(p, cv);
        break;

      case TOK_GCC_ATTRIBUTE:
        if(!rAttribute(cv))
          return false;
        break;

      case TOK_GCC_ASM:
        // asm post-declarator
        // this is stuff like
        // int x __asm("asd")=1, y;
        if(lex.get_token(tk)!='(')
          return false;
        if(!rString(tk))
          return false;
        if(lex.get_token(tk)!=')')
          return false;
        break;

      default:
        UNREACHABLE;
        break;
      }
    }
    else
      break;
  }

  return true;
}

/*
  dcl.align
  : ALIGNAS unary.expr
  | ALIGNAS '(' type.name ')'
*/
bool Parser::optAlignas(typet &cv)
{
  if(lex.LookAhead(0)!=TOK_ALIGNAS)
    return true;

  cpp_tokent tk;
  lex.get_token(tk);

  if(lex.LookAhead(0)!='(')
    return false;

  typet tname;
  cpp_tokent op, cp;

  cpp_token_buffert::post pos=lex.Save();
  lex.get_token(op);

  if(rTypeName(tname))
  {
    if(lex.get_token(cp)==')')
    {
      exprt exp(ID_alignof);
      exp.add(ID_type_arg).swap(tname);
      set_location(exp, tk);

      typet attr(ID_aligned);
      set_location(attr, tk);
      attr.add(ID_size, exp);

      merge_types(attr, cv);

      return true;
    }
  }

  lex.Restore(pos);

  exprt exp;

  if(!rCommaExpression(exp))
    return false;

  if(lex.get_token(cp)==')')
  {
    typet attr(ID_aligned);
    set_location(attr, tk);
    attr.add(ID_size, exp);

    merge_types(attr, cv);

    return true;
  }

  return false;
}

bool Parser::rAttribute(typet &t)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rAttribute "
            << lex.LookAhead(0);
  #endif
  cpp_tokent tk;
  lex.get_token(tk);

  switch(tk.kind)
  {
  case '(':
    if(lex.LookAhead(0)!=')')
      rAttribute(t);

    if(lex.LookAhead(0)!=')')
      return false;
    lex.get_token(tk);
    return true;

  case TOK_GCC_ATTRIBUTE_PACKED:
    {
      typet attr(ID_packed);
      set_location(attr, tk);
      merge_types(attr, t);
      break;
    }

  case TOK_GCC_ATTRIBUTE_TRANSPARENT_UNION:
    {
      typet attr(ID_transparent_union);
      set_location(attr, tk);
      merge_types(attr, t);
      break;
    }

  case TOK_GCC_ATTRIBUTE_VECTOR_SIZE:
    {
      cpp_tokent tk2, tk3;

      if(lex.get_token(tk2)!='(')
        return false;

      exprt exp;
      if(!rCommaExpression(exp))
        return false;

      if(lex.get_token(tk3)!=')')
        return false;

      vector_typet attr(nil_typet(), exp);
      attr.add_source_location()=exp.source_location();
      merge_types(attr, t);
      break;
    }

  case TOK_GCC_ATTRIBUTE_ALIGNED:
    {
      typet attr(ID_aligned);
      set_location(attr, tk);

      if(lex.LookAhead(0)=='(')
      {
        cpp_tokent tk2, tk3;

        if(lex.get_token(tk2)!='(')
          return false;

        exprt exp;
        if(!rCommaExpression(exp))
          return false;

        if(lex.get_token(tk3)!=')')
          return false;

        attr.add(ID_size, exp);
      }

      merge_types(attr, t);
      break;
    }

  case TOK_GCC_ATTRIBUTE_MODE:
    {
      cpp_tokent tk2, tk3;

      if(lex.get_token(tk2)!='(')
        return false;

      irept name;
      if(!rName(name))
        return false;

      if(lex.get_token(tk3)!=')')
        return false;

      typet attr(ID_gcc_attribute_mode);
      set_location(attr, tk);
      attr.set(ID_size, name.get(ID_identifier));
      merge_types(attr, t);
      break;
    }

  case TOK_GCC_ATTRIBUTE_GNU_INLINE:
    {
      typet attr(ID_static);
      set_location(attr, tk);
      merge_types(attr, t);
      break;
    }

  case TOK_GCC_ATTRIBUTE_WEAK:
    {
      typet attr(ID_weak);
      set_location(attr, tk);
      merge_types(attr, t);
      break;
    }

  case TOK_GCC_ATTRIBUTE_ALIAS:
    {
      cpp_tokent tk2, tk3, tk4;

      if(lex.get_token(tk2)!='(')
        return false;

      if(!rString(tk3))
        return false;

      if(lex.get_token(tk4)!=')')
        return false;

      typet attr(ID_alias);
      set_location(attr, tk);
      attr.move_to_sub(tk3.data);
      merge_types(attr, t);
      break;
    }

  case TOK_GCC_ATTRIBUTE_SECTION:
    {
      cpp_tokent tk2, tk3, tk4;

      if(lex.get_token(tk2)!='(')
        return false;

      if(!rString(tk3))
        return false;

      if(lex.get_token(tk4)!=')')
        return false;

      typet attr(ID_section);
      set_location(attr, tk);
      attr.move_to_sub(tk3.data);
      merge_types(attr, t);
      break;
    }

  case TOK_GCC_ATTRIBUTE_NORETURN:
    {
      typet attr(ID_noreturn);
      set_location(attr, tk);
      merge_types(attr, t);
      break;
    }

  case TOK_GCC_ATTRIBUTE_CONSTRUCTOR:
    {
      typet attr(ID_constructor);
      set_location(attr, tk);
      merge_types(attr, t);
      break;
    }

  case TOK_GCC_ATTRIBUTE_DESTRUCTOR:
    {
      typet attr(ID_destructor);
      set_location(attr, tk);
      merge_types(attr, t);
      break;
    }

  case ',':
    if(lex.LookAhead(0)==')')
      // the scanner ignored an attribute
      return true;
    break;

  default:
    return false;
  }

  if(lex.LookAhead(0)==')')
    return true;

  return rAttribute(t);
}

bool Parser::optAttribute(typet &t)
{
  if(lex.LookAhead(0)!='[' ||
     lex.LookAhead(1)!='[')
    return true;

  lex.get_token();
  lex.get_token();

  for(;;)
  {
    cpp_tokent tk;
    lex.get_token(tk);

    switch(tk.kind)
    {
    case ']':
      lex.get_token();
      return true;

    case TOK_NORETURN:
      {
        typet attr(ID_noreturn);
        set_location(attr, tk);
        merge_types(attr, t);
        break;
      }

    default:
      return false;
    }
  }
}

/*

  integral.or.class.spec
  : (CHAR | CHAR16_T | CHAR32_T | WCHAR_T
     | INT | SHORT | LONG | SIGNED | UNSIGNED | FLOAT | DOUBLE
     | VOID | BOOLEAN | COMPLEX)+
  | class.spec
  | enum.spec

  Note: if editing this, see also isTypeSpecifier().
*/
bool Parser::optIntegralTypeOrClassSpec(typet &p)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ')
            << "Parser::optIntegralTypeOrClassSpec 0\n";
  #endif // DEBUG

  // This makes no sense, but is used in Visual Studio header files.
  if(lex.LookAhead(0)==TOK_TYPENAME)
  {
    cpp_tokent tk;
    lex.get_token(tk);
  }

  bool is_integral=false;
  p.make_nil();

  int t;

  for(;;)
  {
    t=lex.LookAhead(0);

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::optIntegralTypeOrClassSpec 1\n";
    #endif // DEBUG

    irep_idt type_id;

    switch(t)
    {
    case TOK_CHAR: type_id=ID_char; break;
    case TOK_CHAR16_T: type_id=ID_char16_t; break;
    case TOK_CHAR32_T: type_id=ID_char32_t; break;
    case TOK_INT: type_id=ID_int; break;
    case TOK_SHORT: type_id=ID_short; break;
    case TOK_LONG: type_id=ID_long; break;
    case TOK_SIGNED: type_id=ID_signed; break;
    case TOK_WCHAR_T: type_id=ID_wchar_t; break;
    case TOK_COMPLEX: type_id=ID_complex; break;
    case TOK_UNSIGNED: type_id=ID_unsigned; break;
    case TOK_FLOAT: type_id=ID_float; break;
    case TOK_DOUBLE: type_id=ID_double; break;
    case TOK_VOID: type_id=ID_void; break;
    case TOK_INT8: type_id=ID_int8; break;
    case TOK_INT16: type_id=ID_int16; break;
    case TOK_INT32: type_id=ID_int32; break;
    case TOK_INT64: type_id=ID_int64; break;
    case TOK_GCC_INT128: type_id=ID_gcc_int128; break;
    case TOK_GCC_FLOAT80: type_id=ID_gcc_float80; break;
    case TOK_GCC_FLOAT128: type_id=ID_gcc_float128; break;
    case TOK_BOOL:
      type_id = ID_c_bool;
      break;
    case TOK_CPROVER_BOOL: type_id=ID_proper_bool; break;
    case TOK_AUTO: type_id = ID_auto; break;
    default: type_id=irep_idt();
    }

    if(!type_id.empty())
    {
      cpp_tokent tk;
      typet kw;
      lex.get_token(tk);
      kw=typet(type_id);
      set_location(kw, tk);

      merge_types(kw, p);

      is_integral=true;
    }
    else
      break;
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ')
            << "Parser::optIntegralTypeOrClassSpec 2\n";
  #endif // DEBUG

  if(is_integral)
    return true;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ')
            << "Parser::optIntegralTypeOrClassSpec 3\n";
  #endif // DEBUG

  if(t==TOK_CLASS || t==TOK_STRUCT || t==TOK_UNION || t==TOK_INTERFACE)
    return rClassSpec(p);
  else if(t==TOK_ENUM)
    return rEnumSpec(p);
  else if(t==TOK_TYPEOF)
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::optIntegralTypeOrClassSpec 4\n";
    #endif // DEBUG

    cpp_tokent typeof_tk;
    lex.get_token(typeof_tk);

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::optIntegralTypeOrClassSpec 5\n";
    #endif // DEBUG

    p=typet(ID_typeof);
    set_location(p, typeof_tk);

    cpp_tokent tk;
    if(lex.get_token(tk)!='(')
      return false;

    // the argument can be a type or an expression

    {
      typet tname;
      cpp_token_buffert::post pos=lex.Save();

      if(rTypeName(tname))
      {
        if(lex.get_token(tk)==')')
        {
          p.add(ID_type_arg).swap(tname);
          return true;
        }
      }

      lex.Restore(pos);
    }

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::optIntegralTypeOrClassSpec 6\n";
    #endif // DEBUG

    exprt expr;
    if(!rCommaExpression(expr))
      return false;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::optIntegralTypeOrClassSpec 7\n";
    #endif // DEBUG

    if(lex.get_token(tk)!=')')
      return false;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::optIntegralTypeOrClassSpec 8\n";
    #endif // DEBUG

    p.add(ID_expr_arg).swap(expr);

    return true;
  }
  else if(t==TOK_DECLTYPE)
  {
    cpp_tokent decltype_tk;
    lex.get_token(decltype_tk);

    p=typet(ID_decltype);
    set_location(p, decltype_tk);

    cpp_tokent tk;
    if(lex.get_token(tk)!='(')
      return false;

    // the argument is always an expression

    exprt expr;
    if(!rCommaExpression(expr))
      return false;

    if(lex.get_token(tk)!=')')
      return false;

    p.add(ID_expr_arg).swap(expr);

    return true;
  }
  else if(t==TOK_UNDERLYING_TYPE)
  {
    // A Visual Studio extension that returns the underlying
    // type of an enum.
    cpp_tokent underlying_type_tk;
    lex.get_token(underlying_type_tk);

    p=typet(ID_msc_underlying_type);
    set_location(p, underlying_type_tk);

    cpp_tokent tk;
    if(lex.get_token(tk)!='(')
      return false;

    // the argument is always a type

    typet tname;

    if(!rTypeName(tname))
      return false;

    if(lex.get_token(tk)!=')')
      return false;

    p.add(ID_type_arg).swap(tname);

    return true;
  }
  else
  {
    p.make_nil();
    return true;
  }
}

/*
  constructor.decl
  : '(' {arg.decl.list} ')' {cv.qualify} {throw.decl}
  {member.initializers} {'=' Constant}
*/
bool Parser::rConstructorDecl(
  cpp_declaratort &constructor,
  typet &type_name,
  typet &trailing_return_type)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rConstructorDecl 0\n";
  #endif

  trailing_return_type.make_nil();

  constructor=cpp_declaratort(typet(ID_function_type));
  constructor.type().subtype().make_nil();
  constructor.name().swap(type_name);

  cpp_tokent op;
  if(lex.get_token(op)!='(')
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rConstructorDecl 1\n";
  #endif

  irept &parameters=constructor.type().add(ID_parameters);

  if(lex.LookAhead(0)!=')')
    if(!rArgDeclList(parameters))
      return false;

  cpp_tokent cp;
  lex.get_token(cp);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rConstructorDecl 2\n";
  #endif

  typet &cv=static_cast<typet &>(constructor.add(ID_method_qualifier));
  cv.make_nil();
  optCvQualify(cv);

  optThrowDecl(constructor.throw_decl());

  if(lex.LookAhead(0)==TOK_ARROW)
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rConstructorDecl 3\n";
    #endif

    // C++11 trailing return type
    cpp_tokent arrow;
    lex.get_token(arrow);

    if(!rTypeSpecifier(trailing_return_type, false))
      return false;
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rConstructorDecl 4\n";
  #endif

  if(lex.LookAhead(0)==':')
  {
    irept mi;

    if(rMemberInitializers(mi))
      constructor.member_initializers().swap(mi);
    else
      return false;
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rConstructorDecl 5\n";
  #endif

  if(lex.LookAhead(0)=='=')
  {
    cpp_tokent eq, value;
    lex.get_token(eq);

    switch(lex.get_token(value))
    {
    case TOK_INTEGER:
      {
        constructor.value()=codet("cpp-pure-virtual");
        set_location(constructor.value(), value);
      }
      break;

    case TOK_DEFAULT: // C++0x
      {
        if(!ansi_c_parser.cpp11)
        {
          SyntaxError();
          return false;
        }

        constructor.value()=codet(ID_default);
        set_location(constructor.value(), value);
      }
      break;

    case TOK_DELETE: // C++0x
      {
        if(!ansi_c_parser.cpp11)
        {
          SyntaxError();
          return false;
        }

        constructor.value()=codet(ID_cpp_delete);
        set_location(constructor.value(), value);
      }
      break;

    default:
      return false;
    }
  }
  else
    constructor.add(ID_value).make_nil();

  return true;
}

/*
  throw.decl : THROW '(' (name {','})* {name} ')'
             | THROW '(' '...' ')'
             | NOEXCEPT
*/
bool Parser::optThrowDecl(irept &throw_decl)
{
  cpp_tokent tk;
  int t;
  irept p=get_nil_irep();

  if(lex.LookAhead(0)==TOK_THROW)
  {
    lex.get_token(tk);
    // p=Ptree::Snoc(p, new LeafReserved(tk));

    if(lex.get_token(tk)!='(')
      return false;

    // p=Ptree::Snoc(p, new Leaf(tk));

    for(;;)
    {
      irept q;
      t=lex.LookAhead(0);
      if(t=='\0')
        return false;
      else if(t==')')
        break;
      else if(t==TOK_ELLIPSIS)
      {
        lex.get_token(tk);
      }
      else if(rName(q))
      {
        //  p=Ptree::Snoc(p, q);
      }
      else
        return false;

      if(lex.LookAhead(0)==',')
      {
        lex.get_token(tk);
        // p=Ptree::Snoc(p, new Leaf(tk));
      }
      else
        break;
    }

    if(lex.get_token(tk)!=')')
      return false;

    // p=Ptree::Snoc(p, new Leaf(tk));
  }
  else if(lex.LookAhead(0)==TOK_NOEXCEPT)
  {
    exprt expr;

    if(!rNoexceptExpr(expr))
      return false;

    // TODO
  }

  throw_decl=p;
  return true;
}

/*
  declarators : declarator.with.init (',' declarator.with.init)*

  is_statement changes the behavior of rArgDeclListOrInit().
*/
bool Parser::rDeclarators(
  cpp_declarationt::declaratorst &declarators,
  bool should_be_declarator,
  bool is_statement)
{
  cpp_tokent tk;

  for(;;)
  {
    cpp_declaratort declarator;
    if(!rDeclaratorWithInit(declarator, should_be_declarator, is_statement))
      return false;

    declarators.push_back(declarator);

    if(lex.LookAhead(0)==',')
      lex.get_token(tk);
    else
      return true;
  }
}

/*
  declarator.with.init
  : ':' expression
  | declarator
    {'=' initialize.expr |
     ':' expression}
*/
bool Parser::rDeclaratorWithInit(
  cpp_declaratort &dw,
  bool should_be_declarator,
  bool is_statement)
{
  if(lex.LookAhead(0)==':')
  {
    // This is an anonymous bit field.
    cpp_tokent tk;
    lex.get_token(tk); // get :

    exprt e;
    if(!rExpression(e, false))
      return false;

    typet bit_field_type(ID_c_bit_field);
    bit_field_type.set(ID_size, e);
    bit_field_type.subtype().make_nil();
    set_location(bit_field_type, tk);

    // merge_types(bit_field_type, declarator.type());

    return true;
  }
  else
  {
    cpp_declaratort declarator;

    if(!rDeclarator(
        declarator, kDeclarator, should_be_declarator, is_statement))
      return false;

    int t=lex.LookAhead(0);
    if(t=='=')
    {
      // initializer
      cpp_tokent tk;
      lex.get_token(tk);

      if(lex.LookAhead(0)==TOK_DEFAULT) // C++0x
      {
        if(!ansi_c_parser.cpp11)
        {
          SyntaxError();
          return false;
        }

        lex.get_token(tk);
        declarator.value()=codet(ID_default);
        set_location(declarator.value(), tk);
      }
      else if(lex.LookAhead(0)==TOK_DELETE) // C++0x
      {
        if(!ansi_c_parser.cpp11)
        {
          SyntaxError();
          return false;
        }

        lex.get_token(tk);
        declarator.value()=codet(ID_cpp_delete);
        set_location(declarator.value(), tk);
      }
      else
      {
        if(!rInitializeExpr(declarator.value()))
          return false;
      }
    }
    else if(t=='{')
    {
      // Possibly a C++11 list initializer;
      // or a function body.

      if(declarator.type().id()!=ID_function_type)
      {
        if(!rInitializeExpr(declarator.value()))
          return false;
      }
    }
    else if(t==':')
    {
      // bit field
      cpp_tokent tk;
      lex.get_token(tk); // get :

      exprt e;
      if(!rExpression(e, false))
        return false;

      typet bit_field_type(ID_c_bit_field);
      bit_field_type.set(ID_size, e);
      bit_field_type.subtype().make_nil();
      set_location(bit_field_type, tk);

      merge_types(bit_field_type, declarator.type());
    }

    dw.swap(declarator);
    return true;
  }
}

/* __stdcall, __fastcall, __clrcall, __cdecl

   These are Visual-Studio specific.

*/

bool Parser::rDeclaratorQualifier()
{
  int t=lex.LookAhead(0);

  // we just eat these

  while(t==TOK_STDCALL || t==TOK_FASTCALL || t==TOK_CLRCALL || t==TOK_CDECL)
  {
    cpp_tokent op;
    lex.get_token(op);
    t=lex.LookAhead(0);
  }

  return true;
}

/*
  declarator
  : (ptr.operator)* (name | '(' declarator ')')
        ('[' comma.expression ']')* {func.args.or.init}

  func.args.or.init
  : '(' arg.decl.list.or.init ')' {cv.qualify} {throw.decl}
  {member.initializers}

  Note: We assume that '(' declarator ')' is followed by '(' or '['.
        This is to avoid accepting a function call F(x) as a pair of
        a type F and a declarator x.  This assumption is ignored
        if should_be_declarator is true.

  Note: is_statement changes the behavior of rArgDeclListOrInit().
*/

bool Parser::rDeclarator(
  cpp_declaratort &declarator,
  DeclKind kind,
  bool should_be_declarator,
  bool is_statement)
{
  int t;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 1\n";
  #endif

  // we can have one or more declarator qualifiers
  if(!rDeclaratorQualifier())
    return false;

  typet d_outer, d_inner;
  irept name;

  name.make_nil();
  d_outer.make_nil();
  d_inner.make_nil();

  if(!optPtrOperator(d_outer))
    return false;

  // we can have another sequence of declarator qualifiers
  if(!rDeclaratorQualifier())
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 2\n";
  #endif

  t=lex.LookAhead(0);

  if(t=='(')
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 3\n";
    #endif

    cpp_tokent op;
    lex.get_token(op);

    cpp_declaratort declarator2;
    if(!rDeclarator(declarator2, kind, true, false))
      return false;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 4\n";
    #endif

    cpp_tokent cp;

    if(lex.get_token(cp)!=')')
      return false;

    if(!should_be_declarator)
    {
      if((kind==kDeclarator || kind==kCastDeclarator) && d_outer.is_nil())
      {
        t=lex.LookAhead(0);
        if(t!='[' && t!='(')
          return false;
      }
    }

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 5\n";
    #endif

    d_inner.swap(declarator2.type());
    name.swap(declarator2.name());
  }
  else if(kind!=kCastDeclarator &&
          (kind==kDeclarator || t==TOK_IDENTIFIER || t==TOK_SCOPE))
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 6\n";
    #endif

    // if this is an argument declarator, "int (*)()" is valid.
    if(!rName(name))
      return false;
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 7\n";
  #endif

  exprt init_args(static_cast<const exprt &>(get_nil_irep()));
  // const...
  typet method_qualifier(static_cast<const typet &>(get_nil_irep()));

  for(;;)
  {
    t=lex.LookAhead(0);
    if(t=='(') // function
    {
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 8\n";
      #endif

      cpp_tokent op, cp;
      exprt args;
      bool is_args=true;

      lex.get_token(op);

      if(lex.LookAhead(0)==')')
        args.clear();
      else
        if(!rArgDeclListOrInit(args, is_args, is_statement))
          return false;

      if(lex.get_token(cp)!=')')
        return false;

      if(is_args)
      {
        typet function_type(ID_function_type);
        function_type.subtype().swap(d_outer);
        function_type.add(ID_parameters).swap(args);

        // make this subtype of d_inner
        make_subtype(function_type, d_inner);
        d_outer.swap(d_inner);

        optCvQualify(method_qualifier);
      }
      else
      {
        init_args.swap(args);
        // loop should end here
      }

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 9\n";
      #endif

      irept throw_decl;
      optThrowDecl(throw_decl); // ignore in this version

      if(lex.LookAhead(0)==TOK_ARROW)
      {
        #ifdef DEBUG
        std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 10\n";
        #endif

        // C++11 trailing return type, but we already have
        // a return type. We should report this as an error.
        cpp_tokent arrow;
        lex.get_token(arrow);

        typet return_type;
        if(!rTypeSpecifier(return_type, false))
          return false;

        if(d_outer.subtype().is_not_nil())
          return false;

        d_outer.subtype().swap(return_type);
      }

      if(lex.LookAhead(0)==':')
      {
        #ifdef DEBUG
        std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 11\n";
        #endif

        irept mi;
        if(rMemberInitializers(mi))
        {
          // TODO: these are only meant to show up in a
          // constructor!
        }
        else
          return false;
      }

      break;                // "T f(int)(char)" is invalid.
    }
    else if(t=='[')         // array
    {
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 12\n";
      #endif

      cpp_tokent ob, cb;
      exprt expr;
      lex.get_token(ob);
      if(lex.LookAhead(0)==']')
        expr.make_nil();
      else
        if(!rCommaExpression(expr))
          return false;

      if(lex.get_token(cb)!=']')
        return false;

      std::list<typet> tl;
      tl.push_back(d_outer);
      while(tl.back().id() == ID_array)
      {
        tl.push_back(tl.back().subtype());
      }

      array_typet array_type(tl.back(), expr);
      tl.pop_back();
      d_outer.swap(array_type);
      while(!tl.empty())
      {
        tl.back().subtype().swap(d_outer);
        d_outer.swap(tl.back());
        tl.pop_back();
      }
    }
    else
      break;
  }

  optCvQualify(d_outer);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 13\n";
  #endif

  declarator=cpp_declaratort();

  declarator.name().swap(name);

  if(init_args.is_not_nil())
    declarator.init_args().swap(init_args);

  if(method_qualifier.is_not_nil())
    declarator.method_qualifier().swap(method_qualifier);

  declarator.type().swap(d_outer);

  return true;
}

/*
  ptr.operator
  : (('*' | ptr.to.member)['&'] {cv.qualify})+
*/
bool Parser::optPtrOperator(typet &ptrs)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::optPtrOperator 1\n";
  #endif // DEBUG

  std::list<typet> t_list;

  for(;;)
  {
    int t=lex.LookAhead(0);

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::optPtrOperator 2 "
              << t << "\n";
    #endif

    if(t=='*')
    {
      typet op(ID_frontend_pointer); // width gets set during conversion
      cpp_tokent tk;
      lex.get_token(tk);
      set_location(op, tk);

      typet cv;
      cv.make_nil();
      optCvQualify(cv); // the qualifier is for the pointer
      if(cv.is_not_nil())
        merge_types(cv, op);

      t_list.push_back(op);
    }
    else if(t=='^')
    {
      // this is an Apple extension called 'block pointer' or 'closure pointer'
      typet op(ID_block_pointer);
      cpp_tokent tk;
      lex.get_token(tk);
      set_location(op, tk);

      typet cv;
      cv.make_nil();
      optCvQualify(cv); // the qualifier is for the pointer
      if(cv.is_not_nil())
        merge_types(cv, op);

      t_list.push_back(op);
    }
    else if(isPtrToMember(0))
    {
      typet op;
      if(!rPtrToMember(op))
        return false;

      typet cv;
      cv.make_nil();
      optCvQualify(cv); // the qualifier is for the pointer
      if(cv.is_not_nil())
      {
        merge_types(op, cv);
        t_list.push_back(cv);
      }
      else
        t_list.push_back(op);
    }
    else
      break;
  }

  {
    int t=lex.LookAhead(0);

    if(t=='&')
    {
      cpp_tokent tk;
      lex.get_token(tk);
      typet op(ID_frontend_pointer); // width gets set during conversion
      op.set(ID_C_reference, true);
      set_location(op, tk);
      t_list.push_front(op);
    }
    else if(t==TOK_ANDAND) // &&, these are C++0x rvalue refs
    {
      cpp_tokent tk;
      lex.get_token(tk);
      typet op(ID_frontend_pointer); // width gets set during conversion
      op.set(ID_C_rvalue_reference, true);
      set_location(op, tk);
      t_list.push_front(op);
    }
  }

  for(std::list<typet>::reverse_iterator
      it=t_list.rbegin();
      it!=t_list.rend();
      it++)
  {
    if(it->id()==ID_merged_type)
    {
      auto &merged_type = to_merged_type(*it);
      merged_type.last_type().subtype().swap(ptrs);
    }
    else
    {
      assert(it->is_not_nil());
      it->subtype().swap(ptrs);
    }

    ptrs.swap(*it);
  }

  return true;
}

/*
  member.initializers
  : ':' member.init (',' member.init)*
*/
bool Parser::rMemberInitializers(irept &init)
{
  cpp_tokent tk;

  if(lex.get_token(tk)!=':')
    return false;

  init=irept(ID_member_initializers);
  set_location(init, tk);

  exprt m;
  if(!rMemberInit(m))
    return false;

  init.move_to_sub(m);

  while(lex.LookAhead(0)==',')
  {
    lex.get_token(tk);
    if(!rMemberInit(m))
      return false;

    init.move_to_sub(m);
  }

  return true;
}

/*
  member.init
  : name '(' function.arguments ')'
  : name '(' '{' initialize.expr ... '}' ')'
*/
bool Parser::rMemberInit(exprt &init)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rMemberInit 1\n";
  #endif

  irept name;

  if(!rName(name))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rMemberInit 2\n";
  #endif

  init=codet(ID_member_initializer);
  init.add(ID_member).swap(name);

  cpp_tokent tk1, tk2;
  lex.get_token(tk1);
  set_location(init, tk1);

  if(tk1.kind=='{' ||
     (tk1.kind=='(' && lex.LookAhead(0)=='{'))
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rMemberInit 3\n";
    #endif
    exprt exp;
    if(!rInitializeExpr(exp))
      return false;

    init.operands().push_back(exp);

    // read closing parenthesis
    lex.get_token(tk2);
    if(tk2.kind!='}' && tk2.kind!=')')
      return false;
  }
  else
  {
    if(tk1.kind!='(')
      return false;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rMemberInit 4\n";
    #endif

    exprt args;

    if(!rFunctionArguments(args))
      return false;

    init.operands().swap(args.operands());

    // read closing parenthesis
    if(lex.get_token(tk2)!=')')
      return false;
  }

  if(lex.LookAhead(0)==TOK_ELLIPSIS)
  {
    lex.get_token();

    // TODO
  }

  return true;
}

/*
  name : {'::'} name2 ('::' name2)*

  name2
  : Identifier {template.args}
  | '~' Identifier
  | OPERATOR operator.name {template.args}

  Don't use this function for parsing an expression
  It always regards '<' as the beginning of template arguments.
*/
bool Parser::rName(irept &name)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rName 0\n";
  #endif

  name=cpp_namet();
  irept::subt &components=name.get_sub();

  if(lex.LookAhead(0)==TOK_TYPENAME)
  {
    cpp_tokent tk;
    lex.get_token(tk);
    name.set(ID_typename, true);
  }

  {
    cpp_tokent tk;
    lex.LookAhead(0, tk);
    set_location(name, tk);
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rName 1\n";
  #endif

  for(;;)
  {
    cpp_tokent tk;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rName 2 "
              << lex.LookAhead(0) << "\n";
    #endif

    switch(lex.LookAhead(0))
    {
    case TOK_TEMPLATE:
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rName 3\n";
      #endif
      lex.get_token(tk);
      // Skip template token, next will be identifier
      if(lex.LookAhead(0)!=TOK_IDENTIFIER)
        return false;
      break;

    case '<':
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rName 4\n";
      #endif
      {
        irept args;
        if(!rTemplateArgs(args))
          return false;

        components.push_back(irept(ID_template_args));
        components.back().add(ID_arguments).swap(args);

        // done unless scope is next
        if(lex.LookAhead(0)!=TOK_SCOPE)
          return true;
      }
      break;

    case TOK_IDENTIFIER:
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rName 5\n";
      #endif
      lex.get_token(tk);
      components.push_back(cpp_namet::namet(tk.data.get(ID_C_base_name)));
      set_location(components.back(), tk);

      {
        int t=lex.LookAhead(0);
        // done unless scope or template args is next
        if(t!=TOK_SCOPE && t!='<')
          return true;
      }
      break;

    case TOK_SCOPE:
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rName 6\n";
      #endif
      lex.get_token(tk);
      components.push_back(irept("::"));
      set_location(components.back(), tk);
      break;

    case '~':
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rName 7\n";
      #endif
      lex.get_token(tk);

      // identifier must be next
      if(lex.LookAhead(0)!=TOK_IDENTIFIER)
        return false;

      components.push_back(irept("~"));
      set_location(components.back(), tk);
      break;

    case TOK_OPERATOR:
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rName 8\n";
      #endif
      lex.get_token(tk);
      {
        components.push_back(irept(ID_operator));
        set_location(components.back(), tk);

        components.push_back(irept());

        if(!rOperatorName(components.back()))
          return false;
      }

      // done unless template args are next
      if(lex.LookAhead(0)!='<')
        return true;
      break;

    default:
      return false;
    }
  }
}

/*
  operator.name
  : '+' | '-' | '*' | '/' | '%' | '^' | '&' | '|' | '~'
  | '!' | '=' | '<' | '>' | AssignOp | ShiftOp | EqualOp
  | RelOp | LogAndOp | LogOrOp | IncOp | ',' | DOTPM | ARROWPM | ArrowOp
  | NEW {'[' ']'}
  | DELETE {'[' ']'}
  | '(' ')'
  | '[' ']'
  | cast.operator.name
*/

bool Parser::rOperatorName(irept &name)
{
  cpp_tokent tk;

  int t=lex.LookAhead(0);

  irep_idt operator_id;

  switch(t)
  {
  case '+':
  case '-':
  case '*':
  case '/':
  case '%':
  case '^':
  case '&':
  case '|':
  case '~':
  case '!':
  case '=':
  case '<':
  case '>':
  case ',':
    operator_id = std::string(1, static_cast<char>(t));
    break;

  case TOK_MULTASSIGN: operator_id="*="; break;
  case TOK_DIVASSIGN: operator_id="/="; break;
  case TOK_MODASSIGN: operator_id="%="; break;
  case TOK_PLUSASSIGN: operator_id="+="; break;
  case TOK_MINUSASSIGN: operator_id="-="; break;
  case TOK_SHLASSIGN: operator_id="<<="; break;
  case TOK_SHRASSIGN: operator_id=">>="; break;
  case TOK_ANDASSIGN: operator_id="&="; break;
  case TOK_XORASSIGN: operator_id="^="; break;
  case TOK_ORASSIGN: operator_id="|="; break;
  case TOK_SHIFTLEFT: operator_id="<<"; break;
  case TOK_SHIFTRIGHT: operator_id=">>"; break;
  case TOK_EQ: operator_id="=="; break;
  case TOK_NE: operator_id="!="; break;
  case TOK_LE: operator_id="<="; break;
  case TOK_GE: operator_id=">="; break;
  case TOK_ANDAND: operator_id="&&"; break;
  case TOK_OROR: operator_id="||"; break;
  case TOK_INCR: operator_id="++"; break;
  case TOK_DECR: operator_id="--"; break;
  case TOK_DOTPM: operator_id=".*"; break;
  case TOK_ARROWPM: operator_id="->*"; break;
  case TOK_ARROW: operator_id="->"; break;

  case TOK_NEW:
  case TOK_DELETE:
    {
      lex.get_token(tk);

      if(lex.LookAhead(0)!='[')
      {
        name=irept(t==TOK_NEW?ID_cpp_new:ID_cpp_delete);
        set_location(name, tk);
      }
      else
      {
        name=irept(t==TOK_NEW?ID_cpp_new_array:ID_cpp_delete_array);
        set_location(name, tk);

        lex.get_token(tk);

        if(lex.get_token(tk)!=']')
          return false;
      }
    }
    return true;

  case '(':
    lex.get_token(tk);
    name=irept("()");
    set_location(name, tk);
    return lex.get_token(tk)==')';

  case '[':
    lex.get_token(tk);
    name=irept("[]");
    set_location(name, tk);
    return lex.get_token(tk)==']';

  default:
    return rCastOperatorName(name);
  }

  assert(!operator_id.empty());
  lex.get_token(tk);
  name=irept(operator_id);
  set_location(name, tk);

  return true;
}

/*
  cast.operator.name
  : {cv.qualify} (integral.or.class.spec | name) {cv.qualify}
    {(ptr.operator)*}
*/

bool Parser::rCastOperatorName(irept &name)
{
  typet cv1, cv2, type_name, ptr;

  cv1.make_nil();
  cv2.make_nil();
  type_name.make_nil();
  ptr.make_nil();

  if(!optCvQualify(cv1))
    return false;

  if(!optIntegralTypeOrClassSpec(type_name))
    return false;

  if(type_name.is_nil())
  {
    if(!rName(type_name))
      return false;
  }

  merge_types(cv1, type_name);

  if(!optCvQualify(cv2))
    return false;

  if(!optPtrOperator(ptr))
    return false;

  make_subtype(type_name, ptr);
  merge_types(cv2, ptr);
  name = ptr;

  return true;
}

/*
  ptr.to.member
  : {'::'} (identifier {template.args} '::')+ '*'
*/
bool Parser::rPtrToMember(irept &ptr_to_mem)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rPtrToMember 0\n";
  #endif

  typet ptm(ID_frontend_pointer); // width gets set during conversion
  irept &name = ptm.add("to-member");
  name=cpp_namet();
  irept::subt &components=name.get_sub();

  {
    cpp_tokent tk;
    lex.LookAhead(0, tk);
    set_location(name, tk);
  }

  bool loop_cond = true;
  while(loop_cond)
  {
    cpp_tokent tk;

    switch(lex.LookAhead(0))
    {
    case TOK_TEMPLATE:
      lex.get_token(tk);
      // Skip template token, next will be identifier
      if(lex.LookAhead(0)!=TOK_IDENTIFIER)
        return false;
      break;

    case '<':
      {
        irept args;
        if(!rTemplateArgs(args))
          return false;

        components.push_back(irept(ID_template_args));
        components.back().add(ID_arguments).swap(args);

        if(lex.LookAhead(0)!=TOK_SCOPE)
          return false;
      }
      break;

    case TOK_IDENTIFIER:
      lex.get_token(tk);
      components.push_back(cpp_namet::namet(tk.data.get(ID_C_base_name)));
      set_location(components.back(), tk);

      {
        int t=lex.LookAhead(0);
        if(t!=TOK_SCOPE && t!='<')
          return false;
      }
      break;

    case TOK_SCOPE:
      lex.get_token(tk);
      components.push_back(irept("::"));
      set_location(components.back(), tk);

      // done if next token is '*'
      if(lex.LookAhead(0) == '*')
      {
        lex.get_token(tk);
        ptr_to_mem.swap(ptm);


        #ifdef DEBUG
        std::cout << std::string(__indent, ' ') << "Parser::rPtrToMember 1\n";
        #endif

        return true;
      }

      if(lex.LookAhead(0) != TOK_IDENTIFIER)
        return false;

      break;

    default:
      return false;
    }
  }
  return false;
}

/*
  template.args
  : '<' '>'
  | '<' template.argument {',' template.argument} '>'

  template.argument
  : type.name
  | logical.or.expr
*/
bool Parser::rTemplateArgs(irept &template_args)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rTemplateArgs 0\n";
  #endif

  cpp_tokent tk1;

  if(lex.get_token(tk1)!='<')
    return false;

  set_location(template_args, tk1);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') <<  "Parser::rTemplateArgs 1\n";
  #endif

  // in case of Foo<>
  if(lex.LookAhead(0)=='>')
  {
    cpp_tokent tk2;
    lex.get_token(tk2);
    return true;
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') <<  "Parser::rTemplateArgs 2\n";
  #endif

  for(;;)
  {
    exprt exp;
    cpp_token_buffert::post pos=lex.Save();

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') <<  "Parser::rTemplateArgs 3\n";
    #endif

    typet a;

    // try type name first
    if(rTypeNameOrFunctionType(a) &&
       ((lex.LookAhead(0) == '>' || lex.LookAhead(0) == ',' ||
         lex.LookAhead(0)==TOK_SHIFTRIGHT) ||
        (lex.LookAhead(0)==TOK_ELLIPSIS &&
         (lex.LookAhead(1) == '>' ||
          lex.LookAhead(1)==TOK_SHIFTRIGHT)))
        )
    {
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') <<  "Parser::rTemplateArgs 4\n";
      #endif

      // ok
      exp=exprt(ID_type);
      exp.add_source_location()=a.source_location();
      exp.type().swap(a);

      // but could also be an expr
      lex.Restore(pos);
      exprt tmp;
      if(rConditionalExpr(tmp, true))
        exp.id(ID_ambiguous);
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') <<  "Parser::rTemplateArgs 4.1\n";
      #endif
      lex.Restore(pos);
      rTypeNameOrFunctionType(a);

      if(lex.LookAhead(0)==TOK_ELLIPSIS)
      {
        lex.get_token(tk1);

        // TODO
      }
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') <<  "Parser::rTemplateArgs 4.2\n";
      #endif
    }
    else
    {
      // parsing failed, try expression
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') <<  "Parser::rTemplateArgs 5\n";
      #endif

      lex.Restore(pos);


      if(!rConditionalExpr(exp, true))
        return false;

      if(lex.LookAhead(0)==TOK_ELLIPSIS)
      {
        lex.get_token(tk1);

        // TODO
      }
    }

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') <<  "Parser::rTemplateArgs 6\n";
    #endif

    template_args.get_sub().push_back(irept(irep_idt()));
    template_args.get_sub().back().swap(exp);

    pos=lex.Save();
    cpp_tokent tk2;
    switch(lex.get_token(tk2))
    {
    case '>':
      return true;

    case ',':
      break;

    case TOK_SHIFTRIGHT: // turn >> into > >
      lex.Restore(pos);
      tk2.kind='>';
      tk2.text='>';
      lex.Replace(tk2);
      lex.Insert(tk2);
      assert(lex.LookAhead(0)=='>');
      assert(lex.LookAhead(1)=='>');
      return true;

    default:
      return false;
    }
  }
}

/*
  arg.decl.list.or.init
    : arg.decl.list
    | function.arguments

  This rule accepts function.arguments to parse declarations like:
        Point p(1, 3);
  "(1, 3)" is arg.decl.list.or.init.

  If maybe_init is true, we first examine whether tokens construct
  function.arguments.  This ordering is significant if tokens are
        Point p(s, t);
  s and t can be type names or variable names.
*/
bool Parser::rArgDeclListOrInit(
  exprt &arglist,
  bool &is_args,
  bool maybe_init)
{
  cpp_token_buffert::post pos=lex.Save();
  if(maybe_init)
  {
    if(rFunctionArguments(arglist))
      if(lex.LookAhead(0)==')')
      {
        is_args=false;
        // encode.Clear();
        return true;
      }

    lex.Restore(pos);
    return(is_args=rArgDeclList(arglist));
  }
  else
  {
    is_args = rArgDeclList(arglist);

    if(is_args)
      return true;
    else
    {
      lex.Restore(pos);
      // encode.Clear();
      return rFunctionArguments(arglist);
    }
  }
}

/*
  arg.decl.list
    : empty
    | arg.declaration ( ',' arg.declaration )* {{ ',' } Ellipses}
*/
bool Parser::rArgDeclList(irept &arglist)
{
  irept list;

  list.clear();
  for(;;)
  {
    cpp_declarationt declaration;

    int t=lex.LookAhead(0);
    if(t==')')
      break;
    else if(t==TOK_ELLIPSIS)
    {
      cpp_tokent tk;
      lex.get_token(tk);
      list.get_sub().push_back(irept(ID_ellipsis));
      break;
    }
    else if(rArgDeclaration(declaration))
    {
      cpp_tokent tk;

      list.get_sub().push_back(irept(irep_idt()));
      list.get_sub().back().swap(declaration);
      t=lex.LookAhead(0);
      if(t==',')
        lex.get_token(tk);
      else if(t==TOK_ELLIPSIS)
      {
        lex.get_token(tk);
        list.get_sub().push_back(irept(ID_ellipsis));
      }
      else if(t!=')' && t!=TOK_ELLIPSIS)
        return false;
    }
    else
    {
      arglist.clear();
      return false;
    }
  }

  arglist.swap(list);

  return true;
}

/*
  arg.declaration
    : {userdef.keyword | REGISTER} type.specifier arg.declarator
      {'=' expression}
*/
bool Parser::rArgDeclaration(cpp_declarationt &declaration)
{
  typet header;
  cpp_tokent tk;

  switch(lex.LookAhead(0))
  {
  case TOK_REGISTER:
    lex.get_token(tk);
    header=typet(ID_register);
    break;

  default:
    header.make_nil();
    break;
  }

  if(!rTypeSpecifier(declaration.type(), true))
    return false;

  cpp_declaratort arg_declarator;

  if(!rDeclarator(arg_declarator, kArgDeclarator, true, false))
    return false;

  declaration.declarators().push_back(arg_declarator);

  int t=lex.LookAhead(0);
  if(t=='=')
  {
    lex.get_token(tk);
    if(!rInitializeExpr(declaration.declarators().back().value()))
       return false;
  }

  return true;
}

/*
  initialize.expr
  : expression
  | '{' initialize.expr (',' initialize.expr)* {','} '}'
*/
bool Parser::rInitializeExpr(exprt &expr)
{
  if(lex.LookAhead(0)!='{')
    return rExpression(expr, false);

  // we want { initialize_expr, ... }

  cpp_tokent tk;
  lex.get_token(tk);

  exprt e;

  expr.id(ID_initializer_list);
  set_location(expr, tk);

  int t=lex.LookAhead(0);

  while(t!='}')
  {
    exprt tmp;

    if(t==TOK_MSC_IF_EXISTS ||
       t==TOK_MSC_IF_NOT_EXISTS)
    {
      // TODO
      cpp_tokent tk;
      exprt name;
      lex.get_token(tk);
      if(lex.get_token(tk)!='(')
        return false;
      if(!rVarName(name))
        return false;
      if(lex.get_token(tk)!=')')
        return false;
      if(lex.get_token(tk)!='{')
        return false;
      if(!rInitializeExpr(name))
        return false;
      if(lex.LookAhead(0)==',')
        lex.get_token(tk);
      if(lex.get_token(tk)!='}')
        return false;
    }

    if(!rInitializeExpr(tmp))
    {
      if(!SyntaxError())
        return false;        // too many errors

      SkipTo('}');
      lex.get_token(tk);
      return true;           // error recovery
    }

    expr.move_to_operands(tmp);

    t=lex.LookAhead(0);
    if(t=='}')
    {
      // done!
    }
    else if(t==',')
    {
      lex.get_token(tk);
      t=lex.LookAhead(0);
    }
    else
    {
      if(!SyntaxError())
        return false;        // too many errors

      SkipTo('}');
      lex.get_token(tk);
      return true;           // error recovery
    }
  }

  lex.get_token(tk);

  return true;
}

/*
  function.arguments
  : empty
  | expression (',' expression)*

  This assumes that the next token following function.arguments is ')'.
*/
bool Parser::rFunctionArguments(exprt &args)
{
  exprt exp;
  cpp_tokent tk;

  args=exprt(irep_idt());
  if(lex.LookAhead(0)==')')
    return true;

  for(;;)
  {
    if(!rExpression(exp, false))
      return false;

    args.move_to_operands(exp);

    if(lex.LookAhead(0)==TOK_ELLIPSIS &&
       (lex.LookAhead(1)==')' || lex.LookAhead(1)==','))
    {
      lex.get_token(tk);
      // TODO

      if(lex.LookAhead(0)==')')
        return true;
      lex.get_token();
    }
    else if(lex.LookAhead(0)!=',')
      return true;
    else
      lex.get_token(tk);
  }
}

/*
  enum.spec
  : ENUM Identifier
  | ENUM {Identifier} '{' {enum.body} '}'
  | ENUM CLASS Identifier '{' {enum.body} '}'
  | ENUM CLASS Identifier ':' Type '{' {enum.body} '}'
*/
bool Parser::rEnumSpec(typet &spec)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rEnumSpec 1\n";
  #endif

  cpp_tokent tk;

  if(lex.get_token(tk)!=TOK_ENUM)
    return false;

  spec=cpp_enum_typet();
  set_location(spec, tk);

  spec.subtype().make_nil();

  // C++11 enum classes
  if(lex.LookAhead(0)==TOK_CLASS)
  {
    lex.get_token(tk);
    spec.set(ID_C_class, true);
  }

  if(lex.LookAhead(0)!='{' &&
     lex.LookAhead(0)!=':')
  {
    // Visual Studio allows full names for the tag,
    // not just an identifier
    irept name;

    if(!rName(name))
      return false;

    spec.add(ID_tag).swap(name);
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rEnumSpec 2\n";
  #endif

  // C++11 enums have an optional underlying type
  if(lex.LookAhead(0)==':')
  {
    lex.get_token(tk); // read the colon
    if(!rTypeName(spec.subtype()))
      return false;
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rEnumSpec 3\n";
  #endif

  if(lex.LookAhead(0)!='{')
    return true; // ok, no body

  lex.get_token(tk);

  if(lex.LookAhead(0)=='}')
  {
    // there is still a body, just an empty one!
    spec.add(ID_body);
  }
  else
    if(!rEnumBody(spec.add(ID_body)))
      return false;

  // there must be closing '}'

  if(lex.get_token(tk)!='}')
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rEnumSpec 4\n";
  #endif

  return true;
}

/*
  enum.body
  : Identifier {'=' expression} (',' Identifier {'=' expression})* {','}
*/
bool Parser::rEnumBody(irept &body)
{
  body.clear();

  for(;;)
  {
    cpp_tokent tk, tk2;

    if(lex.LookAhead(0)=='}')
      return true;

    if(lex.get_token(tk)!=TOK_IDENTIFIER)
      return false;

    body.get_sub().push_back(irept());
    irept &n=body.get_sub().back();
    set_location(n, tk);
    n.set(ID_name, tk.data.get(ID_C_base_name));

    if(lex.LookAhead(0, tk2)=='=') // set the constant
    {
      lex.get_token(tk2); // read the '='

      exprt exp;

      if(!rExpression(exp, false))
      {
        if(!SyntaxError())
          return false;        // too many errors

        SkipTo('}');
        body.clear();          // empty
        return true;           // error recovery
      }

      n.add(ID_value).swap(exp);
    }
    else
      n.add(ID_value).make_nil();

    if(lex.LookAhead(0)!=',')
      return true;

    lex.get_token(tk);
  }
}

/*
  class.spec
  : {userdef.keyword} class.key class.body
  | {userdef.keyword} class.key name {class.body}
  | {userdef.keyword} class.key name ':' base.specifiers class.body

  class.key
  : CLASS | STRUCT | UNION | INTERFACE
*/
bool Parser::rClassSpec(typet &spec)
{
  cpp_tokent tk;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rClassSpec 1\n";
  #endif

  int t=lex.get_token(tk);
  if(t!=TOK_CLASS && t!=TOK_STRUCT &&
     t!=TOK_UNION && t!=TOK_INTERFACE)
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rClassSpec 2\n";
  #endif

  if(t==TOK_CLASS)
  {
    spec=typet(ID_struct);
    spec.set(ID_C_class, true);
  }
  else if(t==TOK_INTERFACE) // MS-specific
  {
    spec=typet(ID_struct);
    spec.set(ID_C_interface, true);
  }
  else if(t==TOK_STRUCT)
    spec=typet(ID_struct);
  else if(t==TOK_UNION)
    spec=typet(ID_union);
  else
    UNREACHABLE;

  set_location(spec, tk);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rClassSpec 3\n";
  #endif

  if(lex.LookAhead(0)=='{')
  {
    // no tag
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rClassSpec 4\n";
    #endif
  }
  else
  {
    if(!optAlignas(spec))
      return false;

    if(lex.LookAhead(0)==TOK_GCC_ATTRIBUTE)
    {
      cpp_tokent tk;
      lex.get_token(tk);

      if(!rAttribute(spec))
        return false;
    }

    irept name;

    if(!rName(name))
      return false;

    spec.add(ID_tag).swap(name);

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rClassSpec 5\n";
    #endif

    t=lex.LookAhead(0);

    if(t==':')
    {
      if(!rBaseSpecifiers(spec.add(ID_bases)))
        return false;
    }
    else if(t=='{')
    {
    }
    else
    {
      return true;
    }
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rClassSpec 6\n";
  #endif

  save_scopet saved_scope(current_scope);
  make_sub_scope(spec.find(ID_tag), new_scopet::kindt::TAG);

  exprt body;

  if(!rClassBody(body))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rClassSpec 7\n";
  #endif

  ((exprt&)spec.add(ID_body)).operands().swap(body.operands());
  return true;
}

/*
  base.specifiers
  : ':' base.specifier (',' base.specifier)*

  base.specifier
  : {{VIRTUAL} (PUBLIC | PROTECTED | PRIVATE) {VIRTUAL}} name
*/
bool Parser::rBaseSpecifiers(irept &bases)
{
  cpp_tokent tk;

  if(lex.get_token(tk)!=':')
    return false;

  for(;;)
  {
    int t=lex.LookAhead(0);
    irept base(ID_base);

    if(t==TOK_VIRTUAL)
    {
      lex.get_token(tk);
      base.set(ID_virtual, true);
      t=lex.LookAhead(0);
    }

    if(t==TOK_PUBLIC || t==TOK_PROTECTED || t==TOK_PRIVATE)
    {
      switch(lex.get_token(tk))
      {
       case TOK_PUBLIC:
        base.set(ID_protection, ID_public);
        break;

       case TOK_PROTECTED:
        base.set(ID_protection, ID_protected);
        break;

       case TOK_PRIVATE:
        base.set(ID_protection, ID_private);
        break;

       default:
        UNREACHABLE;
      }

      t=lex.LookAhead(0);
    }

    if(t==TOK_VIRTUAL)
    {
      lex.get_token(tk);
      base.set(ID_virtual, true);
    }

    if(!rName(base.add(ID_name)))
      return false;

    if(lex.LookAhead(0)==TOK_ELLIPSIS)
    {
      lex.get_token();

      // TODO
    }

    bases.get_sub().push_back(irept());
    bases.get_sub().back().swap(base);

    if(lex.LookAhead(0)!=',')
      return true;
    else
      lex.get_token(tk);
  }
}

/*
  class.body : '{' (class.members)* '}'
*/
bool Parser::rClassBody(exprt &body)
{
  cpp_tokent tk;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rClassBody 0\n";
  #endif

  if(lex.get_token(tk)!='{')
    return false;

  exprt members=exprt("cpp-class-body");

  set_location(members, tk);

  while(lex.LookAhead(0)!='}')
  {
    cpp_itemt member;

    if(!rClassMember(member))
    {
      if(!SyntaxError())
        return false;        // too many errors

      SkipTo('}');
      lex.get_token(tk);
      // body=Ptree::List(ob, nil, new Leaf(tk));
      return true;        // error recovery
    }
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rClassBody "
              << member.pretty() << '\n';
    #endif

    members.move_to_operands(
      static_cast<exprt &>(static_cast<irept &>(member)));
  }

  lex.get_token(tk);
  body.swap(members);
  return true;
}

/*
  class.member
  : (PUBLIC | PROTECTED | PRIVATE) ':'
  | user.access.spec
  | ';'
  | type.def
  | template.decl
  | using.declaration
  | metaclass.decl
  | declaration
  | access.decl
  | static_assert

  Note: if you modify this function, see ClassWalker::TranslateClassSpec()
  as well.
*/
bool Parser::rClassMember(cpp_itemt &member)
{
  cpp_tokent tk1, tk2;

  int t=lex.LookAhead(0);

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rClassMember 0 " << t
            << '\n';
  #endif // DEBUG

  if(t==TOK_PUBLIC || t==TOK_PROTECTED || t==TOK_PRIVATE)
  {
    switch(lex.get_token(tk1))
    {
    case TOK_PUBLIC:
      member.id("cpp-public");
      break;

    case TOK_PROTECTED:
      member.id("cpp-protected");
      break;

    case TOK_PRIVATE:
      member.id("cpp-private");
      break;

    default:
      UNREACHABLE;
    }

    set_location(member, tk1);

    if(lex.get_token(tk2)!=':')
      return false;

    return true;
  }
  else if(t==';')
    return rNullDeclaration(member.make_declaration());
  else if(t==TOK_TYPEDEF)
    return rTypedef(member.make_declaration());
  else if(t==TOK_TEMPLATE)
    return rTemplateDecl(member.make_declaration());
  else if(t==TOK_USING &&
          lex.LookAhead(1)==TOK_IDENTIFIER &&
          lex.LookAhead(2)=='=')
    return rTypedefUsing(member.make_declaration());
  else if(t==TOK_USING)
    return rUsing(member.make_using());
  else if(t==TOK_STATIC_ASSERT)
    return rStaticAssert(member.make_static_assert());
  else
  {
    cpp_token_buffert::post pos=lex.Save();
    if(rDeclaration(member.make_declaration()))
      return true;

    lex.Restore(pos);
    return rAccessDecl(member.make_declaration());
  }
}

/*
  access.decl
  : name ';'                e.g. <qualified class>::<member name>;
*/
bool Parser::rAccessDecl(cpp_declarationt &mem)
{
  cpp_namet name;
  cpp_tokent tk;

  if(!rName(name))
    return false;

  if(lex.get_token(tk)!=';')
    return false;

  cpp_declaratort name_decl;
  name_decl.name() = name;
  mem.declarators().push_back(name_decl);

  // mem=new PtreeAccessDecl(new PtreeName(name, encode),
  //                           Ptree::List(new Leaf(tk)));
  return true;
}

/*
  comma.expression
  : expression
  | comma.expression ',' expression        (left-to-right)
*/
bool Parser::rCommaExpression(exprt &exp)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rCommaExpression 0\n";
  #endif

  if(!rExpression(exp, false))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rCommaExpression 1\n";
  #endif

  while(lex.LookAhead(0)==',')
  {
    cpp_tokent tk;

    lex.get_token(tk);

    exprt right;
    if(!rExpression(right, false))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt(ID_comma);
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rCommaExpression 2\n";
  #endif

  return true;
}

/*
  expression
  : conditional.expr {(AssignOp | '=') expression}        right-to-left
*/
bool Parser::rExpression(exprt &exp, bool template_args)
{
  cpp_tokent tk;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rExpression 0\n";
  #endif

  if(!rConditionalExpr(exp, template_args))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rExpression 1\n";
  #endif

  int t=lex.LookAhead(0);

  if(t=='=' ||
     t==TOK_MULTASSIGN || t==TOK_DIVASSIGN || t==TOK_MODASSIGN ||
     t==TOK_PLUSASSIGN || t==TOK_MINUSASSIGN || t==TOK_SHLASSIGN ||
     t==TOK_SHRASSIGN  || t==TOK_ANDASSIGN ||
     t==TOK_XORASSIGN  || t==TOK_ORASSIGN)
  {
    lex.get_token(tk);

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rExpression 2\n";
    #endif

    exprt right;
    if(!rExpression(right, template_args))
      return false;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rExpression 3\n";
    #endif

    exprt left;
    left.swap(exp);

    exp=exprt(ID_side_effect);

    if(t=='=')
      exp.set(ID_statement, ID_assign);
    else if(t==TOK_PLUSASSIGN)
      exp.set(ID_statement, ID_assign_plus);
    else if(t==TOK_MINUSASSIGN)
      exp.set(ID_statement, ID_assign_minus);
    else if(t==TOK_MULTASSIGN)
      exp.set(ID_statement, ID_assign_mult);
    else if(t==TOK_DIVASSIGN)
      exp.set(ID_statement, ID_assign_div);
    else if(t==TOK_MODASSIGN)
      exp.set(ID_statement, ID_assign_mod);
    else if(t==TOK_SHLASSIGN)
      exp.set(ID_statement, ID_assign_shl);
    else if(t==TOK_SHRASSIGN)
      exp.set(ID_statement, ID_assign_shr);
    else if(t==TOK_ANDASSIGN)
      exp.set(ID_statement, ID_assign_bitand);
    else if(t==TOK_XORASSIGN)
      exp.set(ID_statement, ID_assign_bitxor);
    else if(t==TOK_ORASSIGN)
      exp.set(ID_statement, ID_assign_bitor);

    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rExpression 4\n";
  #endif

  return true;
}

/*
  conditional.expr
  : logical.or.expr {'?' comma.expression ':' conditional.expr}  right-to-left
*/
bool Parser::rConditionalExpr(exprt &exp, bool template_args)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rConditionalExpr 0\n";
  #endif

  if(!rLogicalOrExpr(exp, template_args))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rConditionalExpr 1\n";
  #endif

  if(lex.LookAhead(0)=='?')
  {
    cpp_tokent tk1, tk2;
    exprt then, otherwise;

    lex.get_token(tk1);
    if(!rCommaExpression(then))
      return false;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rConditionalExpr 2\n";
    #endif

    if(lex.get_token(tk2)!=':')
      return false;

    if(!rExpression(otherwise, template_args))
      return false;

    exprt cond;
    cond.swap(exp);

    exp=exprt(ID_if);
    exp.move_to_operands(cond, then, otherwise);
    set_location(exp, tk1);
  }

  return true;
}

/*
  logical.or.expr
  : logical.and.expr
  | logical.or.expr LogOrOp logical.and.expr                left-to-right
*/
bool Parser::rLogicalOrExpr(exprt &exp, bool template_args)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rLogicalOrExpr 0\n";
  #endif

  if(!rLogicalAndExpr(exp, template_args))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rLogicalOrExpr 1\n";
  #endif

  while(lex.LookAhead(0)==TOK_OROR)
  {
    cpp_tokent tk;
    lex.get_token(tk);

    exprt right;
    if(!rLogicalAndExpr(right, template_args))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt(ID_or);
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  return true;
}

/*
  logical.and.expr
  : inclusive.or.expr
  | logical.and.expr LogAndOp inclusive.or.expr
*/
bool Parser::rLogicalAndExpr(exprt &exp, bool template_args)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rLogicalAndExpr 1\n";
  #endif

  if(!rInclusiveOrExpr(exp, template_args))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rLogicalAndExpr 1\n";
  #endif

  while(lex.LookAhead(0)==TOK_ANDAND)
  {
    cpp_tokent tk;
    lex.get_token(tk);

    exprt right;
    if(!rInclusiveOrExpr(right, template_args))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt(ID_and);
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  return true;
}

/*
  inclusive.or.expr
  : exclusive.or.expr
  | inclusive.or.expr '|' exclusive.or.expr
*/
bool Parser::rInclusiveOrExpr(exprt &exp, bool template_args)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rInclusiveOrExpr 0\n";
  #endif

  if(!rExclusiveOrExpr(exp, template_args))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rInclusiveOrExpr 1\n";
  #endif

  while(lex.LookAhead(0)=='|')
  {
    cpp_tokent tk;
    lex.get_token(tk);

    exprt right;
    if(!rExclusiveOrExpr(right, template_args))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt(ID_bitor);
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  return true;
}

/*
  exclusive.or.expr
  : and.expr
  | exclusive.or.expr '^' and.expr
*/
bool Parser::rExclusiveOrExpr(exprt &exp, bool template_args)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rExclusiveOrExpr 0\n";
  #endif

  if(!rAndExpr(exp, template_args))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rExclusiveOrExpr 1\n";
  #endif

  while(lex.LookAhead(0)=='^')
  {
    cpp_tokent tk;
    lex.get_token(tk);

    exprt right;
    if(!rAndExpr(right, template_args))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt(ID_bitxor);
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  return true;
}

/*
  and.expr
  : equality.expr
  | and.expr '&' equality.expr
*/
bool Parser::rAndExpr(exprt &exp, bool template_args)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rAndExpr 0\n";
  #endif

  if(!rEqualityExpr(exp, template_args))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rAndExpr 1\n";
  #endif

  while(lex.LookAhead(0)=='&')
  {
    cpp_tokent tk;
    lex.get_token(tk);

    exprt right;
    if(!rEqualityExpr(right, template_args))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt(ID_bitand);
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  return true;
}

/*
  equality.expr
  : relational.expr
  | equality.expr EqualOp relational.expr
*/
bool Parser::rEqualityExpr(exprt &exp, bool template_args)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rEqualityExpr 0\n";
  #endif

  if(!rRelationalExpr(exp, template_args))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rEqualityExpr 1\n";
  #endif

  while(lex.LookAhead(0)==TOK_EQ ||
        lex.LookAhead(0)==TOK_NE)
  {
    cpp_tokent tk;
    lex.get_token(tk);

    exprt right;
    if(!rRelationalExpr(right, template_args))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt(tk.kind==TOK_EQ?ID_equal:ID_notequal);
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  return true;
}

/*
  relational.expr
  : shift.expr
  | relational.expr (RelOp | '<' | '>') shift.expr
*/
bool Parser::rRelationalExpr(exprt &exp, bool template_args)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rRelationalExpr 0\n";
  #endif

  if(!rShiftExpr(exp, template_args))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rRelationalExpr 1\n";
  #endif

  int t;

  while(t=lex.LookAhead(0),
        (t==TOK_LE || t==TOK_GE || t=='<' || (t=='>' && !template_args)))
  {
    cpp_tokent tk;
    lex.get_token(tk);

    exprt right;
    if(!rShiftExpr(right, template_args))
      return false;

    exprt left;
    left.swap(exp);

    irep_idt id;

    switch(t)
    {
    case TOK_LE: id=ID_le; break;
    case TOK_GE: id=ID_ge; break;
    case '<': id=ID_lt; break;
    case '>': id=ID_gt; break;
    }

    exp=exprt(id);
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  return true;
}

/*
  shift.expr
  : additive.expr
  | shift.expr ShiftOp additive.expr
*/
bool Parser::rShiftExpr(exprt &exp, bool template_args)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rShiftExpr 0\n";
  #endif

  if(!rAdditiveExpr(exp))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rShiftExpr 1\n";
  #endif

  while(lex.LookAhead(0)==TOK_SHIFTLEFT ||
        (lex.LookAhead(0)==TOK_SHIFTRIGHT && !template_args))
  {
    cpp_tokent tk;
    lex.get_token(tk);

    exprt right;
    if(!rAdditiveExpr(right))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt((tk.kind==TOK_SHIFTRIGHT)?ID_shr:ID_shl);
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  return true;
}

/*
  additive.expr
  : multiply.expr
  | additive.expr ('+' | '-') multiply.expr
*/
bool Parser::rAdditiveExpr(exprt &exp)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rAdditiveExpr 0\n";
  #endif

  if(!rMultiplyExpr(exp))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rAdditiveExpr 1\n";
  #endif

  int t;
  while(t=lex.LookAhead(0), (t=='+' || t=='-'))
  {
    cpp_tokent tk;
    lex.get_token(tk);

    exprt right;
    if(!rMultiplyExpr(right))
      return false;

    exprt left;
    left.swap(exp);

    irep_idt id;
    switch(t)
    {
    case '+': id=ID_plus; break;
    case '-': id=ID_minus; break;
    }

    exp=exprt(id);
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  return true;
}

/*
  multiply.expr
  : pm.expr
  | multiply.expr ('*' | '/' | '%') pm.expr
*/
bool Parser::rMultiplyExpr(exprt &exp)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rMultiplyExpr 0\n";
  #endif

  if(!rPmExpr(exp))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rMultiplyExpr 1\n";
  #endif

  int t;
  while(t=lex.LookAhead(0), (t=='*' || t=='/' || t=='%'))
  {
    cpp_tokent tk;
    lex.get_token(tk);

    exprt right;
    if(!rPmExpr(right))
      return false;

    exprt left;
    left.swap(exp);

    irep_idt id;
    switch(t)
    {
    case '*': id=ID_mult; break;
    case '/': id=ID_div; break;
    case '%': id=ID_mod; break;
    }

    exp=exprt(id);
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rMultiplyExpr 2\n";
  #endif

  return true;
}

/*
  pm.expr        (pointer to member .*, ->*)
  : cast.expr
  | pm.expr DOTPM cast.expr
  | pm.expr ARROWPM cast.expr
*/
bool Parser::rPmExpr(exprt &exp)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rPmExpr 0\n";
  #endif

  if(!rCastExpr(exp))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rPmExpr 1\n";
  #endif

  while(lex.LookAhead(0)==TOK_DOTPM ||
        lex.LookAhead(0)==TOK_ARROWPM)
  {
    cpp_tokent tk;
    lex.get_token(tk);

    exprt right;
    if(!rCastExpr(right))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt("pointer-to-member");
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rPmExpr 2\n";
  #endif

  return true;
}

/*
  cast.expr
  : unary.expr
  | '(' type.name ')' cast.expr
*/
bool Parser::rCastExpr(exprt &exp)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rCastExpr 0\n";
  #endif

  if(lex.LookAhead(0)!='(')
    return rUnaryExpr(exp);
  else
  {
    // There is an ambiguity in the C++ grammar as follows:
    // (TYPENAME) + expr   (typecast of unary plus)  vs.
    // (expr) + expr       (sum of two expressions)
    // Same issue with the operators & and - and *

    cpp_tokent tk1, tk2;
    typet tname;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rCastExpr 1\n";
    #endif

    cpp_token_buffert::post pos=lex.Save();
    lex.get_token(tk1);

    if(rTypeName(tname))
    {
      if(lex.get_token(tk2)==')')
      {
        if(lex.LookAhead(0)=='&' &&
           lex.LookAhead(1)==TOK_INTEGER)
        {
          // we have (x) & 123
          // This is likely a binary bit-wise 'and'
        }
        else if(rCastExpr(exp))
        {
          exprt op;
          op.swap(exp);

          exp=exprt("explicit-typecast");
          exp.type().swap(tname);
          exp.move_to_operands(op);
          set_location(exp, tk1);

          return true;
        }
      }
    }

    lex.Restore(pos);
    return rUnaryExpr(exp);
  }
}

/*
  type.name
  : type.specifier cast.declarator
*/
bool Parser::rTypeName(typet &tname)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rTypeName 0\n";
  #endif

  typet type_name;

  if(!rTypeSpecifier(type_name, true))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rTypeName 1\n";
  #endif

  cpp_declaratort declarator;

  if(!rDeclarator(declarator, kCastDeclarator, false, false))
    return false;

  if(!declarator.method_qualifier().id().empty())
  {
    tname.swap(declarator.method_qualifier());
    merge_types(declarator.type(), tname);
  }
  else
    tname.swap(declarator.type());

  // make type_name subtype of arg
  make_subtype(type_name, tname);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rTypeName 2\n";
  #endif

  return true;
}

/*
  type.name
  | type.specifier { '(' type.specifier ( ',' type.specifier )*
      { {,} Ellipsis } ')' } {cv.qualify} {(ptr.operator)*}
*/
bool Parser::rTypeNameOrFunctionType(typet &tname)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ')
            << "Parser::rTypeNameOrFunctionType 0\n";
  #endif

  cpp_token_buffert::post pos=lex.Save();

  if(rTypeName(tname) && lex.LookAhead(0)!='(')
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::rTypeNameOrFunctionType 1\n";
    #endif

    if(!optPtrOperator(tname))
      return false;

    return true;
  }

  lex.Restore(pos);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ')
            << "Parser::rTypeNameOrFunctionType 2\n";
  #endif

  typet return_type;
  if(!rCastOperatorName(return_type))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ')
            << "Parser::rTypeNameOrFunctionType 3\n";
  #endif

  if(lex.LookAhead(0)!='(')
  {
    tname.swap(return_type);

    if(!optPtrOperator(tname))
      return false;

    return true;
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ')
            << "Parser::rTypeNameOrFunctionType 4\n";
  #endif

  code_typet type({}, return_type);
  cpp_tokent op;
  lex.get_token(op);

  // TODO -- cruel hack for Clang's type_traits:
  // struct __member_pointer_traits_imp<_Rp (_Class::*)(_Param..., ...),
  //                                    true, false>
  if(lex.LookAhead(0)==TOK_IDENTIFIER &&
     lex.LookAhead(1)==TOK_SCOPE &&
     lex.LookAhead(2)=='*' &&
     lex.LookAhead(3)==')' &&
     lex.LookAhead(4)=='(')
  {
    lex.get_token();
    lex.get_token();
    lex.get_token();
    lex.get_token();
    lex.get_token();
  }
  else if(lex.LookAhead(0)==TOK_IDENTIFIER &&
          lex.LookAhead(1)==')' &&
          lex.LookAhead(2)=='(')
  {
    lex.get_token(op);
    type.set(ID_identifier, op.data.get(ID_C_base_name));
    lex.get_token();
    lex.get_token();
  }
  else if(lex.LookAhead(0)=='*' &&
          lex.LookAhead(1)==TOK_IDENTIFIER &&
          lex.LookAhead(2)==')' &&
          lex.LookAhead(3)=='(')
  {
    lex.get_token(op);
    lex.get_token(op);
    type.set(ID_identifier, op.data.get(ID_C_base_name));
    lex.get_token();
    lex.get_token();
  }

  for(;;)
  {
    // function type parameters

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::rTypeNameOrFunctionType 5\n";
    #endif

    int t=lex.LookAhead(0);
    if(t==')')
      break;
    else if(t==TOK_ELLIPSIS)
    {
      cpp_tokent tk;
      lex.get_token(tk);
      type.make_ellipsis();
    }
    else
    {
      cpp_declarationt parameter_declaration;
      if(!rArgDeclaration(parameter_declaration))
        return false;

      code_typet::parametert parameter;
      parameter.swap(parameter_declaration);
      type.parameters().push_back(parameter);

      t=lex.LookAhead(0);
      if(t==',')
      {
        cpp_tokent tk;
        lex.get_token(tk);
      }
      else if(t==TOK_ELLIPSIS)
      {
        // TODO -- this is actually ambiguous as it could refer to a
        // template parameter pack or declare a variadic function
        cpp_tokent tk;
        lex.get_token(tk);
        type.make_ellipsis();
      }
      else if(t==')')
        break;
    }
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ')
            << "Parser::rTypeNameOrFunctionType 6\n";
  #endif

  cpp_tokent cp;
  lex.get_token(cp);

  // not sure where this one belongs
  if(!optCvQualify(type))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ')
            << "Parser::rTypeNameOrFunctionType 7\n";
  #endif

  // not sure where this one belongs
  if(!optPtrOperator(type))
    return false;

  tname.swap(type);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ')
            << "Parser::rTypeNameOrFunctionType 8\n";
  #endif

  return true;
}

/*
  unary.expr
  : postfix.expr
  | ('*' | '&' | '+' | '-' | '!' | '~' | IncOp) cast.expr
  | sizeof.expr
  | allocate.expr
  | throw.expression
  | noexcept.expr
*/

bool Parser::rUnaryExpr(exprt &exp)
{
  int t=lex.LookAhead(0);

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rUnaryExpr 0\n";
  #endif

  if(t=='*' || t=='&' || t=='+' ||
     t=='-' || t=='!' || t=='~' ||
     t==TOK_INCR || t==TOK_DECR)
  {
    cpp_tokent tk;
    lex.get_token(tk);

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rUnaryExpr 1\n";
    #endif

    exprt right;
    if(!rCastExpr(right))
      return false;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rUnaryExpr 2\n";
    #endif

    switch(t)
    {
    case '*':
      exp=exprt(ID_dereference);
      break;

    case '&':
      exp=exprt(ID_address_of);
      break;

    case '+':
      exp=exprt(ID_unary_plus);
      break;

    case '-':
      exp=exprt(ID_unary_minus);
      break;

    case '!':
      exp=exprt(ID_not);
      break;

    case '~':
      exp=exprt(ID_bitnot);
      break;

    case TOK_INCR:
      exp=exprt(ID_side_effect);
      exp.set(ID_statement, ID_preincrement);
      break;

    case TOK_DECR:
      exp=exprt(ID_side_effect);
      exp.set(ID_statement, ID_predecrement);
      break;

    default:
      UNREACHABLE;
    }

    exp.move_to_operands(right);
    set_location(exp, tk);

    return true;
  }
  else if(t==TOK_SIZEOF)
    return rSizeofExpr(exp);
  else if(t==TOK_ALIGNOF)
    return rAlignofExpr(exp);
  else if(t==TOK_THROW)
    return rThrowExpr(exp);
  else if(t==TOK_NOEXCEPT)
    return rNoexceptExpr(exp);
  else if(t==TOK_REAL || t==TOK_IMAG)
  {
    // a GCC extension for complex floating-point arithmetic
    cpp_tokent tk;
    lex.get_token(tk);

    exprt unary;

    if(!rUnaryExpr(unary))
      return false;

    exp=exprt(t==TOK_REAL?ID_complex_real:ID_complex_imag);
    exp.move_to_operands(unary);
    set_location(exp, tk);
    return true;
  }
  else if(isAllocateExpr(t))
    return rAllocateExpr(exp);
  else
    return rPostfixExpr(exp);
}

/*
  throw.expression
  : THROW {expression}
*/
bool Parser::rThrowExpr(exprt &exp)
{
  cpp_tokent tk;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rThrowExpr 0\n";
  #endif

  if(lex.get_token(tk)!=TOK_THROW)
    return false;

  int t=lex.LookAhead(0);

  exp = side_effect_expr_throwt(irept(), typet(), source_locationt());
  set_location(exp, tk);

  if(t==':' || t==';')
  {
    // done
  }
  else
  {
    exprt e;

    if(!rExpression(e, false))
      return false;

    exp.move_to_operands(e);
  }

  return true;
}

/*
  typeid.expr
  : TYPEID '(' expression ')'
  | TYPEID '(' type.name ')'
*/
bool Parser::rTypeidExpr(exprt &exp)
{
  cpp_tokent tk;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rTypeidExpr 0\n";
  #endif

  if(lex.get_token(tk)!=TOK_TYPEID)
    return false;

  if(lex.LookAhead(0)=='(')
  {
    typet tname;
    exprt subexp;
    cpp_tokent op, cp;

    cpp_token_buffert::post pos=lex.Save();
    lex.get_token(op);
    if(rTypeName(tname))
    {
      if(lex.get_token(cp)==')')
      {
        // exp=new PtreeTypeidExpr(new Leaf(tk),
        //                        Ptree::List(new Leaf(op), tname,
        //                        new Leaf(cp)));

        exp = exprt(ID_typeid);
        set_location(exp, tk);
        return true;
      }
    }

    lex.Restore(pos);
    lex.get_token(op);

    if(rExpression(subexp, false))
    {
      if(lex.get_token(cp)==')')
      {
        // exp=new PtreeTypeidExpr(
        //   new Leaf(tk),
        //   Ptree::List(
        //     Ptree::List(new Leaf(op), subexp, new Leaf(cp))
        //   ));

        exp = exprt(ID_typeid);
        set_location(exp, tk);
        return true;
      }
    }

    lex.Restore(pos);
  }

  return false;
}

/*
  sizeof.expr
  : SIZEOF unary.expr
  | SIZEOF '(' type.name ')'
  | SIZEOF Ellipsis '(' Identifier ')'
*/

bool Parser::rSizeofExpr(exprt &exp)
{
  cpp_tokent tk;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rSizeofExpr 0\n";
  #endif

  if(lex.get_token(tk)!=TOK_SIZEOF)
    return false;

  if(lex.LookAhead(0)=='(')
  {
    typet tname;
    cpp_tokent op, cp;

    cpp_token_buffert::post pos=lex.Save();
    lex.get_token(op);

    if(rTypeName(tname))
    {
      if(lex.get_token(cp)==')')
      {
        exp=exprt(ID_sizeof);
        exp.add(ID_type_arg).swap(tname);
        set_location(exp, tk);
        return true;
      }
    }

    lex.Restore(pos);
  }
  else if(lex.LookAhead(0)==TOK_ELLIPSIS)
  {
    typet tname;
    cpp_tokent ell, op, cp;

    lex.get_token(ell);

    lex.get_token(op);

    if(rTypeName(tname))
    {
      if(lex.get_token(cp)==')')
      {
        exp=exprt(ID_sizeof);
        exp.add(ID_type_arg).swap(tname);
        set_location(exp, tk);
        return true;
      }
    }

    return false;
  }

  exprt unary;

  if(!rUnaryExpr(unary))
    return false;

  exp=exprt(ID_sizeof);
  exp.move_to_operands(unary);
  set_location(exp, tk);
  return true;
}

/*
  alignof.expr
  | ALIGNOF '(' type.name ')'
*/

bool Parser::rAlignofExpr(exprt &exp)
{
  cpp_tokent tk;

  if(lex.get_token(tk)!=TOK_ALIGNOF)
    return false;

  typet tname;
  cpp_tokent op, cp;

  lex.get_token(op);

  if(!rTypeName(tname))
    return false;

  if(lex.get_token(cp)!=')')
    return false;

  exp=exprt(ID_alignof);
  exp.add(ID_type_arg).swap(tname);
  set_location(exp, tk);
  return true;
}

/*
  noexcept.expr
  : NOEXCEPT '(' expression ')'
*/
bool Parser::rNoexceptExpr(exprt &exp)
{
  cpp_tokent tk;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rNoexceptExpr 0\n";
  #endif

  if(lex.get_token(tk)!=TOK_NOEXCEPT)
    return false;

  if(lex.LookAhead(0)=='(')
  {
    exprt subexp;
    cpp_tokent op, cp;

    lex.get_token(op);

    if(rExpression(subexp, false))
    {
      if(lex.get_token(cp)==')')
      {
        // TODO
        exp=exprt(ID_noexcept);
        exp.move_to_operands(subexp);
        set_location(exp, tk);
        return true;
      }
    }
  }
  else
    return true;

  return false;
}

bool Parser::isAllocateExpr(int t)
{
  if(t==TOK_SCOPE)
    t=lex.LookAhead(1);

  return t==TOK_NEW || t==TOK_DELETE;
}

/*
  allocate.expr
  : {Scope | userdef.keyword} NEW allocate.type
  | {Scope} DELETE {'[' ']'} cast.expr
*/
bool Parser::rAllocateExpr(exprt &exp)
{
  cpp_tokent tk;
  irept head=get_nil_irep();

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rAllocateExpr 0\n";
  #endif

  int t=lex.LookAhead(0);
  if(t==TOK_SCOPE)
  {
    lex.get_token(tk);
    // TODO one can put 'new'/'delete' into a namespace!
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rAllocateExpr 1\n";
  #endif

  t=lex.get_token(tk);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rAllocateExpr 2\n";
  #endif

  if(t==TOK_DELETE)
  {
    exprt obj;

    if(lex.LookAhead(0)=='[')
    {
      lex.get_token(tk);

      if(lex.get_token(tk)!=']')
        return false;

      exp=exprt(ID_side_effect);
      exp.set(ID_statement, ID_cpp_delete_array);
    }
    else
    {
      exp=exprt(ID_side_effect);
      exp.set(ID_statement, ID_cpp_delete);
    }

    set_location(exp, tk);

    if(!rCastExpr(obj))
       return false;

    exp.move_to_operands(obj);

    return true;
  }
  else if(t==TOK_NEW)
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rAllocateExpr 3\n";
    #endif

    exp=exprt(ID_side_effect);
    exp.set(ID_statement, ID_cpp_new);
    set_location(exp, tk);

    exprt arguments, initializer;

    if(!rAllocateType(arguments, exp.type(), initializer))
      return false;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rAllocateExpr 4\n";
    #endif

    exp.add(ID_initializer).swap(initializer);
    exp.operands().swap(arguments.operands());
    return true;
  }
  else
    return false;
}

/*
  allocate.type
  : {'(' function.arguments ')'} type.specifier new.declarator
    {allocate.initializer}
  | {'(' function.arguments ')'} '(' type.name ')' {allocate.initializer}
*/

bool Parser::rAllocateType(
  exprt &arguments,
  typet &atype,
  exprt &initializer)
{
  if(lex.LookAhead(0)!='(')
  {
    atype.make_nil();
  }
  else
  {
    // reads the '('
    lex.get_token();

    // we may need to backtrack
    cpp_token_buffert::post pos=lex.Save();

    if(rTypeName(atype))
    {
      if(lex.get_token()==')')
      {
        // we have "( type.name )"

        if(lex.LookAhead(0)!='(')
        {
          if(!isTypeSpecifier())
            return true;
        }
        else if(rAllocateInitializer(initializer))
        {
          // the next token cannot be '('
          if(lex.LookAhead(0)!='(')
            return true;
        }
      }
    }

    // if we reach here, it's not '(' type.name ')',
    // and we have to process '(' function.arguments ')'.

    lex.Restore(pos);
    if(!rFunctionArguments(arguments))
      return false;

    if(lex.get_token()!=')')
      return false;
  }

  if(lex.LookAhead(0)=='(')
  {
    lex.get_token();

    typet tname;

    if(!rTypeName(tname))
      return false;

    if(lex.get_token()!=')')
      return false;

    atype.swap(tname);
  }
  else
  {
    typet tname;

    if(!rTypeSpecifier(tname, false))
      return false;

    if(!rNewDeclarator(tname))
      return false;

    atype.swap(tname);
  }

  if(lex.LookAhead(0)=='(')
  {
    if(!rAllocateInitializer(initializer))
      return false;
  }
  else if(lex.LookAhead(0)=='{')
  {
    // this is a C++11 extension
    if(!rInitializeExpr(initializer))
      return false;
  }

  return true;
}

/*
  new.declarator
  : empty
  | ptr.operator
  | {ptr.operator} ('[' comma.expression ']')+
*/
bool Parser::rNewDeclarator(typet &decl)
{
  if(lex.LookAhead(0)!='[')
    if(!optPtrOperator(decl))
      return false;

  while(lex.LookAhead(0)=='[')
  {
    cpp_tokent ob, cb;
    exprt expr;

    lex.get_token(ob);
    if(!rCommaExpression(expr))
      return false;

    if(lex.get_token(cb)!=']')
      return false;

    array_typet array_type(decl, expr);
    set_location(array_type, ob);

    decl.swap(array_type);
  }

  return true;
}

/*
  allocate.initializer
  : '(' {initialize.expr (',' initialize.expr)* } ')'
*/
bool Parser::rAllocateInitializer(exprt &init)
{
  if(lex.get_token()!='(')
    return false;

  init.clear();

  if(lex.LookAhead(0)==')')
  {
    lex.get_token();
    return true;
  }

  for(;;)
  {
    exprt exp;
    if(!rInitializeExpr(exp))
      return false;

    init.move_to_operands(exp);

    if(lex.LookAhead(0)==TOK_ELLIPSIS)
    {
      lex.get_token();
      // TODO
    }

    if(lex.LookAhead(0)==',')
      lex.get_token();
    else if(lex.LookAhead(0)==')')
    {
      lex.get_token();
      break;
    }
    else
      return false;
  }

  return true;
}

/*
  postfix.exp
  : primary.exp
  | postfix.expr '[' comma.expression ']'
  | postfix.expr '(' function.arguments ')'
  | postfix.expr '.' var.name
  | postfix.expr ArrowOp var.name
  | postfix.expr IncOp
  | openc++.postfix.expr

  openc++.postfix.expr
  : postfix.expr '.' userdef.statement
  | postfix.expr ArrowOp userdef.statement

  Note: function-style casts are accepted as function calls.
*/
bool Parser::rPostfixExpr(exprt &exp)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rPostfixExpr 0\n";
  #endif

  if(!rPrimaryExpr(exp))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rPostfixExpr 1\n";
  #endif

  exprt e;
  cpp_tokent cp, op;
  int t2;

  for(;;)
  {
    switch(lex.LookAhead(0))
    {
    case '[':
      lex.get_token(op);
      if(!rCommaExpression(e))
        return false;

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rPostfixExpr 2\n";
      #endif

      if(lex.get_token(cp)!=']')
        return false;

      {
        exprt left;
        left.swap(exp);

        exp=exprt(ID_index);
        exp.move_to_operands(left, e);
        set_location(exp, op);
      }
      break;

    case '(':
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rPostfixExpr 3\n";
      #endif

      lex.get_token(op);
      if(!rFunctionArguments(e))
        return false;

      if(lex.get_token(cp)!=')')
        return false;

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rPostfixExpr 4\n";
      #endif

      {
        side_effect_expr_function_callt fc;
        fc.function().swap(exp);
        fc.arguments().reserve(e.operands().size());
        set_location(fc, op);

        Forall_operands(it, e)
          fc.arguments().push_back(*it);
        e.operands().clear(); // save some
        exp.swap(fc);
      }
      break;

    case TOK_INCR:
      lex.get_token(op);

      {
        side_effect_exprt tmp(ID_postincrement, typet(), source_locationt());
        tmp.move_to_operands(exp);
        set_location(tmp, op);
        exp.swap(tmp);
      }
      break;

    case TOK_DECR:
      lex.get_token(op);

      {
        side_effect_exprt tmp(ID_postdecrement, typet(), source_locationt());
        tmp.move_to_operands(exp);
        set_location(tmp, op);
        exp.swap(tmp);
      }
      break;

    case '.':
    case TOK_ARROW:
      t2=lex.get_token(op);

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rPostfixExpr 5\n";
      #endif

      if(!rVarName(e))
        return false;

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rPostfixExpr 6\n";
      #endif

      {
        exprt left;
        left.swap(exp);

        if(t2=='.')
          exp=exprt(ID_member);
        else // ARROW
          exp=exprt(ID_ptrmember);

        exp.move_to_operands(left);
        set_location(exp, op);
      }

      exp.add(ID_component_cpp_name).swap(e);

      break;

    default:
      return true;
    }
  }
}

/*
  __uuidof( expression )
  __uuidof( type )
  This is a Visual Studio Extension.
*/

bool Parser::rMSCuuidof(exprt &expr)
{
  cpp_tokent tk;

  if(lex.get_token(tk)!=TOK_MSC_UUIDOF)
    return false;

  if(lex.get_token(tk)!='(')
    return false;

  {
    typet tname;
    cpp_tokent cp;

    cpp_token_buffert::post pos=lex.Save();

    if(rTypeName(tname))
    {
      if(lex.get_token(cp)==')')
      {
        expr=exprt(ID_msc_uuidof);
        expr.add(ID_type_arg).swap(tname);
        set_location(expr, tk);
        return true;
      }
    }

    lex.Restore(pos);
  }

  exprt unary;

  if(!rUnaryExpr(unary))
    return false;

  if(lex.get_token(tk)!=')')
    return false;

  expr=exprt(ID_msc_uuidof);
  expr.move_to_operands(unary);
  set_location(expr, tk);
  return true;
}

/*
  __if_exists ( identifier ) { token stream }
  __if_not_exists ( identifier ) { token stream }
*/

bool Parser::rMSC_if_existsExpr(exprt &expr)
{
  cpp_tokent tk1;

  lex.get_token(tk1);

  if(tk1.kind!=TOK_MSC_IF_EXISTS &&
     tk1.kind!=TOK_MSC_IF_NOT_EXISTS)
    return false;

  cpp_tokent tk2;

  if(lex.get_token(tk2)!='(')
    return false;

  exprt name;

  if(!rVarName(name))
    return false;

  if(lex.get_token(tk2)!=')')
    return false;

  if(lex.get_token(tk2)!='{')
    return false;

  exprt op;

  if(!rUnaryExpr(op))
    return false;

  if(lex.get_token(tk2)!='}')
    return false;

  expr=exprt(
    tk1.kind==TOK_MSC_IF_EXISTS?ID_msc_if_exists:
                                ID_msc_if_not_exists);

  expr.move_to_operands(name, op);

  set_location(expr, tk1);

  return true;
}

bool Parser::rMSC_if_existsStatement(codet &code)
{
  cpp_tokent tk1;

  lex.get_token(tk1);

  if(tk1.kind!=TOK_MSC_IF_EXISTS &&
     tk1.kind!=TOK_MSC_IF_NOT_EXISTS)
    return false;

  cpp_tokent tk2;

  if(lex.get_token(tk2)!='(')
    return false;

  exprt name;

  if(!rVarName(name))
    return false;

  if(lex.get_token(tk2)!=')')
    return false;

  if(lex.get_token(tk2)!='{')
    return false;

  codet block;

  while(lex.LookAhead(0)!='}')
  {
    codet statement;

    if(!rStatement(statement))
      return false;

    block.move_to_operands(statement);
  }

  if(lex.get_token(tk2)!='}')
    return false;

  code=codet(
    tk1.kind==TOK_MSC_IF_EXISTS?ID_msc_if_exists:
                                ID_msc_if_not_exists);

  code.move_to_operands(name, block);

  set_location(code, tk1);

  return true;
}

/*
  __is_base_of ( base, derived )
  __is_convertible_to ( from, to )
  __is_class ( t )
  __is_... (t)
*/

bool Parser::rTypePredicate(exprt &expr)
{
  cpp_tokent tk;

  lex.get_token(tk);

  expr.id(irep_idt(tk.text));
  set_location(expr, tk);

  typet tname1, tname2;

  switch(tk.kind)
  {
  case TOK_UNARY_TYPE_PREDICATE:
    if(lex.get_token(tk)!='(')
      return false;
    if(!rTypeName(tname1))
      return false;
    if(lex.get_token(tk)!=')')
      return false;
    expr.add(ID_type_arg).swap(tname1);
    break;

  case TOK_BINARY_TYPE_PREDICATE:
    if(lex.get_token(tk)!='(')
      return false;
    if(!rTypeName(tname1))
      return false;
    if(lex.get_token(tk)!=',')
      return false;
    if(!rTypeName(tname2))
      return false;
    if(lex.get_token(tk)!=')')
      return false;
    expr.add("type_arg1").swap(tname1);
    expr.add("type_arg2").swap(tname2);
    break;

  default:
    UNREACHABLE;
  }

  return true;
}

/*
  primary.exp
  : Constant
  | CharConst
  | WideCharConst !!! new
  | String
  | WideStringL   !!! new
  | THIS
  | var.name
  | '(' comma.expression ')'
  | integral.or.class.spec '(' function.arguments ')'
  | integral.or.class.spec initializer
  | typeid.expr
  | true
  | false
  | nullptr
*/
bool Parser::rPrimaryExpr(exprt &exp)
{
  cpp_tokent tk, tk2;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 0 "
            << lex.LookAhead(0) << ' ' << lex.current_token().text << '\n';
  #endif

  switch(lex.LookAhead(0))
  {
  case TOK_INTEGER:
  case TOK_CHARACTER:
  case TOK_FLOATING:
    lex.get_token(tk);
    exp.swap(tk.data);
    set_location(exp, tk);
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 1\n";
    #endif
    return true;

  case TOK_STRING:
    rString(tk);
    exp.swap(tk.data);
    set_location(exp, tk);
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 2\n";
    #endif
    return true;

  case TOK_THIS:
    lex.get_token(tk);
    exp=exprt("cpp-this");
    set_location(exp, tk);
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 3\n";
    #endif
    return true;

  case TOK_TRUE:
    lex.get_token(tk);
    exp = typecast_exprt(true_exprt(), c_bool_type());
    set_location(exp, tk);
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 4\n";
    #endif
    return true;

  case TOK_FALSE:
    lex.get_token(tk);
    exp = typecast_exprt(false_exprt(), c_bool_type());
    set_location(exp, tk);
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 5\n";
    #endif
    return true;

  case TOK_NULLPTR:
    lex.get_token(tk);
    // as an exception, we set the width of pointer
    exp=constant_exprt(ID_NULL, pointer_type(typet(ID_nullptr)));
    set_location(exp, tk);
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 6\n";
    #endif
    return true;

  case '(':
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 7\n";
    #endif
    lex.get_token(tk);

    if(lex.LookAhead(0)=='{') // GCC extension
    {
      codet code;

      if(!rCompoundStatement(code))
        return false;

      exp=exprt(ID_side_effect);
      exp.set(ID_statement, ID_statement_expression);
      set_location(exp, tk);
      exp.move_to_operands(code);

      if(lex.get_token(tk2)!=')')
        return false;
    }
    else
    {
      exprt exp2;

      if(!rCommaExpression(exp2))
        return false;

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 8\n";
      #endif

      if(lex.get_token(tk2)!=')')
        return false;

      exp.swap(exp2);
    }

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 9\n";
    #endif
    return true;

  case '{': // C++11 initialisation expression
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 10\n";
    #endif
    return rInitializeExpr(exp);

  case TOK_TYPEID:
    return rTypeidExpr(exp);

  case TOK_UNARY_TYPE_PREDICATE:
  case TOK_BINARY_TYPE_PREDICATE:
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 11\n";
    #endif
    return rTypePredicate(exp);

  case TOK_MSC_UUIDOF:
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 12\n";
    #endif
    return rMSCuuidof(exp);

  // not quite appropriate: these allow more general
  // token streams, not just expressions
  case TOK_MSC_IF_EXISTS:
  case TOK_MSC_IF_NOT_EXISTS:
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 13\n";
    #endif
    return rMSC_if_existsExpr(exp);

  default:
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 14\n";
    #endif
    {
      typet type;

      if(!optIntegralTypeOrClassSpec(type))
        return false;

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 15\n";
      #endif

      if(type.is_not_nil() && lex.LookAhead(0)==TOK_SCOPE)
      {
        lex.get_token(tk);
        lex.get_token(tk);

        // TODO
      }
      else if(type.is_not_nil())
      {
        #ifdef DEBUG
        std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 16\n";
        #endif
        if(lex.LookAhead(0)=='{')
        {
          lex.LookAhead(0, tk);

          exprt exp2;
          if(!rInitializeExpr(exp2))
            return false;

          exp=exprt("explicit-constructor-call");
          exp.type().swap(type);
          exp.move_to_operands(exp2);
          set_location(exp, tk);
        }
        else if(lex.LookAhead(0)=='(')
        {
          lex.get_token(tk);

          exprt exp2;
          if(!rFunctionArguments(exp2))
            return false;

          if(lex.get_token(tk2)!=')')
            return false;

          exp=exprt("explicit-constructor-call");
          exp.type().swap(type);
          exp.operands().swap(exp2.operands());
          set_location(exp, tk);
        }
        else
          return false;
      }
      else
      {
        if(!rVarName(exp))
          return false;

        if(lex.LookAhead(0)==TOK_SCOPE)
        {
          lex.get_token(tk);

          // exp=new PtreeStaticUserStatementExpr(exp,
          //                        Ptree::Cons(new Leaf(tk), exp2));
          // TODO
        }
      }
    }
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 17\n";
    #endif

    return true;
  }
}

/*
  var.name : {'::'} name2 ('::' name2)*

  name2
  : Identifier {template.args}
  | '~' Identifier
  | OPERATOR operator.name

  if var.name ends with a template type, the next token must be '('
*/
bool Parser::rVarName(exprt &name)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rVarName 0\n";
  #endif

  if(rVarNameCore(name))
    return true;
  else
    return false;
}

bool Parser::rVarNameCore(exprt &name)
{
  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rVarNameCore 0\n";
  #endif

  name = cpp_namet().as_expr();
  irept::subt &components=name.get_sub();

  if(lex.LookAhead(0)==TOK_TYPENAME)
  {
    cpp_tokent tk;
    lex.get_token(tk);
    name.set(ID_typename, true);
  }

  {
    cpp_tokent tk;
    lex.LookAhead(0, tk);
    set_location(name, tk);
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rVarNameCore 1\n";
  #endif

  for(;;)
  {
    cpp_tokent tk;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rVarNameCore 1.1 "
              << lex.LookAhead(0)
              << '\n';
    #endif

    switch(lex.LookAhead(0))
    {
    case TOK_TEMPLATE:
      // this may be a template member function, for example
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rVarNameCore 2\n";
      #endif
      lex.get_token(tk);
      // Skip template token, next will be identifier
      if(lex.LookAhead(0)!=TOK_IDENTIFIER)
        return false;
      break;

    case TOK_IDENTIFIER:
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rVarNameCore 3\n";
      #endif

      lex.get_token(tk);
      components.push_back(cpp_namet::namet(tk.data.get(ID_C_base_name)));
      set_location(components.back(), tk);

      // may be followed by template arguments
      if(maybeTemplateArgs())
      {
        cpp_token_buffert::post pos=lex.Save();

        #ifdef DEBUG
        std::cout << std::string(__indent, ' ') << "Parser::rVarNameCore 4\n";
        #endif

        irept args;
        if(!rTemplateArgs(args))
        {
          lex.Restore(pos);
          return true;
        }

        components.push_back(irept(ID_template_args));
        components.back().add(ID_arguments).swap(args);
      }

      if(!moreVarName())
        return true;
      break;

    case TOK_SCOPE:
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rVarNameCore 5\n";
      #endif

      lex.get_token(tk);
      components.push_back(irept("::"));
      set_location(components.back(), tk);
      break;

    case '~':
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rVarNameCore 6\n";
      #endif

      lex.get_token(tk);

      if(lex.LookAhead(0)!=TOK_IDENTIFIER)
        return false;

      components.push_back(irept("~"));
      set_location(components.back(), tk);
      break;

    case TOK_OPERATOR:
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rVarNameCore 7\n";
      #endif

      lex.get_token(tk);

      components.push_back(irept(ID_operator));
      set_location(components.back(), tk);

      {
        irept op;
        if(!rOperatorName(op))
          return false;

        components.push_back(op);
      }
      return true;

    default:
      return false;
    }
  }
}

bool Parser::moreVarName()
{
  if(lex.LookAhead(0)==TOK_SCOPE)
  {
    int t=lex.LookAhead(1);
    if(t==TOK_IDENTIFIER || t=='~' || t==TOK_OPERATOR || t==TOK_TEMPLATE)
      return true;
  }

  return false;
}

/*
  template.args : '<' any* '>'

  template.args must be followed by '(' or '::'
*/
bool Parser::maybeTemplateArgs()
{
  int i=0;
  int t=lex.LookAhead(i++);

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::maybeTemplateArgs 0\n";
  #endif

  if(t=='<')
  {
#if 1
    for(;;)
    {
      int u=lex.LookAhead(i++);
      if(u=='\0' || u==';' || u=='}')
        return false;
      else if((u=='>' || u==TOK_SHIFTRIGHT) &&
              (lex.LookAhead(i)==TOK_SCOPE || lex.LookAhead(i)=='(' ||
               lex.LookAhead(i)==')'))
        return true;
    }
#else
    int n=1;

    while(n>0)
    {
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ')
                << "Parser::maybeTemplateArgs 1\n";
      #endif

      int u=lex.LookAhead(i++);

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ')
                << "Parser::maybeTemplateArgs 2\n";
      #endif

      if(u=='<')
        ++n;
      else if(u=='>')
        --n;
      else if(u=='(')
      {
        int m=1;
        while(m>0)
        {
          int v=lex.LookAhead(i++);

          #ifdef DEBUG
          std::cout << std::string(__indent, ' ')
                    << "Parser::maybeTemplateArgs 3\n";
          #endif

          if(v=='(')
            ++m;
          else if(v==')')
            --m;
          else if(v=='\0' || v==';' || v=='}')
            return false;
        }
      }
      else if(u=='\0' || u==';' || u=='}')
        return false;
      else if(u==TOK_SHIFTRIGHT && n>=2)
        n-=2;

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ')
                << "Parser::maybeTemplateArgs 4\n";
      #endif
    }

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::maybeTemplateArgs 5\n";
    #endif

    t=lex.LookAhead(i);

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::maybeTemplateArgs 6\n";
    #endif

    return t==TOK_SCOPE || t=='(';
#endif
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::maybeTemplateArgs 7\n";
  #endif

  return false;
}

/*
  function.body  : compound.statement
                 | { asm }
*/

bool Parser::rFunctionBody(cpp_declaratort &declarator)
{
  // The following is an extension in GCC,
  // ARMCC, CodeWarrior...

  if(lex.LookAhead(0)=='{' &&
     lex.LookAhead(1)==TOK_ASM_STRING)
  {
    cpp_tokent ob, tk, cb;
    lex.get_token(ob);

    codet body=code_blockt();
    set_location(body, ob);

    lex.get_token(tk);
    // TODO: add to body

    if(lex.get_token(cb)!='}')
      return false;

    declarator.value()=body;
    return true;
  }
  else
  {
    // this is for the benefit of set_location
    const cpp_namet &cpp_name=declarator.name();
    current_function=cpp_name.get_base_name();

    codet body;
    if(!rCompoundStatement(body))
    {
      current_function.clear();
      return false;
    }

    declarator.value()=body;

    current_function.clear();

    return true;
  }
}

/*
  compound.statement
  : '{' (statement)* '}'
*/
bool Parser::rCompoundStatement(codet &statement)
{
  cpp_tokent ob, cb;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rCompoundStatement 1\n";
  #endif

  if(lex.get_token(ob)!='{')
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rCompoundStatement 2\n";
  #endif

  statement=code_blockt();
  set_location(statement, ob);

  while(lex.LookAhead(0)!='}')
  {
    codet statement2;

    if(!rStatement(statement2))
    {
      if(!SyntaxError())
        return false;        // too many errors

      SkipTo('}');
      lex.get_token(cb);
      return true;        // error recovery
    }

    statement.move_to_operands(statement2);
  }

  if(lex.get_token(cb)!='}')
    return false;

  return true;
}

/*
  statement
  : compound.statement
  | typedef
  | if.statement
  | switch.statement
  | while.statement
  | do.statement
  | for.statement
  | try.statement
  | BREAK ';'
  | CONTINUE ';'
  | RETURN { comma.expression } ';'
  | GOTO Identifier ';'
  | CASE expression ':' statement
  | DEFAULT ':' statement
  | Identifier ':' statement
  | expr.statement
  | USING { NAMESPACE } identifier ';'
  | STATIC_ASSERT ( expression ',' expression ) ';'
*/
bool Parser::rStatement(codet &statement)
{
  cpp_tokent tk1, tk2, tk3;
  int k;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rStatement 0 "
            << lex.LookAhead(0) << "\n";
  #endif

  switch(k=lex.LookAhead(0))
  {
  case '{':
    return rCompoundStatement(statement);

  case TOK_TYPEDEF:
    return rTypedefStatement(statement);

  case TOK_IF:
    return rIfStatement(statement);

  case TOK_SWITCH:
    return rSwitchStatement(statement);

  case TOK_WHILE:
    return rWhileStatement(statement);

  case TOK_DO:
    return rDoStatement(statement);

  case TOK_FOR:
    return rForStatement(statement);

  case TOK_TRY:
    return rTryStatement(statement);

  case TOK_MSC_TRY:
    return rMSC_tryStatement(statement);

  case TOK_MSC_LEAVE:
    return rMSC_leaveStatement(statement);

  case TOK_BREAK:
  case TOK_CONTINUE:
    lex.get_token(tk1);

    if(k==TOK_BREAK)
      statement=codet(ID_break);
    else // CONTINUE
      statement=codet(ID_continue);

    set_location(statement, tk1);

    if(lex.get_token(tk2)!=';')
      return false;

    return true;

  case TOK_RETURN:
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rStatement RETURN 0\n";
    #endif

    lex.get_token(tk1);

    statement=codet(ID_return);
    set_location(statement, tk1);

    if(lex.LookAhead(0)==';')
    {
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ')
                << "Parser::rStatement RETURN 1\n";
      #endif
      lex.get_token(tk2);
    }
    else
    {
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ')
                << "Parser::rStatement RETURN 2\n";
      #endif

      exprt exp;

      if(!rCommaExpression(exp))
        return false;

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ')
                << "Parser::rStatement RETURN 3\n";
      #endif

      if(lex.get_token(tk2)!=';')
        return false;

      statement.move_to_operands(exp);
    }

    return true;

  case TOK_GOTO:
    lex.get_token(tk1);

    statement=codet(ID_goto);
    set_location(statement, tk1);

    if(lex.get_token(tk2)!=TOK_IDENTIFIER)
      return false;

    if(lex.get_token(tk3)!=';')
      return false;

    statement.set(ID_destination, tk2.data.get(ID_C_base_name));

    return true;

  case TOK_CASE:
    {
      lex.get_token(tk1);

      exprt case_expr;
      if(!rExpression(case_expr, false))
        return false;

      if(lex.LookAhead(0)==TOK_ELLIPSIS)
      {
        // This is a gcc extension for case ranges.
        // Should really refuse in non-GCC modes.
        lex.get_token(tk2);

        exprt range_end;
        if(!rExpression(range_end, false))
          return false;

        statement=codet(ID_gcc_switch_case_range);
        statement.operands().resize(3);
        statement.op0()=case_expr;
        statement.op1()=range_end;
        set_location(statement, tk1);

        if(lex.get_token(tk2)!=':')
          return false;

        codet statement2;
        if(!rStatement(statement2))
          return false;

        statement.op2().swap(statement2);
      }
      else
      {
        statement=code_switch_caset();
        set_location(statement, tk1);
        statement.op0()=case_expr;

        if(lex.get_token(tk2)!=':')
          return false;

        codet statement2;
        if(!rStatement(statement2))
          return false;

        statement.op1().swap(statement2);
      }
    }
    return true;

  case TOK_DEFAULT:
    {
      lex.get_token(tk1);

      statement=code_switch_caset();
      statement.set(ID_default, true);
      set_location(statement, tk1);

      if(lex.get_token(tk2)!=':')
        return false;

      codet statement2;
      if(!rStatement(statement2))
        return false;

      statement.op1().swap(statement2);
    }
    return true;

  case TOK_GCC_ASM:
    return rGCCAsmStatement(statement);

  case TOK_MSC_ASM:
    return rMSCAsmStatement(statement);

  case TOK_MSC_IF_EXISTS:
  case TOK_MSC_IF_NOT_EXISTS:
    return rMSC_if_existsStatement(statement);

  case TOK_IDENTIFIER:
    if(lex.LookAhead(1)==':')        // label statement
    {
      lex.get_token(tk1);

      statement=codet(ID_label);
      set_location(statement, tk1);
      statement.set(ID_label, tk1.data.get(ID_C_base_name));

      lex.get_token(tk2);

      codet statement2;
      if(!rStatement(statement2))
        return false;

      statement.move_to_operands(statement2);
      return true;
    }

    return rExprStatement(statement);

  case TOK_USING:
    {
      if(lex.LookAhead(1)==TOK_IDENTIFIER &&
         lex.LookAhead(2)=='=')
      {
        statement=codet(ID_decl);
        statement.operands().resize(1);
        return rTypedefUsing((cpp_declarationt &)statement.op0());
      }

      cpp_usingt cpp_using;

      if(!rUsing(cpp_using))
        return false;

      // TODO

      return true;
    }

  case TOK_STATIC_ASSERT:
    {
      cpp_static_assertt cpp_static_assert;

      if(!rStaticAssert(cpp_static_assert))
        return false;

      statement.set_statement(ID_static_assert);
      statement.add_source_location()=cpp_static_assert.source_location();
      statement.operands().swap(cpp_static_assert.operands());

      return true;
    }

  default:
    return rExprStatement(statement);
  }
}

/*
  if.statement
  : IF '(' comma.expression ')' statement { ELSE statement }
*/
bool Parser::rIfStatement(codet &statement)
{
  cpp_tokent tk1, tk2, tk3, tk4;

  if(lex.get_token(tk1)!=TOK_IF)
    return false;

  statement=codet(ID_ifthenelse);
  set_location(statement, tk1);

  if(lex.get_token(tk2)!='(')
    return false;

  exprt exp;
  if(!rCondition(exp))
    return false;

  if(lex.get_token(tk3)!=')')
    return false;

  codet then;
  if(!rStatement(then))
    return false;

  statement.operands().resize(3);
  statement.op0().swap(exp);
  statement.op1().swap(then);

  if(lex.LookAhead(0)==TOK_ELSE)
  {
    lex.get_token(tk4);

    codet otherwise;
    if(!rStatement(otherwise))
      return false;

    statement.op2().swap(otherwise);
  }
  else
    statement.op2().make_nil();

  return true;
}

/*
  switch.statement
  : SWITCH '(' comma.expression ')' statement
*/
bool Parser::rSwitchStatement(codet &statement)
{
  cpp_tokent tk1, tk2, tk3;

  if(lex.get_token(tk1)!=TOK_SWITCH)
    return false;

  statement=codet(ID_switch);
  set_location(statement, tk1);

  if(lex.get_token(tk2)!='(')
    return false;

  exprt exp;
  if(!rCondition(exp))
    return false;

  if(lex.get_token(tk3)!=')')
    return false;

  codet body;
  if(!rStatement(body))
    return false;

  statement.move_to_operands(exp, body);

  return true;
}

/*
  while.statement
  : WHILE '(' comma.expression ')' statement
*/
bool Parser::rWhileStatement(codet &statement)
{
  cpp_tokent tk1, tk2, tk3;

  if(lex.get_token(tk1)!=TOK_WHILE)
    return false;

  statement=codet(ID_while);
  set_location(statement, tk1);

  if(lex.get_token(tk2)!='(')
    return false;

  exprt exp;
  if(!rCondition(exp))
    return false;

  if(lex.get_token(tk3)!=')')
    return false;

  codet body;
  if(!rStatement(body))
    return false;

  statement.move_to_operands(exp, body);

  return true;
}

/*
  do.statement
  : DO statement WHILE '(' comma.expression ')' ';'
*/
bool Parser::rDoStatement(codet &statement)
{
  cpp_tokent tk0, tk1, tk2, tk3, tk4;

  if(lex.get_token(tk0)!=TOK_DO)
    return false;

  statement=codet(ID_dowhile);
  set_location(statement, tk0);

  codet body;
  if(!rStatement(body))
    return false;

  if(lex.get_token(tk1)!=TOK_WHILE)
    return false;

  if(lex.get_token(tk2)!='(')
    return false;

  exprt exp;
  if(!rCommaExpression(exp))
    return false;

  if(lex.get_token(tk3)!=')')
    return false;

  if(lex.get_token(tk4)!=';')
    return false;

  statement.move_to_operands(exp, body);

  return true;
}

/*
  for.statement
  : FOR '(' expr.statement {comma.expression} ';' {comma.expression} ')'
    statement
*/
bool Parser::rForStatement(codet &statement)
{
  cpp_tokent tk1, tk2, tk3, tk4;

  if(lex.get_token(tk1)!=TOK_FOR)
    return false;

  statement=codet(ID_for);
  set_location(statement, tk1);

  if(lex.get_token(tk2)!='(')
    return false;

  codet exp1;

  if(!rExprStatement(exp1))
    return false;

  exprt exp2;

  if(lex.LookAhead(0)==';')
    exp2.make_nil();
  else
    if(!rCommaExpression(exp2))
      return false;

  if(lex.get_token(tk3)!=';')
    return false;

  exprt exp3;

  if(lex.LookAhead(0)==')')
    exp3.make_nil();
  else
  {
    if(!rCommaExpression(exp3))
      return false;
  }

  if(lex.get_token(tk4)!=')')
    return false;

  codet body;

  if(!rStatement(body))
    return false;

  statement.reserve_operands(4);
  statement.move_to_operands(exp1);
  statement.move_to_operands(exp2);
  statement.move_to_operands(exp3);
  statement.move_to_operands(body);

  return true;
}

/*
  try.statement
  : TRY compound.statement (exception.handler)+ ';'

  exception.handler
  : CATCH '(' (arg.declaration | Ellipsis) ')' compound.statement
*/
bool Parser::rTryStatement(codet &statement)
{
  {
    cpp_tokent try_token;

    // The 'try' block
    if(lex.get_token(try_token)!=TOK_TRY)
      return false;

    statement=codet(ID_try_catch);
    statement.operands().reserve(2);
    set_location(statement, try_token);

    codet body;

    if(!rCompoundStatement(body))
      return false;

    statement.move_to_operands(body);
  }

  // iterate while there are catch clauses
  do
  {
    cpp_tokent catch_token, op_token, cp_token;

    if(lex.get_token(catch_token)!=TOK_CATCH)
      return false;

    if(lex.get_token(op_token)!='(')
      return false;

    codet catch_op;

    if(lex.LookAhead(0)==TOK_ELLIPSIS)
    {
      cpp_tokent ellipsis_token;
      lex.get_token(ellipsis_token);
      codet ellipsis(ID_ellipsis);
      set_location(ellipsis, ellipsis_token);
      catch_op=ellipsis;
    }
    else
    {
      cpp_declarationt declaration;

      if(!rArgDeclaration(declaration))
        return false;

      // No name in the declarator? Make one.
      assert(declaration.declarators().size()==1);

      if(declaration.declarators().front().name().is_nil())
        declaration.declarators().front().name() = cpp_namet("#anon");

      codet code_decl;
      code_decl.set_statement(ID_decl);
      code_decl.move_to_operands(declaration);
      set_location(code_decl, catch_token);

      catch_op=code_decl;
    }

    if(lex.get_token(cp_token)!=')')
      return false;

    codet body;

    if(!rCompoundStatement(body))
      return false;

    assert(body.get_statement()==ID_block);

    body.operands().insert(body.operands().begin(), catch_op);

    statement.move_to_operands(body);
  }
  while(lex.LookAhead(0)==TOK_CATCH);

  return true;
}

bool Parser::rMSC_tryStatement(codet &statement)
{
  // These are for 'structured exception handling',
  // and are a relic from Visual C.

  cpp_tokent tk, tk2, tk3;

  if(lex.get_token(tk)!=TOK_MSC_TRY)
    return false;

  set_location(statement, tk);

  codet body1, body2;

  if(!rCompoundStatement(body1))
    return false;

  if(lex.LookAhead(0)==TOK_MSC_EXCEPT)
  {
    lex.get_token(tk);
    statement.set_statement(ID_msc_try_except);

    // get '(' comma.expression ')'

    if(lex.get_token(tk2)!='(')
      return false;

    exprt exp;
    if(!rCommaExpression(exp))
      return false;

    if(lex.get_token(tk3)!=')')
      return false;

    if(!rCompoundStatement(body2))
      return false;

    statement.move_to_operands(body1, exp, body2);
  }
  else if(lex.LookAhead(0)==TOK_MSC_FINALLY)
  {
    lex.get_token(tk);
    statement.set_statement(ID_msc_try_finally);

    if(!rCompoundStatement(body2))
      return false;

    statement.move_to_operands(body1, body2);
  }
  else
    return false;

  return true;
}

bool Parser::rMSC_leaveStatement(codet &statement)
{
  // These are for 'structured exception handling',
  // and are a relic from Visual C.

  cpp_tokent tk;

  if(lex.get_token(tk)!=TOK_MSC_LEAVE)
    return false;

  statement = codet(ID_msc_leave);
  set_location(statement, tk);

  return true;
}

bool Parser::rGCCAsmStatement(codet &statement)
{
  cpp_tokent tk;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rGCCAsmStatement 1\n";
  #endif // DEBUG

  // asm [volatile] ("stuff" [ : ["=S" [(__res)], ... ]]) ;

  if(lex.get_token(tk)!=TOK_GCC_ASM)
    return false;

  statement=codet(ID_asm);
  statement.set(ID_flavor, ID_gcc);
  statement.operands().resize(5); // always has 5 operands
  set_location(statement, tk);

  if(lex.LookAhead(0)==TOK_VOLATILE)
    lex.get_token(tk);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rGCCAsmStatement 3\n";
  #endif // DEBUG

  if(lex.get_token(tk)!='(')
    return false;
  if(!rString(tk))
    return false;

  statement.op0()=tk.data;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rGCCAsmStatement 3\n";
  #endif // DEBUG

  while(lex.LookAhead(0)!=')')
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rGCCAsmStatement 4\n";
    #endif // DEBUG

    // get ':'
    if(lex.get_token(tk)!=':')
      return false;

    for(;;)
    {
      if(lex.LookAhead(0)!=TOK_STRING)
        break;

      // get String
      rString(tk);

      if(lex.LookAhead(0)=='(')
      {
        // get '('
        lex.get_token(tk);

        #ifdef DEBUG
        std::cout << std::string(__indent, ' ')
                  << "Parser::rGCCAsmStatement 5\n";
        #endif // DEBUG

        exprt expr;
        if(!rCommaExpression(expr))
          return false;

        #ifdef DEBUG
        std::cout << std::string(__indent, ' ')
                  << "Parser::rGCCAsmStatement 6\n";
        #endif // DEBUG

        if(lex.get_token(tk)!=')')
          return false;
      }

      // more?
      if(lex.LookAhead(0)!=',')
        break;
      lex.get_token(tk);
    }
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rGCCAsmStatement 7\n";
  #endif // DEBUG

  if(lex.get_token(tk)!=')')
    return false;
  if(lex.get_token(tk)!=';')
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rGCCAsmStatement 8\n";
  #endif // DEBUG

  return true;
}

bool Parser::rMSCAsmStatement(codet &statement)
{
  cpp_tokent tk;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rMSCAsmStatement 1\n";
  #endif // DEBUG

  // asm "STUFF"
  // asm { "STUFF" }

  if(lex.get_token(tk)!=TOK_MSC_ASM)
    return false;

  statement=codet(ID_asm);
  statement.set(ID_flavor, ID_msc);
  set_location(statement, tk);

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rMSCAsmStatement 2\n";
  #endif // DEBUG

  if(lex.LookAhead(0)=='{')
  {
    lex.get_token(tk); // eat the '{'

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rMSCAsmStatement 3\n";
    #endif // DEBUG

    if(lex.LookAhead(0)!=TOK_ASM_STRING)
      return true;

    lex.get_token(tk);

    statement.move_to_operands(tk.data);
    if(lex.get_token(tk)!='}')
      return false;

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rMSCAsmStatement 4\n";
    #endif // DEBUG
  }
  else
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rMSCAsmStatement 5\n";
    #endif // DEBUG

    if(lex.LookAhead(0)!=TOK_ASM_STRING)
      return true;

    lex.get_token(tk);
    statement.move_to_operands(tk.data);

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rMSCAsmStatement 6\n";
    #endif // DEBUG
  }

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rMSCAsmStatement 7\n";
  #endif // DEBUG

  return true;
}

/*
  expr.statement
  : ';'
  | declaration.statement
  | comma.expression ';'
  | openc++.postfix.expr
  | openc++.primary.exp
*/
bool Parser::rExprStatement(codet &statement)
{
  cpp_tokent tk;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rExprStatement 0\n";
  #endif

  if(lex.LookAhead(0)==';')
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rExprStatement 1\n";
    #endif

    lex.get_token(tk);
    statement = code_skipt();
    set_location(statement, tk);
    return true;
  }
  else
  {
    #ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rExprStatement 2\n";
    #endif

    cpp_token_buffert::post pos=lex.Save();

    if(rDeclarationStatement(statement))
    {
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "rDe "
                << statement.pretty() << '\n';
      #endif
      return true;
    }
    else
    {
      exprt exp;

      lex.Restore(pos);

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rExprStatement 3\n";
      #endif

      if(!rCommaExpression(exp))
        return false;

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rExprStatement 4\n";
      #endif

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rExprStatement 5 "
                << lex.LookAhead(0) << "\n";
      #endif

      if(lex.get_token(tk)!=';')
        return false;

      #ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rExprStatement 6\n";
      #endif

      statement=codet(ID_expression);
      statement.add_source_location()=exp.source_location();
      statement.move_to_operands(exp);
      return true;
    }
  }
}

bool Parser::rCondition(exprt &statement)
{
  cpp_token_buffert::post pos=lex.Save();

  // C++ conditions can be a declaration!

  cpp_declarationt declaration;

  if(rSimpleDeclaration(declaration))
  {
    statement=codet(ID_decl);
    statement.move_to_operands(declaration);
    return true;
  }
  else
  {
    lex.Restore(pos);

    if(!rCommaExpression(statement))
      return false;

    return true;
  }
}

/*
  declaration.statement
  : decl.head integral.or.class.spec {cv.qualify} {declarators} ';'
  | decl.head name {cv.qualify} declarators ';'
  | const.declaration

  decl.head
  : {storage.spec} {cv.qualify}

  const.declaration
  : cv.qualify {'*'} Identifier '=' expression {',' declarators} ';'

  Note: if you modify this function, take a look at rDeclaration(), too.
*/
bool Parser::rDeclarationStatement(codet &statement)
{
  cpp_storage_spect storage_spec;
  typet cv_q, integral;
  cpp_member_spect member_spec;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ')
            << "Parser::rDeclarationStatement 1\n";
  #endif

  if(!optStorageSpec(storage_spec))
    return false;

  cv_q.make_nil();

  if(!optCvQualify(cv_q))
    return false;

  // added for junk like const volatile static ...
  if(!optStorageSpec(storage_spec))
    return false;

  if(!optCvQualify(cv_q))
    return false;

  if(!optIntegralTypeOrClassSpec(integral))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ')
            << "Parser::rDeclarationStatement 2\n";
  #endif

  if(integral.is_not_nil())
    return rIntegralDeclStatement(statement, storage_spec, integral, cv_q);
  else
  {
    int t=lex.LookAhead(0);

    #ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::rDeclarationStatement 3 " << t << "\n";
    #endif

    if(cv_q.is_not_nil() &&
       ((t==TOK_IDENTIFIER && lex.LookAhead(1)=='=') || t=='*'))
    {
      #ifdef DEBUG
      std::cout << std::string(__indent, ' ')
                << "Parser::rDeclarationStatement 4\n";
      #endif

      statement=codet(ID_decl);
      statement.operands().resize(1);
      cpp_declarationt &declaration=(cpp_declarationt &)(statement.op0());
      return rConstDeclaration(declaration);
    }
    else
      return rOtherDeclStatement(statement, storage_spec, cv_q);
  }
}

/*
  integral.decl.statement
  : decl.head integral.or.class.spec {cv.qualify} {declarators} ';'
*/
bool Parser::rIntegralDeclStatement(
  codet &statement,
  cpp_storage_spect &storage_spec,
  typet &integral,
  typet &cv_q)
{
  cpp_tokent tk;

  if(!optCvQualify(cv_q))
    return false;

  merge_types(cv_q, integral);

  cpp_declarationt declaration;
  declaration.type().swap(integral);
  declaration.storage_spec().swap(storage_spec);

  if(lex.LookAhead(0)==';')
  {
    lex.get_token(tk);
    statement=codet(ID_decl);
    set_location(statement, tk);
    statement.move_to_operands(declaration);
  }
  else
  {
    if(!rDeclarators(declaration.declarators(), false, true))
      return false;

    if(lex.get_token(tk)!=';')
      return false;

    statement=codet(ID_decl);
    set_location(statement, tk);

    statement.move_to_operands(declaration);
  }

  return true;
}

/*
   other.decl.statement
   :decl.head name {cv.qualify} declarators ';'
*/
bool Parser::rOtherDeclStatement(
  codet &statement,
  cpp_storage_spect &storage_spec,
  typet &cv_q)
{
  typet type_name;
  cpp_tokent tk;

  #ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclStatement 1\n";
  #endif // DEBUG

  if(!rName(type_name))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclStatement 2\n";
  #endif // DEBUG

  if(!optCvQualify(cv_q))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclStatement 3\n";
  #endif // DEBUG

  merge_types(cv_q, type_name);

  cpp_declarationt declaration;
  declaration.type().swap(type_name);
  declaration.storage_spec().swap(storage_spec);

  if(!rDeclarators(declaration.declarators(), false, true))
    return false;

  #ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclStatement 4\n";
  #endif // DEBUG

  if(lex.get_token(tk)!=';')
    return false;

  statement=codet(ID_decl);
  set_location(statement, tk);
  statement.move_to_operands(declaration);

  return true;
}

bool Parser::MaybeTypeNameOrClassTemplate(cpp_tokent &)
{
  return true;
}

void Parser::SkipTo(int token)
{
  cpp_tokent tk;

  for(;;)
  {
    int t=lex.LookAhead(0);
    if(t==token || t=='\0')
      break;
    else
      lex.get_token(tk);
  }
}

bool Parser::operator()()
{
  number_of_errors=0;
  max_errors=10;

  cpp_itemt item;

  while(rProgram(item))
  {
    parser.parse_tree.items.push_back(item);
    item.clear();
  }

  #if 0
  root_scope.print(std::cout);
  #endif

  return number_of_errors!=0;
}

bool cpp_parse()
{
  Parser parser(cpp_parser);
  return parser();
}
