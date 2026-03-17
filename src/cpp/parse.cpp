/*******************************************************************\

Module: C++ Language Parsing

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Parsing

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/std_code.h>

#include <ansi-c/ansi_c_y.tab.h>
#include <ansi-c/merged_type.h>

#include "cpp_enum_type.h"
#include "cpp_member_spec.h"
#include "cpp_parser.h"
#include "cpp_token_buffer.h"

#include <map>

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
    VARIABLE_TEMPLATE,
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
    return kind == kindt::FUNCTION_TEMPLATE || kind == kindt::CLASS_TEMPLATE ||
           kind == kindt::MEMBER_TEMPLATE || kind == kindt::VARIABLE_TEMPLATE;
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
    case kindt::VARIABLE_TEMPLATE:
      return "VARIABLE_TEMPLATE";
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
    out << std::string(indent, ' ') << it->first << ": "
        << kind2string(it->second.kind) << '\n';
    it->second.print_rec(out, indent+2);
  }
}

class Parser // NOLINT(readability/identifiers)
{
public:
  Parser(cpp_parsert &_cpp_parser, message_handlert &message_handler)
    : lex(_cpp_parser.token_buffer),
      parse_tree(_cpp_parser.parse_tree),
      message_handler(message_handler),
      max_errors(10),
      cpp11(config.cpp.cpp_standard >= configt::cppt::cpp_standardt::CPP11),
      cpp20(config.cpp.cpp_standard >= configt::cppt::cpp_standardt::CPP20)
  {
    root_scope.kind=new_scopet::kindt::NAMESPACE;
    current_scope=&root_scope;
  }

  bool operator()();

protected:
  cpp_token_buffert &lex;
  cpp_parse_treet &parse_tree;
  message_handlert &message_handler;

  // scopes
  new_scopet root_scope;
  new_scopet *current_scope;
  new_scopet &add_id(const irept &name, new_scopet::kindt);
  new_scopet &add_id(const irep_idt &, new_scopet::kindt);
  void make_sub_scope(const irept &name, new_scopet::kindt);
  void make_sub_scope(const irep_idt &, new_scopet::kindt);
  new_scopet *lookup_id(const irep_idt &id);
  bool in_template_scope() const;

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
  std::optional<codet> rTypedefStatement();
  bool rTypeSpecifier(typet &, bool);
  bool isTypeSpecifier();
  bool rLinkageSpec(cpp_linkage_spect &);
  bool rNamespaceSpec(cpp_namespace_spect &);
  bool rUsing(cpp_usingt &);
  bool rUsingOrTypedef(cpp_itemt &);
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
  bool rGCCAttribute(typet &);
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
  bool rCppCastExpr(exprt &);
  bool rPostfixExpr(exprt &);
  bool rPrimaryExpr(exprt &);
  bool rLambdaExpr(exprt &);
  bool rVarName(exprt &);
  bool rVarNameCore(exprt &);
  bool maybeTemplateArgs();

  bool rFunctionBody(cpp_declaratort &);
  bool rContractAttributes(typet &);
  std::optional<codet> rCompoundStatement();
  std::optional<codet> rStatement();
  std::optional<codet> rIfStatement();
  std::optional<codet> rSwitchStatement();
  std::optional<codet> rWhileStatement();
  std::optional<codet> rDoStatement();
  std::optional<codet> rForStatement();
  std::optional<codet> rTryStatement();

  std::optional<codet> rExprStatement();
  std::optional<codet> rDeclarationStatement();
  std::optional<codet>
  rIntegralDeclStatement(cpp_storage_spect &, typet &, typet &);
  std::optional<codet> rOtherDeclStatement(cpp_storage_spect &, typet &);

  bool MaybeTypeNameOrClassTemplate(cpp_tokent &);
  void SkipTo(int token);
  bool moreVarName();

  bool rString(cpp_tokent &tk);

  // GCC extensions
  std::optional<codet> rGCCAsmStatement();

  // MSC extensions
  std::optional<codet> rMSC_tryStatement();
  std::optional<codet> rMSC_leaveStatement();
  std::optional<codet> rMSCAsmStatement();
  std::optional<codet> rMSC_if_existsStatement();
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
        p = &p->add_subtype();
    }

    *p=src;
  }

  unsigned int max_errors;
  const bool cpp11;
  const bool cpp20;
};

static bool is_identifier(int token)
{
  return token == TOK_GCC_IDENTIFIER || token == TOK_MSC_IDENTIFIER;
}

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

new_scopet *Parser::lookup_id(const irep_idt &id)
{
  for(new_scopet *scope = current_scope; scope != nullptr;
      scope = scope->parent)
  {
    auto it = scope->id_map.find(id);
    if(it != scope->id_map.end())
      return &(it->second);
  }
  return nullptr;
}

bool Parser::in_template_scope() const
{
  for(new_scopet *scope = current_scope; scope != nullptr;
      scope = scope->parent)
  {
    if(scope->kind == new_scopet::kindt::TEMPLATE)
      return true;
  }
  return false;
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

    std::string message = "parse error before '";

    for(std::size_t i=0; i<ERROR_TOKENS; i++)
      if(t[i].kind!='\0')
      {
        if(i!=0)
          message+=' ';
        message+=t[i].text;
      }

    message+="'";

    messaget log{message_handler};
    log.error().source_location = source_location;
    log.error() << message << messaget::eom;
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
  declaration                                         [gram.dcl]
  : block.declaration
  | function.definition
  | template.declaration
  | explicit.instantiation
  | explicit.specialization
  | linkage.specification
  | namespace.definition
  | empty.declaration
  | attribute.declaration

  block.declaration
  : simple.declaration
  | asm.definition
  | namespace.alias.definition
  | using.declaration
  | using.directive
  | static_assert.declaration
  | alias.declaration

  C++11 [dcl.dcl] (A.6)
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
  else if(t==TOK_USING)
    return rUsingOrTypedef(item);
  else if(t==TOK_STATIC_ASSERT)
    return rStaticAssert(item.make_static_assert());
  else if(t == TOK_GCC_ASM)
  {
    // top-level asm declaration
    auto statement = rGCCAsmStatement();
    if(!statement.has_value())
      return false;
    item.make_declaration();
    return true;
  }
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
  typedef.declaration                                 [dcl.typedef]
  : TYPEDEF type.specifier declarators ';'

  C++11 [dcl.typedef] (A.6)
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

  for(const auto &declarator : declaration.declarators())
  {
    if(!declarator.name().is_nil())
      add_id(declarator.name(), new_scopet::kindt::TYPEDEF);
  }

  return true;
}

/*
  alias.declaration                                   [dcl.typedef]
  : USING identifier attribute.specifier.seq? '=' type.id ';'

  C++11 [dcl.typedef] (A.6)
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

  declaration.set_is_typedef();
  declaration.type()=typet(ID_typedef);

  if(!is_identifier(lex.get_token(tk)))
    return false;

  cpp_declaratort name;
  name.name()=cpp_namet(tk.data.get(ID_C_base_name));
  name.type().make_nil();

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rTypedefUsing 2\n";
#endif

  if(!optAttribute(declaration.type()))
    return false;

  if(lex.get_token(tk)!='=')
    return false;

  if(!rTypeNameOrFunctionType(type_name))
    return false;

  merge_types(type_name, declaration.type());

  declaration.declarators().push_back(name);

  if(lex.get_token(tk)!=';')
    return false;

  // Register typedef name in the scope
  if(!name.name().is_nil())
    add_id(name.name(), new_scopet::kindt::TYPEDEF);

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rTypedefUsing 3\n";
#endif

  return true;
}

std::optional<codet> Parser::rTypedefStatement()
{
  cpp_declarationt declaration;
  if(!rTypedef(declaration))
    return {};

  return code_frontend_declt(
    static_cast<symbol_exprt &>(static_cast<exprt &>(declaration)));
}

/*
  type.specifier                                      [dcl.type]
  : {cv.qualifier} (simple.type.specifier | class.specifier
    | enum.specifier) {cv.qualifier}

  simple.type.specifier                               [dcl.type.simple]
  : nested.name.specifier? type.name
  | nested.name.specifier TEMPLATE simple.template.id
  | CHAR | CHAR16_T | CHAR32_T | WCHAR_T | BOOL | SHORT | INT | LONG
  | SIGNED | UNSIGNED | FLOAT | DOUBLE | VOID | AUTO
  | decltype.specifier

  C++11 [dcl.type] (A.6)
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

    // C++20 constrained auto: ConceptName auto
    // Drop the concept constraint and use auto for verification.
    if(lex.LookAhead(0) == TOK_AUTO)
    {
      cpp_tokent auto_tk;
      lex.get_token(auto_tk);
      tspec = typet(ID_auto);
      set_location(tspec, auto_tk);
    }
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

  return is_identifier(t) || t == TOK_SCOPE || t == TOK_CONST ||
         t == TOK_VOLATILE || t == TOK_RESTRICT || t == TOK_CHAR ||
         t == TOK_INT || t == TOK_SHORT || t == TOK_LONG || t == TOK_CHAR16_T ||
         t == TOK_CHAR32_T || t == TOK_CHAR8_T || t == TOK_WCHAR_T ||
         t == TOK_COMPLEX // new !!!
         || t == TOK_SIGNED || t == TOK_UNSIGNED || t == TOK_FLOAT ||
         t == TOK_DOUBLE || t == TOK_INT8 || t == TOK_INT16 || t == TOK_INT32 ||
         t == TOK_INT64 || t == TOK_GCC_INT128 || t == TOK_PTR32 ||
         t == TOK_PTR64 || t == TOK_GCC_FLOAT16 || t == TOK_GCC_FLOAT80 ||
         t == TOK_GCC_FLOAT128 || t == TOK_GCC_FLOAT32 ||
         t == TOK_GCC_FLOAT32X || t == TOK_GCC_FLOAT64 ||
         t == TOK_GCC_FLOAT64X || t == TOK_VOID || t == TOK_BOOL ||
         t == TOK_CPROVER_BOOL || t == TOK_CLASS || t == TOK_STRUCT ||
         t == TOK_UNION || t == TOK_ENUM || t == TOK_INTERFACE ||
         t == TOK_TYPENAME || t == TOK_TYPEOF || t == TOK_DECLTYPE ||
         t == TOK_UNDERLYING_TYPE || t == TOK_GCC_BUILTIN_REMOVE_CV ||
         t == TOK_GCC_BUILTIN_REMOVE_REFERENCE ||
         t == TOK_GCC_BUILTIN_REMOVE_CVREF || t == TOK_ATOMIC_TYPE_SPECIFIER;
}

/*
  linkage.specification                               [dcl.link]
  : EXTERN string.literal declaration
  | EXTERN string.literal '{' declaration.seq? '}'

  C++11 [dcl.link] (A.6)
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
  namespace.definition                                [namespace.def]
  : INLINE? NAMESPACE identifier? '{' namespace.body '}'
  | NAMESPACE identifier '=' qualified.namespace.specifier ';'

  C++11 [namespace.def] (A.6)
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

  // Tolerate __attribute__ before the namespace name, as used by libc++:
  // namespace __attribute__((__type_visibility__("default"))) std { }
  typet discard;
  if(!optAttribute(discard))
    return false;

  // namespace might be anonymous
  if(lex.LookAhead(0) != '{')
  {
    if(is_identifier(lex.get_token(tk2)))
      name=tk2.data.get(ID_C_base_name);
    else
      return false;
  }

  namespace_spec=cpp_namespace_spect();
  set_location(namespace_spec, tk1);
  namespace_spec.set_namespace(name);
  namespace_spec.set_is_inline(is_inline);

  // C++17: nested namespace definition (namespace A::B::C { })
  // Build nested namespace_spec nodes for each component.
  if(lex.LookAhead(0) == TOK_SCOPE)
  {
    // Parse the rest of the nested name
    std::vector<irep_idt> names;
    names.push_back(name);
    while(lex.LookAhead(0) == TOK_SCOPE)
    {
      lex.get_token(tk2); // eat ::

      // Check for inline nested namespace (C++20, but tolerate)
      if(lex.LookAhead(0) == TOK_INLINE)
        lex.get_token(tk2);

      if(!is_identifier(lex.LookAhead(0)))
        return false;
      lex.get_token(tk2);
      names.push_back(tk2.data.get(ID_C_base_name));
    }

    // Build nested structure from inside out
    // namespace A::B::C { body } becomes
    // namespace A { namespace B { namespace C { body } } }
    cpp_namespace_spect *current = &namespace_spec;
    for(std::size_t i = 1; i < names.size(); i++)
    {
      current->items().push_back(cpp_itemt());
      cpp_namespace_spect &inner =
        current->items().back().make_namespace_spec();
      inner = cpp_namespace_spect();
      set_location(inner, tk1);
      inner.set_namespace(names[i]);
      current = &inner;
    }

    if(lex.LookAhead(0) != '{')
      return false;
    return rLinkageBody(current->items());
  }

  // Tolerate __attribute__ after the namespace name, as used by glibc:
  // inline namespace __cxx11 __attribute__((__abi_tag__ ("cxx11"))) { }
  if(!optAttribute(discard))
    return false;

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
  using.declaration                                   [namespace.udecl]
  : USING TYPENAME? nested.name.specifier unqualified.id ';'
  | USING '::' unqualified.id ';'

  using.directive                                     [namespace.udir]
  : attribute.specifier.seq? USING NAMESPACE nested.name.specifier?
    namespace.name ';'

  C++11 [namespace.udecl], [namespace.udir] (A.6)
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

  // C++20 using enum: parse and treat as no-op for now
  if(lex.LookAhead(0) == TOK_ENUM)
  {
    lex.get_token(tk);
    if(!rName(cpp_using.name()))
      return false;
    if(lex.get_token(tk) != ';')
      return false;
    return true;
  }

  if(!rName(cpp_using.name()))
    return false;

  // We will eventually need to record this attribute as Clang's
  // __using_if_exists__ affects type checking.
  typet discard;
  if(!optAttribute(discard))
    return false;

  if(lex.get_token(tk)!=';')
    return false;

  return true;
}

/*
  alias.declaration | using.declaration               [dcl.typedef]
  : USING identifier attribute.specifier.seq? '=' type.id ';'
  | using.declaration

  C++11 [dcl.typedef], [namespace.udecl] (A.6)
*/
bool Parser::rUsingOrTypedef(cpp_itemt &item)
{
  cpp_token_buffert::post pos = lex.Save();

  cpp_tokent tk;
  if(lex.get_token(tk) != TOK_USING)
    return false;

  typet discard;
  if(
    is_identifier(lex.get_token(tk)) && optAttribute(discard) &&
    lex.LookAhead(0) == '=')
  {
    lex.Restore(pos);
    return rTypedefUsing(item.make_declaration());
  }

  lex.Restore(pos);
  return rUsing(item.make_using());
}

/*
  static_assert.declaration                           [dcl.dcl]
  : STATIC_ASSERT '(' constant.expression ',' string.literal ')' ';'

  C++11 [dcl.dcl] (A.6)
*/
bool Parser::rStaticAssert(cpp_static_assertt &cpp_static_assert)
{
  cpp_tokent tk;

  if(lex.get_token(tk)!=TOK_STATIC_ASSERT)
    return false;

  if(lex.get_token(tk)!='(')
    return false;

  exprt cond;

  if(!rExpression(cond, false))
    return false;

  exprt description;

  // C++17: message is optional
  if(lex.LookAhead(0) == ',')
  {
    lex.get_token(tk);
    if(!rExpression(description, false))
      return false;
  }
  else
  {
    description = exprt(ID_string_constant);
    description.set(ID_value, "");
  }

  if(lex.get_token(tk)!=')')
    return false;

  if(lex.get_token(tk)!=';')
    return false;

  cpp_static_assert =
    cpp_static_assertt(std::move(cond), std::move(description));
  set_location(cpp_static_assert, tk);

  return true;
}

/*
  linkage.body : '{' declaration.seq? '}'             [dcl.link]

  Also used for namespace.body.

  C++11 [dcl.link] (A.6)
*/
bool Parser::rLinkageBody(cpp_linkage_spect::itemst &items)
{
  cpp_tokent op, cp;

  if(lex.get_token(op)!='{')
    return false;

  items.clear();
  while(lex.LookAhead(0)!='}')
  {
    if(lex.LookAhead(0) == '\0')
      return false;

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
  template.declaration                                [temp]
  : TEMPLATE '<' template.parameter.list '>' declaration
  | TEMPLATE declaration                              (explicit instantiation)
  | TEMPLATE '<' '>' declaration                      (explicit specialization)

  C++11 [temp] (A.12)
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
  else if(lex.LookAhead(0) == TOK_CONCEPT)
  {
    // C++20 concept: template<...> concept Name = expr;
    // Parse as constexpr bool variable for verification purposes.
    cpp_tokent concept_tk;
    lex.get_token(concept_tk);

    cpp_tokent name_tk;
    if(!is_identifier(lex.get_token(name_tk)))
      return false;

    if(lex.get_token(concept_tk) != '=')
      return false;

    exprt constraint;
    if(!rExpression(constraint, false))
      return false;

    if(lex.get_token(concept_tk) != ';')
      return false;

    // Build as: constexpr bool Name = expr;
    body.type() = typet(ID_bool);
    body.storage_spec().set_constexpr();
    cpp_declaratort declarator;
    declarator.name() = cpp_namet(name_tk.data.get(ID_C_base_name));
    set_location(declarator.name(), name_tk);
    declarator.value() = constraint;
    body.declarators().push_back(declarator);
  }
  else
  {
    // C++20 leading requires clause: skip
    if(lex.LookAhead(0) == TOK_REQUIRES)
    {
      cpp_tokent req_tk;
      lex.get_token(req_tk);
      if(lex.LookAhead(0) == '(')
      {
        lex.get_token(req_tk);
        int depth = 1;
        while(depth > 0)
        {
          int t = lex.get_token(req_tk);
          if(t == '(')
            ++depth;
          else if(t == ')')
            --depth;
          else if(t == 0)
            return false;
        }
      }
    }

    if(!rDeclaration(body))
      return false;
  }

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

  case num_tdks:
  case tdk_unknown:
    UNREACHABLE;
    break;
  }

  // Register variable template names so the parser can disambiguate
  // name<args> as template arguments rather than less-than comparison.
  // Skip class templates, function templates, and qualified names
  // (out-of-class static member definitions).
  if(
    (kind == tdk_decl || kind == tdk_specialization) &&
    !decl.is_class_template() && !decl.declarators().empty() &&
    decl.declarators().front().type().id() != ID_function_type &&
    !decl.declarators().front().name().is_qualified())
  {
    const auto &dname = decl.declarators().front().name();
    irep_idt base = dname.get_base_name();
    if(
      base != irep_idt() && lookup_id(base) == nullptr &&
      current_scope->parent != nullptr)
    {
      auto &entry = current_scope->parent->id_map[base];
      entry.kind = new_scopet::kindt::VARIABLE_TEMPLATE;
    }
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

  // merge nested template parameters (e.g., template<T> template<U>)
  while(lex.LookAhead(0)==TOK_TEMPLATE)
  {
    lex.get_token(tk);
    if(lex.LookAhead(0)!='<')
      break;

    lex.get_token(tk);
    irept inner_args;
    if(!rTempArgList(inner_args))
      return false;

    if(lex.get_token(tk)!='>')
      return false;

    for(auto &sub : inner_args.get_sub())
      template_parameters.get_sub().push_back(sub);
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
  template.parameter.list                             [temp.param]
  : template.parameter
  | template.parameter.list ',' template.parameter

  C++11 [temp.param] (A.12)
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
  template.parameter                                  [temp.param]
  : type.parameter
  | parameter.declaration

  type.parameter
  : CLASS '...'? identifier?
  | CLASS identifier? '=' type.id
  | TYPENAME '...'? identifier?
  | TYPENAME identifier? '=' type.id
  | TEMPLATE '<' template.parameter.list '>' CLASS '...'? identifier?
  | TEMPLATE '<' template.parameter.list '>' CLASS identifier? '=' id.expression

  C++11 [temp.param] (A.12)
*/
bool Parser::rTempArgDeclaration(cpp_declarationt &declaration)
{
#ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rTempArgDeclaration 0\n";
#endif

  int t0=lex.LookAhead(0);

  // C++20: concept-constrained parameter, e.g. template<Integral T>
  // Treat as typename T (ignore the constraint for verification).
  // Only match if the first identifier is NOT a known template parameter
  // (to avoid misinterpreting template<typename Ty, Ty V>).
  if(
    cpp20 && is_identifier(t0) &&
    (is_identifier(lex.LookAhead(1)) || lex.LookAhead(1) == TOK_ELLIPSIS))
  {
    cpp_token_buffert::post pos = lex.Save();

    cpp_tokent concept_tk;
    lex.get_token(concept_tk);

    irep_idt first_name = concept_tk.data.get(ID_C_base_name);
    auto *id_entry = lookup_id(first_name);
    bool is_known_type =
      id_entry != nullptr &&
      (id_entry->kind == new_scopet::kindt::TYPE_TEMPLATE_PARAMETER ||
       id_entry->kind == new_scopet::kindt::TYPEDEF ||
       id_entry->kind == new_scopet::kindt::TAG);

    if(!is_known_type)
    {
      declaration = cpp_declarationt();
      set_location(declaration, concept_tk);
      declaration.set(ID_is_type, true);
      declaration.type() = typet("cpp-template-type");

      declaration.declarators().resize(1);
      cpp_declaratort &declarator = declaration.declarators().front();
      declarator = cpp_declaratort();
      declarator.name().make_nil();
      declarator.type().make_nil();
      set_location(declarator, concept_tk);

      if(lex.LookAhead(0) == TOK_ELLIPSIS)
      {
        cpp_tokent ellipsis_tk;
        lex.get_token(ellipsis_tk);
        declarator.set_has_ellipsis();
      }

      if(is_identifier(lex.LookAhead(0)))
      {
        cpp_tokent name_tk;
        lex.get_token(name_tk);
        declarator.name() = cpp_namet(name_tk.data.get(ID_C_base_name));
        set_location(declarator.name(), name_tk);
        add_id(declarator.name(), new_scopet::kindt::TYPE_TEMPLATE_PARAMETER);
      }

      if(
        lex.LookAhead(0) == '=' || lex.LookAhead(0) == ',' ||
        lex.LookAhead(0) == '>')
      {
        if(lex.LookAhead(0) == '=')
        {
          cpp_tokent eq_tk;
          lex.get_token(eq_tk);
          typet default_type;
          if(!rTypeName(default_type))
          {
            lex.Restore(pos);
            t0 = lex.LookAhead(0);
          }
          else
          {
            declarator.value() = exprt(ID_type);
            declarator.value().type().swap(default_type);
            return true;
          }
        }
        else
          return true;
      }
      else
      {
        lex.Restore(pos);
        t0 = lex.LookAhead(0);
      }
    }
    else
    {
      lex.Restore(pos);
      t0 = lex.LookAhead(0);
    }
  }

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

    if(lex.LookAhead(0)==TOK_ELLIPSIS)
    {
      cpp_tokent tk2;
      lex.get_token(tk2);
      declarator.set_has_ellipsis();
    }

    if(is_identifier(lex.LookAhead(0)))
    {
      cpp_tokent tk2;
      lex.get_token(tk2);

      declarator.name() = cpp_namet(tk2.data.get(ID_C_base_name));
      set_location(declarator.name(), tk2);

      add_id(declarator.name(), new_scopet::kindt::TYPE_TEMPLATE_PARAMETER);
    }

    if(lex.LookAhead(0)=='=')
    {
      if(declarator.get_has_ellipsis())
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

    cpp_tokent tk1;

    if(lex.get_token(tk1) != TOK_CLASS)
      return false;

    declaration = cpp_declarationt();
    set_location(declaration, tk1);

    declaration.set(ID_is_type, true);
    declaration.type() = template_type;

    declaration.declarators().resize(1);
    cpp_declaratort &declarator = declaration.declarators().front();

    declarator = cpp_declaratort();
    declarator.name().make_nil();
    declarator.type().make_nil();
    set_location(declarator, tk1);

    if(lex.LookAhead(0) == ',' || lex.LookAhead(0) == '>')
      return true;

    if(lex.LookAhead(0) == TOK_ELLIPSIS)
    {
      cpp_tokent tk2;
      lex.get_token(tk2);
      declarator.set_has_ellipsis();
    }

    if(is_identifier(lex.LookAhead(0)))
    {
      cpp_tokent tk2;
      lex.get_token(tk2);

      declarator.name() = cpp_namet(tk2.data.get(ID_C_base_name));
      set_location(declarator.name(), tk2);

      add_id(declarator.name(), new_scopet::kindt::TYPE_TEMPLATE_PARAMETER);
    }
    else
      return false;

    if(lex.LookAhead(0)=='=')
    {
      if(declarator.get_has_ellipsis())
        return false;

      typet default_type;

      lex.get_token(tk1);
      if(!rTypeName(default_type))
        return false;

      declarator.value() = exprt(ID_type);
      declarator.value().type().swap(default_type);
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

    declaration.declarators().resize(1);
    cpp_declaratort &declarator = declaration.declarators().front();

    if(lex.LookAhead(0)==TOK_ELLIPSIS)
    {
      cpp_tokent tk2;
      lex.get_token(tk2);
      declarator.set_has_ellipsis();
    }

    if(!rDeclarator(declarator, kArgDeclarator, true, false))
      return false;

#ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::rTempArgDeclaration 4\n";
#endif

    add_id(declarator.name(), new_scopet::kindt::NON_TYPE_TEMPLATE_PARAMETER);

    exprt &value=declarator.value();

    if(lex.LookAhead(0)=='=')
    {
      if(declarator.get_has_ellipsis())
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
  explicit.instantiation                              [temp.explicit]
  : EXTERN TEMPLATE declaration

  C++11 [temp.explicit] (A.12)
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

  // Mark as extern so the type-checker can skip it.
  decl.storage_spec().set_extern();

  return true;
}

/*
  simple.declaration                                  [dcl.dcl]
  : decl.specifier.seq? init.declarator.list? ';'
  | attribute.specifier.seq decl.specifier.seq? init.declarator.list ';'

  function.definition                                 [dcl.fct.def]
  : attribute.specifier.seq? decl.specifier.seq? declarator
    virt.specifier.seq? function.body

  The parser splits declarations into three cases:
  - integral.declaration: decl-specifier-seq starts with an integral type
    or class/enum specifier
  - const.declaration: starts with cv-qualifier followed by '*' or identifier
  - other.declaration: decl-specifier-seq starts with a name (user-defined type)

  Note: if you modify this function, look at declaration.statement, too.
  Note: this regards a statement like "T (a);" as a constructor
        declaration.  See isConstructorDecl().

  C++11 [dcl.dcl], [dcl.fct.def] (A.6, A.7)
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

  // C++11 [dcl.align]: alignas is an alignment-specifier, part of
  // attribute-specifier-seq
  if(!optAlignas(declaration.type()))
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

  if(member_spec.is_empty())
    if(!optMemberSpec(member_spec))
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
              << '\n';
#endif

    if(
      cv_q.is_not_nil() &&
      ((is_identifier(t) && lex.LookAhead(1) == '=') || t == '*'))
    {
      return rConstDeclaration(declaration);
    }
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

  // C++20 constrained auto: ConceptName auto
  if(integral.is_not_nil() && lex.LookAhead(0) == TOK_AUTO)
  {
    cpp_tokent auto_tk;
    lex.get_token(auto_tk);
    integral = typet(ID_auto);
    set_location(integral, auto_tk);
  }

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
            << static_cast<char>(lex.LookAhead(0)) << '\n';
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
    std::cout << std::string(__indent, ' ') << "Parser::rIntegralDeclaration 6 "
              << lex.LookAhead(0) << '\n';
#endif

    if(!rDeclarators(declaration.declarators(), true))
      return false;

    // handle trailing return type
    if(
      declaration.type().id() == ID_auto &&
      declaration.declarators().size() == 1 &&
      declaration.declarators().front().type().id() == ID_function_type &&
      declaration.declarators().front().type().add_subtype().is_not_nil())
    {
      declaration.type() =
        to_type_with_subtype(declaration.declarators().front().type())
          .subtype();
      declaration.declarators().front().type().add_subtype().make_nil();
    }

#ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::rIntegralDeclaration 7\n";
#endif

    if(!declaration.declarators().empty())
    {
      if(!rContractAttributes(declaration.declarators().front().type()))
        return false;
    }

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

  // C++20 constrained auto: ConceptName auto
  if(lex.LookAhead(0) == TOK_AUTO)
  {
    cpp_tokent auto_tk;
    lex.get_token(auto_tk);
    type_name = typet(ID_auto);
    set_location(type_name, auto_tk);
  }

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

    DATA_INVARIANT(!type_name.get_sub().empty(), "type name details expected");

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

    DATA_INVARIANT(!type_name.get_sub().empty(), "type name details expected");

    bool is_destructor=false;
    for(const auto &irep : type_name.get_sub())
    {
      if(irep.id() == "~")
      {
        is_destructor=true;
        break;
      }
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

  if(!declaration.declarators().empty())
  {
    if(!rContractAttributes(declaration.declarators().front().type()))
      return false;
  }

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
            << lex.LookAhead(0) << "  " << lex.LookAhead(1) << '\n';
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
    else if(is_identifier(t))
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
  ptr.to.member (lookahead check)                     [dcl.mptr]
  : '::'? (identifier template.args? '::')+ '*'

  C++11 [dcl.mptr] (A.7)
*/
bool Parser::isPtrToMember(int i)
{
  int t0=lex.LookAhead(i++);

  if(t0==TOK_SCOPE)
      t0=lex.LookAhead(i++);

  while(is_identifier(t0))
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
  function.specifier                                  [dcl.fct.spec]
  : INLINE | VIRTUAL | EXPLICIT

  Also handles FRIEND, which is a decl-specifier.

  C++11 [dcl.fct.spec] (A.6)
*/
bool Parser::optMemberSpec(cpp_member_spect &member_spec)
{
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
    case TOK_EXPLICIT:
      member_spec.set_explicit(true);
      // C++20 explicit(expr): skip the condition
      if(lex.LookAhead(0) == '(')
      {
        cpp_tokent op;
        lex.get_token(op);
        exprt discarded;
        if(!rExpression(discarded, false))
          return false;
        if(lex.get_token(op) != ')')
          return false;
      }
      break;
    default: UNREACHABLE;
    }

    // Skip __attribute__((...)) between member specifiers
    {
      typet discard;
      discard.make_nil();
      if(!optAttribute(discard))
        return false;
    }

    t=lex.LookAhead(0);
  }

  return true;
}

/*
  storage.class.specifier                             [dcl.stc]
  : REGISTER | STATIC | THREAD_LOCAL | EXTERN | MUTABLE

  Also handles CONSTEXPR, which is a decl-specifier per C++11 [dcl.spec].

  C++11 [dcl.stc] (A.6)
*/
bool Parser::optStorageSpec(cpp_storage_spect &storage_spec)
{
  int t=lex.LookAhead(0);

  if(
    t == TOK_STATIC || t == TOK_EXTERN || (t == TOK_AUTO && !cpp11) ||
    t == TOK_REGISTER || t == TOK_MUTABLE || t == TOK_GCC_ASM ||
    t == TOK_THREAD_LOCAL || t == TOK_CONSTEXPR || t == TOK_CONSTEVAL ||
    t == TOK_CONSTINIT)
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
    case TOK_CONSTEXPR:
      storage_spec.set_constexpr();
      break;
    // C++20 consteval/constinit: treat as constexpr for verification
    case TOK_CONSTEVAL:
    case TOK_CONSTINIT:
      storage_spec.set_constexpr();
      break;
    default: UNREACHABLE;
    }

    set_location(storage_spec, tk);
  }

  return true;
}

/*
  cv.qualifier.seq                                    [dcl.type.cv]
  : (CONST | VOLATILE)+

  Also accepts RESTRICT as a GCC extension.

  C++11 [dcl.type.cv] (A.6): constexpr is a decl-specifier, handled by
  optStorageSpec.
*/
bool Parser::optCvQualify(typet &cv)
{
  for(;;)
  {
    int t=lex.LookAhead(0);
    if(
      t == TOK_CONST || t == TOK_VOLATILE || t == TOK_RESTRICT ||
      t == TOK_PTR32 || t == TOK_PTR64 || t == TOK_GCC_ATTRIBUTE ||
      t == TOK_GCC_ASM || t == TOK_ATOMIC_TYPE_QUALIFIER)
    {
      cpp_tokent tk;
      lex.get_token(tk);
      typet p;

      switch(t)
      {
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
        if(!rGCCAttribute(cv))
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

      case TOK_ATOMIC_TYPE_QUALIFIER:
        // C11 _Atomic qualifier — ignore in C++ mode
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
  alignment.specifier                                 [dcl.align]
  : ALIGNAS '(' type.id '...'? ')'
  | ALIGNAS '(' assignment.expression '...'? ')'

  C++11 [dcl.align] (A.6)
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
  lex.get_token(op);
  cpp_token_buffert::post pos = lex.Save();

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

bool Parser::rGCCAttribute(typet &t)
{
#ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rGCCAttribute "
            << lex.LookAhead(0);
#endif
  cpp_tokent tk;
  lex.get_token(tk);

  switch(tk.kind)
  {
  case '(':
    if(lex.LookAhead(0)!=')')
      rGCCAttribute(t);

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

      type_with_subtypet attr(ID_frontend_vector, uninitialized_typet{});
      attr.set(ID_size, exp);
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
      attr.set(ID_size, to_cpp_name(name).get_base_name());
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

  return rGCCAttribute(t);
}

bool Parser::optAttribute(typet &t)
{
  // C++11 [dcl.attr] (A.6): attribute-specifier-seq is zero or more
  // attribute-specifiers.
  while(lex.LookAhead(0) == TOK_GCC_ATTRIBUTE)
  {
    lex.get_token();

    if(!rGCCAttribute(t))
      return false;
  }

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
      if(lex.LookAhead(0) != ']')
        return false;
      lex.get_token();
      return true;

    case TOK_NORETURN:
      {
        typet attr(ID_noreturn);
        set_location(attr, tk);
        merge_types(attr, t);
        break;
      }

      case TOK_NODISCARD:
      {
        typet attr(ID_nodiscard);
        set_location(attr, tk);
        merge_types(attr, t);
        break;
      }

    default:
        // TODO: we may wish to change this: GCC, Clang, Visual Studio merely
        // warn when they see an attribute that they don't recognize
        if(is_identifier(tk.kind) && lex.LookAhead(0) == TOK_SCOPE)
        {
        // scoped attribute like clang::something
        exprt discarded;
        if(!rExpression(discarded, false))
          return false;
        }
        else
        return false;
    }
  }
}

/*
  simple.type.specifier (integral types)              [dcl.type.simple]
  : (CHAR | CHAR16_T | CHAR32_T | WCHAR_T | INT | SHORT | LONG
     | SIGNED | UNSIGNED | FLOAT | DOUBLE | VOID | BOOL | COMPLEX)+
  | class.specifier
  | enum.specifier

  C++11 [dcl.type.simple] (A.6).  Note: if editing this, see also
  isTypeSpecifier().
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
    case TOK_CHAR8_T:
    {
        // char8_t is unsigned char in C++20
        cpp_tokent tk;
        lex.get_token(tk);
        typet unsigned_kw(ID_unsigned);
        set_location(unsigned_kw, tk);
        merge_types(unsigned_kw, p);
        typet char_kw(ID_char);
        set_location(char_kw, tk);
        merge_types(char_kw, p);
        is_integral = true;
        continue;
    }
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
    case TOK_GCC_FLOAT16:
      type_id = ID_gcc_float16;
      break;
    case TOK_GCC_FLOAT80: type_id=ID_gcc_float80; break;
    case TOK_GCC_FLOAT128: type_id=ID_gcc_float128; break;
    case TOK_GCC_FLOAT32:
      type_id = ID_gcc_float32;
      break;
    case TOK_GCC_FLOAT32X:
      type_id = ID_gcc_float32x;
      break;
    case TOK_GCC_FLOAT64:
      type_id = ID_gcc_float64;
      break;
    case TOK_GCC_FLOAT64X:
      type_id = ID_gcc_float64x;
      break;
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

    // C++14: decltype(auto)
    if(lex.LookAhead(0) == TOK_AUTO)
    {
      lex.get_token(tk);
      if(lex.get_token(tk) != ')')
        return false;
      p.set("#auto", true);
      return true;
    }

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
  else if(
    t == TOK_GCC_BUILTIN_REMOVE_CV || t == TOK_GCC_BUILTIN_REMOVE_REFERENCE ||
    t == TOK_GCC_BUILTIN_REMOVE_CVREF)
  {
    cpp_tokent tk;
    lex.get_token(tk);

    if(t == TOK_GCC_BUILTIN_REMOVE_CV)
      p = typet(ID_remove_cv);
    else if(t == TOK_GCC_BUILTIN_REMOVE_REFERENCE)
      p = typet(ID_remove_reference);
    else
      p = typet(ID_remove_cvref);

    set_location(p, tk);

    if(lex.get_token(tk) != '(')
      return false;

    typet tname;
    if(!rTypeName(tname))
      return false;

    if(lex.get_token(tk) != ')')
      return false;

    p.add(ID_type_arg).swap(tname);

    return true;
  }
  else if(
    t == TOK_ATOMIC_TYPE_SPECIFIER ||
    (is_identifier(t) && lex.LookAhead(1) == '(' &&
     [&]
     {
       cpp_tokent peek;
       lex.LookAhead(0, peek);
       return peek.data.get(ID_C_base_name) == "_Atomic";
     }()))
  {
    // C11 _Atomic(T) — parse and treat as T in C++ mode
    cpp_tokent tk;
    lex.get_token(tk);

    if(lex.get_token(tk) != '(')
      return false;

    if(!rTypeName(p))
      return false;

    if(lex.get_token(tk) != ')')
      return false;

    return true;
  }
  else
  {
    p.make_nil();
    return true;
  }
}

/*
  parameters.and.qualifiers                           [dcl.fct]
  : '(' parameter.declaration.clause ')' cv.qualifier.seq?
    ref.qualifier? exception.specification? attribute.specifier.seq?

  Also handles member.initializers and trailing.return.type.

  function.body                                       [dcl.fct.def]
  : ctor.initializer? compound.statement
  | function.try.block
  | '=' DEFAULT ';'
  | '=' DELETE ';'

  C++11 [dcl.fct], [dcl.fct.def] (A.7)
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
  constructor.type().add_subtype().make_nil();
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

  // C++11 [dcl.fct]: optional ref-qualifier (& or &&)
  if(lex.LookAhead(0) == '&')
  {
    cpp_tokent tk;
    lex.get_token(tk);
  }
  else if(lex.LookAhead(0) == TOK_ANDAND)
  {
    cpp_tokent tk;
    lex.get_token(tk);
  }

  optThrowDecl(constructor.throw_decl());

  // GCC __attribute__ after noexcept
  if(lex.LookAhead(0) == TOK_GCC_ATTRIBUTE)
  {
    cpp_tokent tk;
    lex.get_token(tk);
    // consume (( ... ))
    if(lex.LookAhead(0) == '(')
    {
      lex.get_token(tk);
      int depth = 1;
      while(depth > 0)
      {
        lex.get_token(tk);
        if(tk.kind == '(')
          ++depth;
        else if(tk.kind == ')')
          --depth;
        else if(tk.kind == '\0')
          return false;
      }
    }
  }

  if(lex.LookAhead(0)==TOK_ARROW)
  {
#ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rConstructorDecl 3\n";
#endif

    // C++11 trailing return type: -> trailing-type-specifier-seq
    //   abstract-declarator?
    cpp_tokent arrow;
    lex.get_token(arrow);

    if(!rTypeName(trailing_return_type))
      return false;
  }

  // C++11 virt-specifier-seq: override, final
  for(;;)
  {
    cpp_tokent virt_tk;
    if(!is_identifier(lex.LookAhead(0)))
      break;
    lex.LookAhead(0, virt_tk);
    if(virt_tk.text == "override" || virt_tk.text == "final")
      lex.get_token(virt_tk);
    else
      break;
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
        if(!cpp11)
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
        if(!cpp11)
        {
          SyntaxError();
          return false;
        }

        constructor.value()=codet(ID_cpp_delete);
        set_location(constructor.value(), value);

        // C++26 = delete("message") — skip optional message
        if(lex.LookAhead(0) == '(')
        {
          cpp_tokent lp, msg, rp;
          lex.get_token(lp);
          lex.get_token(msg); // string literal
          if(lex.get_token(rp) != ')')
          return false;
        }
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
  exception.specification                             [except.spec]
  : dynamic.exception.specification
  | noexcept.specification

  dynamic.exception.specification
  : THROW '(' type.id.list? ')'

  type.id.list
  : type.id '...'?
  | type.id.list ',' type.id '...'?

  noexcept.specification
  : NOEXCEPT '(' constant.expression ')'
  | NOEXCEPT

  C++11 [except.spec] (A.13)
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
    lex.get_token(tk);

    if(lex.LookAhead(0) == '(')
    {
      // noexcept(constant-expression)
      cpp_tokent op, cp;
      lex.get_token(op);

      exprt expr;
      if(!rCommaExpression(expr))
        return false;

      if(lex.get_token(cp) != ')')
        return false;

      p = irept(ID_noexcept);
      p.add(ID_value).swap(expr);
    }
    else
    {
      // bare noexcept (equivalent to noexcept(true))
      p = irept(ID_noexcept);
    }
  }

  throw_decl=p;
  return true;
}

/*
  init.declarator.list                                [dcl.decl]
  : init.declarator
  | init.declarator.list ',' init.declarator

  is_statement changes the behavior of rArgDeclListOrInit().

  C++11 [dcl.decl] (A.7)
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
  init.declarator                                     [dcl.decl]
  : declarator initializer?

  initializer                                         [dcl.init]
  : brace.or.equal.initializer
  | '(' expression.list ')'

  brace.or.equal.initializer
  : '=' initializer.clause
  | braced.init.list

  Also handles bit-field declarations: ':' constant.expression

  C++11 [dcl.decl], [dcl.init] (A.7)
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
    bit_field_type.add_subtype().make_nil();
    set_location(bit_field_type, tk);

    dw.type() = std::move(bit_field_type);

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
        if(!cpp11)
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
        if(!cpp11)
        {
          SyntaxError();
          return false;
        }

        lex.get_token(tk);
        declarator.value()=codet(ID_cpp_delete);
        set_location(declarator.value(), tk);

        // C++26 = delete("message") — skip optional message
        if(lex.LookAhead(0) == '(')
        {
          cpp_tokent lp, msg, rp;
          lex.get_token(lp);
          lex.get_token(msg); // string literal
          if(lex.get_token(rp) != ')')
            return false;
        }
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
      bit_field_type.add_subtype().make_nil();
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
  declarator                                          [dcl.decl]
  : ptr.declarator
  | noptr.declarator parameters.and.qualifiers trailing.return.type

  ptr.declarator
  : noptr.declarator
  | ptr.operator ptr.declarator

  noptr.declarator
  : declarator.id attribute.specifier.seq?
  | noptr.declarator parameters.and.qualifiers
  | noptr.declarator '[' expression? ']' attribute.specifier.seq?
  | '(' ptr.declarator ')'

  Note: We assume that '(' declarator ')' is followed by '(' or '['.
        This is to avoid accepting a function call F(x) as a pair of
        a type F and a declarator x.  This assumption is ignored
        if should_be_declarator is true.

  Note: is_statement changes the behavior of rArgDeclListOrInit().

  C++11 [dcl.decl] (A.7)
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

  if(lex.LookAhead(0) == TOK_ELLIPSIS && lex.LookAhead(1) != ')')
  {
    cpp_tokent tk;
    lex.get_token(tk);
    d_outer.set(ID_ellipsis, true);
  }

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
  else if(
    kind != kCastDeclarator &&
    (kind == kDeclarator || is_identifier(t) || t == TOK_SCOPE))
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
        function_type.add_subtype().swap(d_outer);
        function_type.add(ID_parameters).swap(args);

        // C++23 deducing this: check if first parameter has
        // explicit_this
        {
          const auto &params = function_type.find(ID_parameters).get_sub();
          if(!params.empty() && params.front().get_bool("explicit_this"))
          {
            function_type.set("explicit_this", true);
          }
        }

        // cv-qualifiers and ref-qualifier go on the function type
        // before it's nested into the declarator
        {
          typet cv_tmp;
          cv_tmp.make_nil();
          optCvQualify(cv_tmp);
          if(cv_tmp.is_not_nil())
            merge_types(cv_tmp, method_qualifier);
        }

        // C++11 [dcl.fct]: optional ref-qualifier (& or &&)
        if(lex.LookAhead(0) == '&')
        {
          cpp_tokent rq;
          lex.get_token(rq);
          function_type.set(ID_C_ref_qualifier, "&");
        }
        else if(lex.LookAhead(0) == TOK_ANDAND)
        {
          cpp_tokent rq;
          lex.get_token(rq);
          function_type.set(ID_C_ref_qualifier, "&&");
        }

        // make this subtype of d_inner
        make_subtype(function_type, d_inner);
        d_outer.swap(d_inner);
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
      optThrowDecl(throw_decl);

      // C++17: store noexcept as annotation on the function type.
      // Uses #C_noexcept (comment prefix) so it doesn't affect type
      // equality but is used by cpp_type2name for template specialization
      // naming.
      if(throw_decl.id() == ID_noexcept)
      {
        // Check if noexcept(false)
        bool is_noexcept = true;
        if(throw_decl.find(ID_value).is_not_nil())
        {
          const exprt &val =
            static_cast<const exprt &>(throw_decl.find(ID_value));
          if(val.id() == ID_typecast && val.has_operands())
          {
            const auto &inner = val.operands().front();
            if(inner.id() == ID_constant && inner.get(ID_value) == ID_false)
                is_noexcept = false;
          }
          else if(
            val.id() == ID_constant &&
            (val.get(ID_value) == ID_false || val.get(ID_value) == "0"))
          {
            is_noexcept = false;
          }
        }

        if(is_noexcept)
        {
          typet *p = &d_outer;
          while(p->is_not_nil() && p->id() != ID_function_type)
            p = &p->add_subtype();
          if(p->id() == ID_function_type)
            p->set("#C_noexcept", true);
        }
      }

      // GCC __attribute__ after noexcept
      if(lex.LookAhead(0) == TOK_GCC_ATTRIBUTE)
      {
        cpp_tokent tk;
        lex.get_token(tk);
        if(lex.LookAhead(0) == '(')
        {
          lex.get_token(tk);
          int depth = 1;
          while(depth > 0)
          {
            lex.get_token(tk);
            if(tk.kind == '(')
                ++depth;
            else if(tk.kind == ')')
                --depth;
            else if(tk.kind == '\0')
                return false;
          }
        }
      }

      if(lex.LookAhead(0)==TOK_ARROW)
      {
#ifdef DEBUG
        std::cout << std::string(__indent, ' ') << "Parser::rDeclarator2 10\n";
#endif

        // C++11 trailing return type, but we already have
        // a return type. We should report this as an error.
        cpp_tokent arrow;
        lex.get_token(arrow);

        // C++11 trailing return type: -> trailing-type-specifier-seq
        //   abstract-declarator?
        typet return_type;
        if(!rTypeName(return_type))
          return false;

        if(d_outer.add_subtype().is_not_nil())
          return false;

        d_outer.add_subtype().swap(return_type);
      }

      // C++11 virt-specifier-seq: override, final
      for(;;)
      {
        cpp_tokent virt_tk;
        if(!is_identifier(lex.LookAhead(0)))
          break;
        lex.LookAhead(0, virt_tk);
        if(virt_tk.text == "override" || virt_tk.text == "final")
          lex.get_token(virt_tk);
        else
          break;
      }

      // C++20 trailing requires clause: skip
      if(lex.LookAhead(0) == TOK_REQUIRES)
      {
        cpp_tokent req_tk;
        lex.get_token(req_tk);
        if(lex.LookAhead(0) == '(')
        {
          lex.get_token(req_tk);
          int depth = 1;
          while(depth > 0)
          {
            int t = lex.get_token(req_tk);
            if(t == '(')
                ++depth;
            else if(t == ')')
                --depth;
            else if(t == 0)
                return false;
          }
        }
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
        tl.push_back(tl.back().add_subtype());
      }

      array_typet array_type(tl.back(), expr);
      tl.pop_back();
      d_outer.swap(array_type);
      while(!tl.empty())
      {
        tl.back().add_subtype().swap(d_outer);
        d_outer.swap(tl.back());
        tl.pop_back();
      }
    }
    else
      break;
  }

  optCvQualify(d_outer);
  if(d_outer.is_not_nil() && !d_outer.has_subtypes())
  {
    merged_typet merged_type;
    merged_type.move_to_subtypes(d_outer);
    typet nil;
    nil.make_nil();
    merged_type.move_to_sub(nil);
    d_outer.swap(merged_type);
  }

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
  ptr.operator                                        [dcl.decl]
  : '*' attribute.specifier.seq? cv.qualifier.seq?
  | '&' attribute.specifier.seq?
  | '&&' attribute.specifier.seq?
  | nested.name.specifier '*' attribute.specifier.seq? cv.qualifier.seq?

  Also handles Apple's block pointer extension ('^').

  C++11 [dcl.decl] (A.7)
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
    std::cout << std::string(__indent, ' ') << "Parser::optPtrOperator 2 " << t
              << '\n';
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
      op.set(ID_C_reference, true);
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
      merged_type.last_type().add_subtype().swap(ptrs);
    }
    else
    {
      DATA_INVARIANT(it->is_not_nil(), "must not be nil");
      it->add_subtype().swap(ptrs);
    }

    ptrs.swap(*it);
  }

  return true;
}

/*
  ctor.initializer                                    [class.base.init]
  : ':' mem.initializer.list

  mem.initializer.list
  : mem.initializer '...'?
  | mem.initializer ',' mem.initializer.list '...'?

  C++11 [class.base.init] (A.10)
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
  mem.initializer                                     [class.base.init]
  : mem.initializer.id '(' expression.list? ')'
  | mem.initializer.id braced.init.list

  mem.initializer.id
  : class.or.decltype
  | identifier

  C++11 [class.base.init] (A.10)
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

  if(tk1.kind == '{')
  {
#ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rMemberInit 3\n";
#endif
    // braced-init-list: the '{' was already consumed
    // parse initializer-clause (',' initializer-clause)* ','? '}'
    if(lex.LookAhead(0) != '}')
    {
      for(;;)
      {
        exprt exp;
        if(!rInitializeExpr(exp))
          return false;
        init.add_to_operands(std::move(exp));
        if(lex.LookAhead(0) == ',')
        {
          lex.get_token(tk2);
          if(lex.LookAhead(0) == '}')
            break; // trailing comma
        }
        else
          break;
      }
    }
    if(lex.get_token(tk2) != '}')
      return false;
  }
  else if(tk1.kind == '(' && lex.LookAhead(0) == '{')
  {
#ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rMemberInit 3b\n";
#endif
    exprt exp;
    if(!rInitializeExpr(exp))
      return false;

    init.operands().push_back(exp);

    if(lex.get_token(tk2) != ')')
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
  qualified.id                                        [expr.prim]
  : nested.name.specifier TEMPLATE? unqualified.id

  nested.name.specifier
  : '::'
  | type.name '::'
  | namespace.name '::'
  | decltype.specifier '::'
  | nested.name.specifier identifier '::'
  | nested.name.specifier TEMPLATE? simple.template.id '::'

  unqualified.id
  : identifier template.args?
  | '~' identifier
  | OPERATOR operator.name template.args?

  This function is used for declarator names (not expressions).
  It always regards '<' as the beginning of template arguments.

  C++11 [expr.prim] (A.4)
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

  bool template_keyword_seen = false;

  for(;;)
  {
    cpp_tokent tk;

#ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rName 2 "
              << lex.LookAhead(0) << '\n';
#endif

    switch(lex.LookAhead(0))
    {
    case TOK_TEMPLATE:
#ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rName 3\n";
#endif
      lex.get_token(tk);
      template_keyword_seen = true;
      // Skip template token, next will be identifier
      if(!is_identifier(lex.LookAhead(0)))
        return false;
      break;

    case '<':
#ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rName 4\n";
#endif
      {
        // Check if the previous identifier could be a template.
        // Per C++11 [temp.names]/4, a name followed by '<' is a
        // template-id only if name lookup finds a template.
        // For dependent qualified names (e.g., T::member where T is
        // a template parameter), the 'template' keyword is required
        // to treat '<' as a template bracket.
        if(!template_keyword_seen && !components.empty())
        {
          const irept &last = components.back();
          if(last.id() == ID_name)
          {
            irep_idt id = last.get(ID_identifier);
            if(!id.empty())
            {
                new_scopet *found = lookup_id(id);
                if(
                  found != nullptr && !found->is_type() &&
                  !found->is_template())
                  return true;

                // For qualified names (A::B<), check whether the
                // qualifier is dependent.  Only then treat '<' as
                // less-than per [temp.names]/4.
                if(found == nullptr)
                {
                  for(std::size_t i = components.size(); i >= 2; --i)
                  {
                    if(components[i - 1].id() != "::")
                      continue;

                    // Qualifier is a template-id (e.g., Wrapper<T>::)
                    // — likely dependent on template parameters.
                    // Only treat as dependent if the template args
                    // contain template parameters; concrete
                    // instantiations like Outer<int>:: are not
                    // dependent.
                    if(i >= 2 && components[i - 2].id() == ID_template_args)
                    {
                      const irept &targs = components[i - 2].find(ID_arguments);
                      bool has_dependent_arg = false;
                      for(const auto &arg : targs.get_sub())
                      {
                        if(arg.id() == ID_name || arg.id() == ID_cpp_name)
                        {
                          irep_idt aid;
                          if(arg.id() == ID_name)
                            aid = arg.get(ID_identifier);
                          else if(!arg.get_sub().empty())
                            aid = arg.get_sub().front().get(ID_identifier);
                          if(!aid.empty())
                          {
                            new_scopet *afound = lookup_id(aid);
                            if(
                              afound != nullptr &&
                              afound->kind ==
                                new_scopet::kindt::TYPE_TEMPLATE_PARAMETER)
                            {
                              has_dependent_arg = true;
                              break;
                            }
                          }
                        }
                      }
                      if(has_dependent_arg)
                        return true;
                      // Concrete instantiation — fall through to
                      // try parsing '<' as template args.
                      break;
                    }

                    // Qualifier is a simple name
                    if(components[i - 2].id() == ID_name)
                    {
                      irep_idt qid = components[i - 2].get(ID_identifier);
                      new_scopet *qfound = lookup_id(qid);
                      if(
                        qfound != nullptr &&
                        qfound->kind ==
                          new_scopet::kindt::TYPE_TEMPLATE_PARAMETER)
                      {
                        return true;
                      }
                    }
                    break;
                  }
                }
            }
          }
        }

        irept args;
        if(!rTemplateArgs(args))
          return false;

        components.push_back(irept(ID_template_args));
        components.back().add(ID_arguments).swap(args);

        template_keyword_seen = false;

        // done unless scope is next
        if(lex.LookAhead(0)!=TOK_SCOPE)
          return true;
      }
      break;

    case TOK_GCC_IDENTIFIER:
    case TOK_MSC_IDENTIFIER:
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
      if(!is_identifier(lex.LookAhead(0)))
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

    case TOK_DECLTYPE:
      // C++11: decltype(expr)::member
      lex.get_token(tk);
      {
        components.push_back(typet{ID_decltype});
        set_location(components.back(), tk);

        if(lex.get_token(tk) != '(')
          return false;

        exprt expr;
        if(!rCommaExpression(expr))
          return false;

        if(lex.get_token(tk) != ')')
          return false;

        components.back().add(ID_expr_arg).swap(expr);

        if(lex.LookAhead(0) != TOK_SCOPE)
          return true;
      }
      break;

    default:
      return false;
    }
  }
}

/*
  operator.function.id                                [over.oper]
  : OPERATOR operator

  operator: one of
    new  delete  new[]  delete[]
    +  -  *  /  %  ^  &  |  ~
    !  =  <  >  +=  -=  *=  /=  %=
    ^=  &=  |=  <<  >>  >>=  <<=  ==  !=
    <=  >=  &&  ||  ++  --  ,  ->*  ->
    ()  []

  Also handles conversion-function-id (cast operator).

  C++11 [over.oper] (A.11)
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
  case TOK_SPACESHIP:
    operator_id = "<=>";
    break;
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
    // C++11: user-defined literal operator: operator "" suffix
    if(t == TOK_STRING)
    {
        lex.get_token(tk);
        // The suffix identifier follows the empty string literal
        if(is_identifier(lex.LookAhead(0)))
        {
          cpp_tokent suffix_tk;
          lex.get_token(suffix_tk);
          name = irept("\"\"" + suffix_tk.data.get_string(ID_C_base_name));
          set_location(name, tk);
          return true;
        }
        return false;
    }
    return rCastOperatorName(name);
  }

  DATA_INVARIANT(!operator_id.empty(), "operator id missing");
  lex.get_token(tk);
  name=irept(operator_id);
  set_location(name, tk);

  return true;
}

/*
  conversion.function.id                              [class.conv.fct]
  : OPERATOR conversion.type.id

  conversion.type.id
  : type.specifier.seq conversion.declarator?

  conversion.declarator
  : ptr.operator conversion.declarator?

  C++11 [class.conv.fct] (A.10)
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
  ptr.to.member (nested.name.specifier '*')           [dcl.mptr]
  : '::'? (identifier template.args? '::')+ '*'

  C++11 [dcl.mptr] (A.7)
*/
bool Parser::rPtrToMember(irept &ptr_to_mem)
{
#ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rPtrToMember 0\n";
#endif

  typet ptm(ID_frontend_pointer); // width gets set during conversion
  irept &name = ptm.add(ID_to_member);
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
      if(!is_identifier(lex.LookAhead(0)))
        return false;
      break;

    case '<':
    {
      irept args;
      if(!rTemplateArgs(args))
        return false;

      components.push_back(irept(ID_template_args));
      components.back().add(ID_arguments).swap(args);

      if(lex.LookAhead(0) != TOK_SCOPE)
        return false;

      break;
    }

    case TOK_GCC_IDENTIFIER:
    case TOK_MSC_IDENTIFIER:
    {
      lex.get_token(tk);
      components.push_back(cpp_namet::namet(tk.data.get(ID_C_base_name)));
      set_location(components.back(), tk);

      int t = lex.LookAhead(0);
      if(t != TOK_SCOPE && t != '<')
        return false;

      break;
    }

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

      if(!is_identifier(lex.LookAhead(0)))
        return false;

      break;

    default:
      return false;
    }
  }
  return false;
}

/*
  template.argument.list                              [temp.names]
  : template.argument '...'?
  | template.argument.list ',' template.argument '...'?

  template.argument
  : type.id
  | constant.expression
  | id.expression

  C++11 [temp.names] (A.12)
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

  // C++11: Foo<> where >> is scanned as shift-right
  if(lex.LookAhead(0) == TOK_SHIFTRIGHT)
  {
    cpp_token_buffert::post pos = lex.Save();
    cpp_tokent tk2;
    lex.get_token(tk2);
    // split >> into > >
    lex.Restore(pos);
    tk2.kind = '>';
    tk2.text = '>';
    lex.Replace(tk2);
    lex.Insert(tk2);
    lex.get_token();
    DATA_INVARIANT(lex.LookAhead(0) == '>', "should be >");
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
        exp.set(ID_ellipsis, true);
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
        exp.set(ID_ellipsis, true);
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
      lex.get_token();
      DATA_INVARIANT(lex.LookAhead(0) == '>', "should be >");
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
  parameter.declaration.clause                        [dcl.fct]
  : parameter.declaration.list? '...'?
  | parameter.declaration.list ',' '...'

  parameter.declaration.list
  : parameter.declaration
  | parameter.declaration.list ',' parameter.declaration

  C++11 [dcl.fct] (A.7)
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
      if(lex.LookAhead(0) == TOK_ELLIPSIS)
      {
        lex.get_token(tk);
        list.get_sub().push_back(irept(ID_ellipsis));
      }

      t = lex.LookAhead(0);
      if(t == ',')
        lex.get_token(tk);
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
  parameter.declaration                               [dcl.fct]
  : attribute.specifier.seq? decl.specifier.seq declarator
  | attribute.specifier.seq? decl.specifier.seq declarator '=' initializer.clause
  | attribute.specifier.seq? decl.specifier.seq abstract.declarator?
  | attribute.specifier.seq? decl.specifier.seq abstract.declarator?
    '=' initializer.clause

  C++11 [dcl.fct] (A.7)
*/
bool Parser::rArgDeclaration(cpp_declarationt &declaration)
{
  typet header;
  cpp_tokent tk;
  bool is_explicit_this = false;

  switch(lex.LookAhead(0))
  {
  case TOK_REGISTER:
    lex.get_token(tk);
    header=typet(ID_register);
    break;

  // C++23 deducing this: skip 'this' keyword in parameter
  case TOK_THIS:
    lex.get_token(tk);
    header.make_nil();
    is_explicit_this = true;
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

  arg_declarator.set_is_parameter(true);

  declaration.declarators().push_back(arg_declarator);

  if(is_explicit_this)
    declaration.set("explicit_this", true);

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
  initializer.clause                                  [dcl.init]
  : assignment.expression
  | braced.init.list

  initializer.list
  : initializer.clause '...'?
  | initializer.list ',' initializer.clause '...'?

  braced.init.list
  : '{' initializer.list ','? '}'
  | '{' '}'

  C++11 [dcl.init] (A.7)
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

    // C++20 designated initializer: .member = expr
    if(t == '.' && is_identifier(lex.LookAhead(1)) && lex.LookAhead(2) == '=')
    {
      cpp_tokent dot_tk, name_tk, eq_tk;
      lex.get_token(dot_tk);
      lex.get_token(name_tk);
      lex.get_token(eq_tk);

      if(!rInitializeExpr(tmp))
      {
        if(!SyntaxError())
          return false;
        SkipTo('}');
        lex.get_token(tk);
        return true;
      }

      exprt desig(ID_designated_initializer);
      set_location(desig, dot_tk);
      exprt member(ID_member);
      member.set(ID_component_name, name_tk.data.get(ID_C_base_name));
      exprt designator;
      designator.add_to_operands(std::move(member));
      desig.add(ID_designator).swap(designator);
      desig.add_to_operands(std::move(tmp));
      expr.add_to_operands(std::move(desig));
    }
    else if(!rInitializeExpr(tmp))
    {
      if(!SyntaxError())
        return false;        // too many errors

      SkipTo('}');
      lex.get_token(tk);
      return true;           // error recovery
    }
    else
    {
      expr.add_to_operands(std::move(tmp));
    }

    // C++11: pack expansion in initializer list
    if(lex.LookAhead(0) == TOK_ELLIPSIS)
    {
      lex.get_token(tk);
      expr.operands().back().set(ID_ellipsis, true);
    }

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
  expression.list                                     [expr.post]
  : initializer.list

  C++11 [expr.post] (A.4): expression-list is an initializer-list,
  which includes braced-init-lists.
  This assumes that the next token following the list is ')'.
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
    if(!rInitializeExpr(exp))
      return false;

    args.add_to_operands(std::move(exp));

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
  enum.specifier                                      [dcl.enum]
  : enum.head '{' enumerator.list? '}'
  | enum.head '{' enumerator.list ',' '}'

  enum.head
  : enum.key attribute.specifier.seq? identifier? enum.base?
  | enum.key attribute.specifier.seq? nested.name.specifier identifier
    enum.base?

  enum.key : ENUM | ENUM CLASS | ENUM STRUCT

  enum.base : ':' type.specifier.seq

  opaque.enum.declaration
  : enum.key attribute.specifier.seq? identifier enum.base? ';'

  C++11 [dcl.enum] (A.6)
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

  spec.add_subtype().make_nil();

  // C++11 enum classes
  if(lex.LookAhead(0)==TOK_CLASS)
  {
    lex.get_token(tk);
    spec.set(ID_C_class, true);
  }

  // C++11 [dcl.enum] (A.6): attribute-specifier-seq after enum-key
  if(!optAttribute(spec))
    return false;

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
    if(!rTypeName(spec.add_subtype()))
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
  enumerator.list                                     [dcl.enum]
  : enumerator.definition
  | enumerator.list ',' enumerator.definition

  enumerator.definition
  : enumerator
  | enumerator '=' constant.expression

  enumerator : identifier

  C++11 [dcl.enum] (A.6)
*/
bool Parser::rEnumBody(irept &body)
{
  body.clear();

  for(;;)
  {
    cpp_tokent tk, tk2;

    if(lex.LookAhead(0)=='}')
      return true;

    if(!is_identifier(lex.get_token(tk)))
      return false;

    body.get_sub().push_back(irept());
    irept &n=body.get_sub().back();
    set_location(n, tk);
    n.set(ID_name, tk.data.get(ID_C_base_name));

    // skip any attributes on enumerators
    typet discarded_attribute;
    if(!optAttribute(discarded_attribute))
      return false;

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
  class.specifier                                     [class]
  : class.head '{' member.specification? '}'

  class.head
  : class.key attribute.specifier.seq? class.head.name class.virt.specifier?
    base.clause?
  | class.key attribute.specifier.seq? base.clause?

  class.key : CLASS | STRUCT | UNION

  C++11 [class] (A.8).  Also handles INTERFACE (MS extension).
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

  if(!optAlignas(spec))
    return false;

  // If alignas turned the struct/union into a merged_type, unwrap it:
  // store the alignment directly on the struct/union type.
  if(spec.id() == ID_merged_type)
  {
    typet unwrapped;
    irept alignment;
    for(auto &sub : to_type_with_subtypes(spec).subtypes())
    {
      if(sub.id() == ID_struct || sub.id() == ID_union)
        unwrapped = sub;
      else if(sub.id() == ID_aligned)
        alignment = sub.find(ID_size);
    }
    if(unwrapped.is_not_nil())
    {
      unwrapped.add_source_location() = spec.source_location();
      if(alignment.is_not_nil())
        unwrapped.set(ID_C_alignment, alignment);
      spec = unwrapped;
    }
  }

  if(!optAttribute(spec))
    return false;

  if(lex.LookAhead(0) == '{' || lex.LookAhead(0) == ':')
  {
    // no tag
#ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rClassSpec 4\n";
#endif

    if(lex.LookAhead(0) == ':')
    {
      if(!rBaseSpecifiers(spec.add(ID_bases)))
        return false;
    }
  }
  else
  {
    irept name;

    if(!rName(name))
      return false;

    spec.add(ID_tag).swap(name);

#ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rClassSpec 5\n";
#endif

    t=lex.LookAhead(0);

    // class-virt-specifier: final
    if(is_identifier(t))
    {
      cpp_tokent peek;
      lex.LookAhead(0, peek);
      if(peek.text == "final")
      {
        lex.get_token(peek);
        spec.set(ID_final, true);
        t = lex.LookAhead(0);
      }
    }

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
      // Forward declaration - register the tag in the scope
      new_scopet::kindt kind = in_template_scope()
                                 ? new_scopet::kindt::CLASS_TEMPLATE
                                 : new_scopet::kindt::TAG;
      add_id(spec.find(ID_tag), kind);
      return true;
    }
  }

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rClassSpec 6\n";
#endif

  save_scopet saved_scope(current_scope);
  {
    new_scopet::kindt kind = in_template_scope()
                               ? new_scopet::kindt::CLASS_TEMPLATE
                               : new_scopet::kindt::TAG;
    make_sub_scope(spec.find(ID_tag), kind);
  }

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
  base.clause                                         [class.derived]
  : ':' base.specifier.list

  base.specifier.list
  : base.specifier '...'?
  | base.specifier.list ',' base.specifier '...'?

  base.specifier
  : attribute.specifier.seq? base.type.specifier
  | attribute.specifier.seq? VIRTUAL access.specifier? base.type.specifier
  | attribute.specifier.seq? access.specifier VIRTUAL? base.type.specifier

  C++11 [class.derived] (A.9)
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
  member.specification                                [class.mem]
  : member.declaration member.specification?
  | access.specifier ':' member.specification?

  member.declaration
  : attribute.specifier.seq? decl.specifier.seq? member.declarator.list? ';'
  | function.definition ';'?
  | using.declaration
  | static_assert.declaration
  | template.declaration
  | alias.declaration

  C++11 [class.mem] (A.8)
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

    members.add_to_operands(
      std::move(static_cast<exprt &>(static_cast<irept &>(member))));
  }

  lex.get_token(tk);
  body.swap(members);
  return true;
}

/*
  class.member (see member.declaration above)         [class.mem]
  : access.specifier ':'
  | ';'
  | typedef.declaration
  | template.declaration
  | using.declaration
  | alias.declaration
  | static_assert.declaration
  | declaration
  | access.decl

  C++11 [class.mem] (A.8)
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
  else if(t==TOK_USING)
    return rUsingOrTypedef(member);
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
  access.declaration                                  [class.access.dcl]
  : qualified.id ';'

  e.g. Base::member;

  C++11 [class.access.dcl] (deprecated, prefer using-declaration)
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
  expression                                          [gram.expr]
  : assignment.expression
  | expression ',' assignment.expression              (left-to-right)

  C++11 [expr.comma] (A.4)
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
    exp.add_to_operands(std::move(left), std::move(right));
    set_location(exp, tk);
  }

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rCommaExpression 2\n";
#endif

  return true;
}

/*
  assignment.expression                               [expr.ass]
  : conditional.expression
  | logical.or.expression assignment.operator initializer.clause
  | throw.expression

  assignment.operator: one of
    = *= /= %= += -= >>= <<= &= ^= |=

  C++11 [expr.ass] (A.4): the RHS of an assignment is an
  initializer-clause, which includes braced-init-lists.
  throw-expression is an assignment-expression.
*/
bool Parser::rExpression(exprt &exp, bool template_args)
{
  cpp_tokent tk;

#ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rExpression 0\n";
#endif

  if(lex.LookAhead(0) == TOK_THROW)
    return rThrowExpr(exp);

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
    if(!rInitializeExpr(right))
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

    exp.add_to_operands(std::move(left), std::move(right));
    set_location(exp, tk);
  }

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rExpression 4\n";
#endif

  return true;
}

/*
  conditional.expression                              [expr.cond]
  : logical.or.expression
  | logical.or.expression '?' expression ':' assignment.expression

  C++11 [expr.cond] (A.4): right-to-left associativity.
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

    exp =
      if_exprt(std::move(cond), std::move(then), std::move(otherwise), typet());
    set_location(exp, tk1);
  }

  return true;
}

/*
  logical.or.expression                               [expr.log.or]
  : logical.and.expression
  | logical.or.expression '||' logical.and.expression (left-to-right)

  C++11 [expr.log.or] (A.4)
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

    // C++17 fold expression: (expr || ...)
    if(lex.LookAhead(0) == TOK_ELLIPSIS)
    {
      lex.get_token(tk);
      break;
    }

    exprt right;
    if(!rLogicalAndExpr(right, template_args))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt(ID_or);
    exp.add_to_operands(std::move(left), std::move(right));
    set_location(exp, tk);
  }

  return true;
}

/*
  logical.and.expression                              [expr.log.and]
  : inclusive.or.expression
  | logical.and.expression '&&' inclusive.or.expression

  C++11 [expr.log.and] (A.4)
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

    // C++17 fold expression: (expr && ...)
    if(lex.LookAhead(0) == TOK_ELLIPSIS)
    {
      lex.get_token(tk);
      break;
    }

    exprt right;
    if(!rInclusiveOrExpr(right, template_args))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt(ID_and);
    exp.add_to_operands(std::move(left), std::move(right));
    set_location(exp, tk);
  }

  return true;
}

/*
  inclusive.or.expression                             [expr.or]
  : exclusive.or.expression
  | inclusive.or.expression '|' exclusive.or.expression

  C++11 [expr.or] (A.4)
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
    exp.add_to_operands(std::move(left), std::move(right));
    set_location(exp, tk);
  }

  return true;
}

/*
  exclusive.or.expression                             [expr.xor]
  : and.expression
  | exclusive.or.expression '^' and.expression

  C++11 [expr.xor] (A.4)
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
    exp.add_to_operands(std::move(left), std::move(right));
    set_location(exp, tk);
  }

  return true;
}

/*
  and.expression                                      [expr.bit.and]
  : equality.expression
  | and.expression '&' equality.expression

  C++11 [expr.bit.and] (A.4)
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
    exp.add_to_operands(std::move(left), std::move(right));
    set_location(exp, tk);
  }

  return true;
}

/*
  equality.expression                                 [expr.eq]
  : relational.expression
  | equality.expression '==' relational.expression
  | equality.expression '!=' relational.expression

  C++11 [expr.eq] (A.4)
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
    exp.add_to_operands(std::move(left), std::move(right));
    set_location(exp, tk);
  }

  return true;
}

/*
  relational.expression                               [expr.rel]
  : shift.expression
  | relational.expression '<' shift.expression
  | relational.expression '>' shift.expression
  | relational.expression '<=' shift.expression
  | relational.expression '>=' shift.expression

  C++11 [expr.rel] (A.4)
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

  while(t = lex.LookAhead(0),
        (t == TOK_LE || t == TOK_GE || t == '<' ||
         (t == '>' && !template_args) || t == TOK_SPACESHIP))
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
    case TOK_SPACESHIP:
      id = ID_spaceship;
      break;
    }

    exp=exprt(id);
    exp.add_to_operands(std::move(left), std::move(right));
    set_location(exp, tk);
  }

  return true;
}

/*
  shift.expression                                    [expr.shift]
  : additive.expression
  | shift.expression '<<' additive.expression
  | shift.expression '>>' additive.expression

  C++11 [expr.shift] (A.4)
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
    exp.add_to_operands(std::move(left), std::move(right));
    set_location(exp, tk);
  }

  return true;
}

/*
  additive.expression                                 [expr.add]
  : multiplicative.expression
  | additive.expression '+' multiplicative.expression
  | additive.expression '-' multiplicative.expression

  C++11 [expr.add] (A.4)
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

    // C++17 fold expression: (expr + ...)
    if(lex.LookAhead(0) == TOK_ELLIPSIS)
    {
      lex.get_token(tk);
      break;
    }

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
    exp.add_to_operands(std::move(left), std::move(right));
    set_location(exp, tk);
  }

  return true;
}

/*
  multiplicative.expression                           [expr.mul]
  : pm.expression
  | multiplicative.expression '*' pm.expression
  | multiplicative.expression '/' pm.expression
  | multiplicative.expression '%' pm.expression

  C++11 [expr.mul] (A.4)
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
    exp.add_to_operands(std::move(left), std::move(right));
    set_location(exp, tk);
  }

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rMultiplyExpr 2\n";
#endif

  return true;
}

/*
  pm.expression                                       [expr.mptr.oper]
  : cast.expression
  | pm.expression '.*' cast.expression
  | pm.expression '->*' cast.expression

  C++11 [expr.mptr.oper] (A.4)
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

    exp = exprt(ID_pointer_to_member);
    exp.add_to_operands(std::move(left), std::move(right));
    set_location(exp, tk);
  }

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rPmExpr 2\n";
#endif

  return true;
}

/*
  cast.expression                                     [expr.cast]
  : unary.expression
  | '(' type.id ')' cast.expression

  Extension: '(' type.id ')' braced.init.list (GCC/Clang compound literal)

  C++11 [expr.cast] (A.4)
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
        else if(lex.LookAhead(0) == '{')
        {
          // GCC/Clang extension: (type) { ... }
          exprt exp2;
          if(!rInitializeExpr(exp2))
            return false;

          exp = exprt("explicit-typecast");
          exp.type().swap(tname);
          exp.add_to_operands(std::move(exp2));
          set_location(exp, tk1);

          return true;
        }
        else if(rCastExpr(exp))
        {
          exprt op;
          op.swap(exp);

          exp=exprt("explicit-typecast");
          exp.type().swap(tname);
          exp.add_to_operands(std::move(op));
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
  type.id                                             [dcl.name]
  : type.specifier.seq abstract.declarator?

  C++11 [dcl.name] (A.7)
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
  if(
    is_identifier(lex.LookAhead(0)) && lex.LookAhead(1) == TOK_SCOPE &&
    lex.LookAhead(2) == '*' && lex.LookAhead(3) == ')' &&
    lex.LookAhead(4) == '(')
  {
    lex.get_token();
    lex.get_token();
    lex.get_token();
    lex.get_token();
    lex.get_token();
  }
  else if(
    is_identifier(lex.LookAhead(0)) && lex.LookAhead(1) == ')' &&
    lex.LookAhead(2) == '(')
  {
    lex.get_token(op);
    type.set(ID_identifier, op.data.get(ID_C_base_name));
    lex.get_token();
    lex.get_token();
  }
  else if(
    lex.LookAhead(0) == '*' && is_identifier(lex.LookAhead(1)) &&
    lex.LookAhead(2) == ')' && lex.LookAhead(3) == '(')
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

      code_typet::parametert parameter(typet{});
      parameter.swap(parameter_declaration);
      type.parameters().push_back(parameter);

      t=lex.LookAhead(0);
      if(t == TOK_ELLIPSIS)
      {
        cpp_tokent tk;
        lex.get_token(tk);
        to_cpp_declaration(type.parameters().back())
          .declarators()
          .back()
          .set_has_ellipsis();
        t = lex.LookAhead(0);
      }

      if(t == ',')
      {
        cpp_tokent tk;
        lex.get_token(tk);
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

  // C++11 [dcl.fct]: optional ref-qualifier (& or &&)
  if(lex.LookAhead(0) == '&')
  {
    cpp_tokent rq;
    lex.get_token(rq);
    type.set(ID_C_ref_qualifier, "&");
  }
  else if(lex.LookAhead(0) == TOK_ANDAND)
  {
    cpp_tokent rq;
    lex.get_token(rq);
    type.set(ID_C_ref_qualifier, "&&");
  }

  // C++17: noexcept as part of the function type
  if(lex.LookAhead(0) == TOK_NOEXCEPT)
  {
    cpp_tokent ne;
    lex.get_token(ne);
    if(lex.LookAhead(0) == '(')
    {
      // noexcept(expression) — consume the expression
      lex.get_token(ne);
      int depth = 1;
      while(depth > 0)
      {
        lex.get_token(ne);
        if(ne.kind == '(')
          ++depth;
        else if(ne.kind == ')')
          --depth;
        else if(ne.kind == '\0')
          return false;
      }
    }
    // Store noexcept on the function type
    type.set(ID_noexcept, true);
  }

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
  unary.expression                                    [expr.unary]
  : postfix.expression
  | '++' cast.expression
  | '--' cast.expression
  | unary.operator cast.expression
  | SIZEOF unary.expression
  | SIZEOF '(' type.id ')'
  | SIZEOF '...' '(' identifier ')'
  | ALIGNOF '(' type.id ')'
  | noexcept.expression
  | new.expression
  | delete.expression

  unary.operator: one of  * & + - ! ~

  C++11 [expr.unary] (A.4): throw-expression is handled in rExpression
  as it is an assignment-expression.
*/

bool Parser::rUnaryExpr(exprt &exp)
{
  int t=lex.LookAhead(0);

#ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rUnaryExpr 0\n";
#endif

  // C++20 co_await/co_yield: parse operand and pass through
  if(t == TOK_CO_AWAIT || t == TOK_CO_YIELD)
  {
    cpp_tokent tk;
    lex.get_token(tk);
    if(!rCastExpr(exp))
      return false;
    return true;
  }

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

    exp.add_to_operands(std::move(right));
    set_location(exp, tk);

    return true;
  }
  else if(t==TOK_SIZEOF)
    return rSizeofExpr(exp);
  else if(t==TOK_ALIGNOF)
    return rAlignofExpr(exp);
  else if(t == TOK_OFFSETOF)
  {
    // __builtin_offsetof(type, member)
    cpp_tokent tk;
    lex.get_token(tk);
    if(lex.get_token(tk) != '(')
      return false;
    typet tname;
    if(!rTypeName(tname))
      return false;
    if(lex.get_token(tk) != ',')
      return false;
    // parse member designator as identifier(s) with . separators
    exp = exprt(ID_builtin_offsetof);
    exp.type() = typet(ID_size_t);
    exp.add(ID_type_arg).swap(tname);
    {
      exprt member(ID_designated_initializer);
      for(;;)
      {
        cpp_tokent mtk;
        if(!is_identifier(lex.LookAhead(0)))
          return false;
        lex.get_token(mtk);
        exprt desig(ID_member);
        desig.set(ID_component_name, mtk.data.get(ID_C_base_name));
        member.add_to_operands(std::move(desig));
        if(lex.LookAhead(0) != '.')
          break;
        lex.get_token(mtk);
      }
      exp.add(ID_designator).swap(member);
    }
    if(lex.get_token(tk) != ')')
      return false;
    set_location(exp, tk);
    return true;
  }
  else if(t==TOK_NOEXCEPT)
    return rNoexceptExpr(exp);
  else if(t == TOK_BIT_CAST)
  {
    // __builtin_bit_cast(type, expr)
    cpp_tokent tk;
    lex.get_token(tk);
    if(lex.get_token(tk) != '(')
      return false;
    typet tname;
    if(!rTypeName(tname))
      return false;
    if(lex.get_token(tk) != ',')
      return false;
    exprt val;
    if(!rExpression(val, false))
      return false;
    if(lex.get_token(tk) != ')')
      return false;
    exp = exprt(ID_typecast);
    exp.type() = tname;
    exp.add_to_operands(std::move(val));
    set_location(exp, tk);
    return true;
  }
  else if(t==TOK_REAL || t==TOK_IMAG)
  {
    // a GCC extension for complex floating-point arithmetic
    cpp_tokent tk;
    lex.get_token(tk);

    exprt unary;

    if(!rUnaryExpr(unary))
      return false;

    exp=exprt(t==TOK_REAL?ID_complex_real:ID_complex_imag);
    exp.add_to_operands(std::move(unary));
    set_location(exp, tk);
    return true;
  }
  else if(isAllocateExpr(t))
    return rAllocateExpr(exp);
  else
    return rPostfixExpr(exp);
}

/*
  throw.expression                                    [except.throw]
  : THROW {assignment.expression}

  C++11 [except] (A.13)
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

    exp.add_to_operands(std::move(e));
  }

  return true;
}

/*
  typeid.expression                                   [expr.typeid]
  : TYPEID '(' expression ')'
  | TYPEID '(' type.id ')'

  C++11 [expr.typeid] (A.4)
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
  sizeof.expression                                   [expr.sizeof]
  : SIZEOF unary.expression
  | SIZEOF '(' type.id ')'
  | SIZEOF '...' '(' identifier ')'

  C++11 [expr.sizeof] (A.4)
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

    cpp_token_buffert::post pos2 = lex.Save();
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

    // C++11: sizeof...(pack) where pack is a non-type parameter pack
    lex.Restore(pos2);
    lex.get_token(ell); // re-consume ...
    lex.get_token(op);  // re-consume (

    {
      exprt pack_expr;
      if(rName(pack_expr))
      {
        if(lex.get_token(cp) == ')')
        {
          exp = exprt(ID_sizeof);
          exp.add_to_operands(std::move(pack_expr));
          set_location(exp, tk);
          return true;
        }
      }
    }

    return false;
  }

  exprt unary;

  if(!rUnaryExpr(unary))
    return false;

  exp=exprt(ID_sizeof);
  exp.add_to_operands(std::move(unary));
  set_location(exp, tk);
  return true;
}

/*
  alignof.expression                                  [expr.alignof]
  : ALIGNOF '(' type.id ')'

  C++11 [expr.alignof] (A.4)
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
  : NOEXCEPT '(' comma.expression ')'

  C++11 [expr.unary.noexcept] (A.4)
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

  if(lex.LookAhead(0) != '(')
    return false;

  exprt subexp;
  cpp_tokent op, cp;

  lex.get_token(op);

  if(!rCommaExpression(subexp))
    return false;

  if(lex.get_token(cp) != ')')
    return false;

  exp = exprt(ID_noexcept);
  exp.add_to_operands(std::move(subexp));
  set_location(exp, tk);
  return true;
}

bool Parser::isAllocateExpr(int t)
{
  if(t==TOK_SCOPE)
    t=lex.LookAhead(1);

  return t==TOK_NEW || t==TOK_DELETE;
}

/*
  new.expression                                      [expr.new]
  : '::'? NEW new.placement? new.type.id new.initializer?
  | '::'? NEW new.placement? '(' type.id ')' new.initializer?

  delete.expression                                   [expr.delete]
  : '::'? DELETE cast.expression
  | '::'? DELETE '[' ']' cast.expression

  C++11 [expr.new], [expr.delete] (A.4)
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

    exp.add_to_operands(std::move(obj));

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
  : new.placement? type.specifier new.declarator? new.initializer?
  | new.placement? '(' type.id ')' new.initializer?

  new.placement                                       [expr.new]
  : '(' expression.list ')'

  new.initializer
  : '(' expression.list? ')'
  | braced.init.list

  C++11 [expr.new] (A.4)
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
  new.declarator                                      [expr.new]
  : ptr.operator new.declarator?
  | noptr.new.declarator

  noptr.new.declarator
  : '[' expression ']' attribute.specifier.seq?
  | noptr.new.declarator '[' constant.expression ']' attribute.specifier.seq?

  C++11 [expr.new] (A.4)
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
  new.initializer                                     [expr.new]
  : '(' expression.list? ')'
  | braced.init.list

  C++11 [expr.new] (A.4)
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

    init.add_to_operands(std::move(exp));

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
  postfix.expression                                  [expr.post]
  : primary.expression
  | postfix.expression '[' expression ']'
  | postfix.expression '[' braced.init.list ']'
  | postfix.expression '(' expression.list? ')'
  | simple.type.specifier '(' expression.list? ')'
  | typename.specifier '(' expression.list? ')'
  | simple.type.specifier braced.init.list
  | typename.specifier braced.init.list
  | postfix.expression '.' TEMPLATE? id.expression
  | postfix.expression '->' TEMPLATE? id.expression
  | postfix.expression '++'
  | postfix.expression '--'
  | DYNAMIC_CAST '<' type.id '>' '(' expression ')'
  | STATIC_CAST '<' type.id '>' '(' expression ')'
  | REINTERPRET_CAST '<' type.id '>' '(' expression ')'
  | CONST_CAST '<' type.id '>' '(' expression ')'
  | TYPEID '(' expression ')'
  | TYPEID '(' type.id ')'

  C++11 [expr.post] (A.4)
*/
bool Parser::rPostfixExpr(exprt &exp)
{
#ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rPostfixExpr 0\n";
#endif

  int t0 = lex.LookAhead(0);

  if(
    t0 == TOK_DYNAMIC_CAST || t0 == TOK_STATIC_CAST ||
    t0 == TOK_REINTERPRET_CAST || t0 == TOK_CONST_CAST)
  {
    if(!rCppCastExpr(exp))
      return false;
  }
  else if(t0 == TOK_TYPEID)
  {
    if(!rTypeidExpr(exp))
      return false;
  }
  else if(!rPrimaryExpr(exp))
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

      if(lex.LookAhead(0) == '{')
      {
        // C++11 initialisation expression in subscript
        if(!rInitializeExpr(e))
          return false;
      }
      else if(!rCommaExpression(e))
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
        exp.add_to_operands(std::move(left), std::move(e));
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
        side_effect_expr_function_callt fc(
          std::move(exp), {}, typet{}, source_locationt{});
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
        tmp.add_to_operands(std::move(exp));
        set_location(tmp, op);
        exp.swap(tmp);
      }
      break;

    case TOK_DECR:
      lex.get_token(op);

      {
        side_effect_exprt tmp(
          ID_postdecrement, {std::move(exp)}, typet(), source_locationt());
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

        exp.add_to_operands(std::move(left));
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
  c++cast.expr
  : (DYNAMIC_CAST | STATIC_CAST | REINTERPRET_CAST | CONST_CAST)
    '<' type.name '>' '(' comma.expression ')'

  C++11 [expr.post] (A.4)
*/
bool Parser::rCppCastExpr(exprt &expr)
{
  cpp_tokent tk;

  lex.get_token(tk);

  expr.id(irep_idt(tk.text));
  set_location(expr, tk);

  if(lex.get_token(tk) != '<')
    return false;

  typet tname;
  if(!rTypeName(tname))
    return false;

  if(lex.get_token(tk) != '>')
    return false;

  if(lex.get_token(tk) != '(')
    return false;

  exprt op;
  if(!rCommaExpression(op))
    return false;

  if(lex.get_token(tk) != ')')
    return false;

  expr.type().swap(tname);
  expr.add_to_operands(std::move(op));

  return true;
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
  expr.add_to_operands(std::move(unary));
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

  expr.add_to_operands(std::move(name), std::move(op));

  set_location(expr, tk1);

  return true;
}

std::optional<codet> Parser::rMSC_if_existsStatement()
{
  cpp_tokent tk1;

  lex.get_token(tk1);

  if(tk1.kind != TOK_MSC_IF_EXISTS && tk1.kind != TOK_MSC_IF_NOT_EXISTS)
    return {};

  cpp_tokent tk2;

  if(lex.get_token(tk2)!='(')
    return {};

  exprt name;

  if(!rVarName(name))
    return {};

  if(lex.get_token(tk2)!=')')
    return {};

  if(lex.get_token(tk2)!='{')
    return {};

  code_blockt block;

  while(lex.LookAhead(0)!='}')
  {
    if(auto statement = rStatement())
      block.add(std::move(*statement));
    else
      return {};
  }

  if(lex.get_token(tk2)!='}')
    return {};

  codet code(
    tk1.kind == TOK_MSC_IF_EXISTS ? ID_msc_if_exists : ID_msc_if_not_exists);

  code.add_to_operands(std::move(name), std::move(block));

  set_location(code, tk1);

  return std::move(code);
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
    if(lex.LookAhead(0) == TOK_ELLIPSIS)
      lex.get_token(tk);
    if(lex.LookAhead(0) == ',')
    {
      lex.get_token(tk);
      if(!rTypeName(tname2))
        return false;
      if(lex.LookAhead(0) == TOK_ELLIPSIS)
        lex.get_token(tk);
      // consume any additional type arguments (variadic traits)
      while(lex.LookAhead(0) == ',')
      {
        lex.get_token(tk);
        typet extra;
        if(!rTypeName(extra))
          return false;
        if(lex.LookAhead(0) == TOK_ELLIPSIS)
          lex.get_token(tk);
      }
    }
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
  lambda.expression                                   [expr.prim.lambda]
  : lambda.introducer lambda.declarator? compound.statement

  lambda.introducer
  : '[' lambda.capture? ']'

  lambda.capture
  : capture.default
  | capture.list
  | capture.default ',' capture.list

  capture.default: '&' | '='
  capture.list: capture (',' capture)*
  capture: simple.capture | init.capture
  simple.capture: identifier | '&' identifier | THIS

  lambda.declarator
  : '(' parameter.declaration.clause ')' MUTABLE?
    exception.specification? trailing.return.type?

  C++11 [expr.prim.lambda] (A.4)
*/
bool Parser::rLambdaExpr(exprt &exp)
{
  cpp_tokent tk;

  if(lex.get_token(tk) != '[')
    return false;

  exp = exprt("lambda");
  set_location(exp, tk);

  // Parse lambda capture
  irept &capture = exp.add("lambda_capture");

  if(lex.LookAhead(0) != ']')
  {
    // capture-default: '&' or '='
    if(
      lex.LookAhead(0) == '&' &&
      (lex.LookAhead(1) == ']' || lex.LookAhead(1) == ','))
    {
      lex.get_token(tk);
      capture.set("default", "&");
      if(lex.LookAhead(0) == ',')
        lex.get_token(tk);
    }
    else if(
      lex.LookAhead(0) == '=' &&
      (lex.LookAhead(1) == ']' || lex.LookAhead(1) == ','))
    {
      lex.get_token(tk);
      capture.set("default", "=");
      if(lex.LookAhead(0) == ',')
        lex.get_token(tk);
    }

    // capture-list
    while(lex.LookAhead(0) != ']')
    {
      irept cap("capture");
      bool by_ref = false;

      if(lex.LookAhead(0) == '&')
      {
        lex.get_token(tk);
        by_ref = true;
      }

      if(lex.LookAhead(0) == TOK_THIS)
      {
        lex.get_token(tk);
        cap.set("this", true);
      }
      else if(is_identifier(lex.LookAhead(0)))
      {
        lex.get_token(tk);
        cap.set(ID_identifier, tk.data.get(ID_C_base_name));

        // C++14 init-capture: identifier '=' expression
        if(lex.LookAhead(0) == '=')
        {
          lex.get_token(tk);
          exprt init;
          if(!rExpression(init, false))
            return false;
          cap.add("init", init);
        }
      }
      else
        return false;

      if(by_ref)
        cap.set("by_ref", true);

      capture.get_sub().push_back(cap);

      if(lex.LookAhead(0) == ',')
        lex.get_token(tk);
      else
        break;
    }
  }

  if(lex.get_token(tk) != ']')
    return false;

  // C++20 template lambda: []<typename T>(T x) { ... }
  // Skip template parameters for verification purposes.
  if(lex.LookAhead(0) == '<')
  {
    lex.get_token(tk);
    // Skip until matching '>'
    int depth = 1;
    while(depth > 0)
    {
      int t = lex.get_token(tk);
      if(t == '<')
        ++depth;
      else if(t == '>')
        --depth;
      else if(t == 0) // EOF
        return false;
    }
  }

  // Optional lambda declarator: '(' params ')' mutable? exception-spec?
  //   trailing-return-type?
  if(lex.LookAhead(0) == '(')
  {
    lex.get_token(tk); // consume '('

    irept &params = exp.add("parameters");

    if(lex.LookAhead(0) != ')')
    {
      // Parse parameter declarations
      for(;;)
      {
        cpp_declarationt param_decl;
        if(!rArgDeclaration(param_decl))
          return false;

        params.get_sub().push_back(
          static_cast<irept &>(static_cast<exprt &>(param_decl)));

        if(lex.LookAhead(0) == ',')
          lex.get_token(tk);
        else
          break;
      }
    }

    if(lex.get_token(tk) != ')')
      return false;

    // optional mutable
    if(lex.LookAhead(0) == TOK_MUTABLE)
      lex.get_token(tk);

    // optional constexpr (C++17)
    if(lex.LookAhead(0) == TOK_CONSTEXPR)
      lex.get_token(tk);

    // optional exception specification
    optThrowDecl(exp.add(ID_exception_list));

    // optional trailing return type
    if(lex.LookAhead(0) == TOK_ARROW)
    {
      lex.get_token(tk);
      typet return_type;
      if(!rTypeName(return_type))
        return false;
      exp.add("return_type", return_type);
    }

    // C++20 requires clause on lambda: skip
    if(lex.LookAhead(0) == TOK_REQUIRES)
    {
      lex.get_token(tk);
      if(lex.LookAhead(0) == '(')
      {
        lex.get_token(tk);
        int depth = 1;
        while(depth > 0)
        {
          int t = lex.get_token(tk);
          if(t == '(')
            ++depth;
          else if(t == ')')
            --depth;
          else if(t == 0)
            return false;
        }
      }
    }
  }

  // compound statement (body)
  if(auto body = rCompoundStatement())
  {
    exp.add("body", *body);
    return true;
  }

  return false;
}

/*
  primary.expression                                  [expr.prim]
  : literal
  | THIS
  | '(' expression ')'
  | id.expression
  | lambda.expression

  literal: integer | character | floating | string | boolean | pointer

  C++11 [expr.prim.general] (A.4).  The simple-type-specifier and
  typename-specifier forms of postfix-expression are also handled here
  when the type is followed by '(' or '{'.
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

    // C++11 user-defined literals: 4_kb becomes operator""_kb(4)
    if(is_identifier(lex.LookAhead(0)))
    {
      cpp_tokent suffix_tk;
      lex.LookAhead(0, suffix_tk);
      if(!suffix_tk.text.empty() && suffix_tk.text[0] == '_')
      {
        lex.get_token(suffix_tk);
        // Build cpp_name: operator + ""_suffix
        irept op_node(ID_operator);
        set_location(op_node, tk);
        irept suffix_node("\"\"" + suffix_tk.text);
        set_location(suffix_node, tk);

        exprt name_expr(ID_cpp_name);
        name_expr.get_sub().push_back(op_node);
        name_expr.get_sub().push_back(suffix_node);
        set_location(name_expr, tk);

        side_effect_expr_function_callt fc(
          std::move(name_expr), {std::move(exp)}, typet{}, source_locationt{});
        set_location(fc, tk);
        exp.swap(fc);
      }
    }

#ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rPrimaryExpr 1\n";
#endif
    return true;

  case TOK_STRING:
    rString(tk);
    exp.swap(tk.data);
    set_location(exp, tk);

    // C++11 user-defined string literal: "abc"_suffix
    if(is_identifier(lex.LookAhead(0)))
    {
      cpp_tokent suffix_tk;
      lex.LookAhead(0, suffix_tk);
      if(!suffix_tk.text.empty() && suffix_tk.text[0] == '_')
      {
        lex.get_token(suffix_tk);
        irept op_node(ID_operator);
        set_location(op_node, tk);
        irept suffix_node("\"\"" + suffix_tk.text);
        set_location(suffix_node, tk);

        exprt name_expr(ID_cpp_name);
        name_expr.get_sub().push_back(op_node);
        name_expr.get_sub().push_back(suffix_node);
        set_location(name_expr, tk);

        // String UDL: operator""_suffix(str, len)
        exprt len = from_integer(exp.get(ID_value).size(), signed_int_type());
        set_location(len, tk);
        side_effect_expr_function_callt fc(
          std::move(name_expr),
          {std::move(exp), std::move(len)},
          typet{},
          source_locationt{});
        set_location(fc, tk);
        exp.swap(fc);
      }
    }

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

  case TOK_REQUIRES:
  {
    // C++20 requires expression: treat as true for verification
    lex.get_token(tk);
    if(lex.LookAhead(0) == '(')
    {
      lex.get_token(tk);
      int depth = 1;
      while(depth > 0)
      {
        int t = lex.get_token(tk);
        if(t == '(')
          ++depth;
        else if(t == ')')
          --depth;
        else if(t == 0)
          return false;
      }
    }
    if(lex.LookAhead(0) == '{')
    {
      lex.get_token(tk);
      int depth = 1;
      while(depth > 0)
      {
        int t = lex.get_token(tk);
        if(t == '{')
          ++depth;
        else if(t == '}')
          --depth;
        else if(t == 0)
          return false;
      }
    }
    exp = typecast_exprt(true_exprt(), c_bool_type());
    set_location(exp, tk);
    return true;
  }

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
    exp = null_pointer_exprt{pointer_type(typet(ID_nullptr))};
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

    // C++17 left fold expression: (... op expr)
    if(lex.LookAhead(0) == TOK_ELLIPSIS)
    {
      lex.get_token(tk2); // consume ...
      // The next token must be a binary operator
      cpp_tokent op_tk;
      lex.get_token(op_tk);
      exprt right;
      if(!rCastExpr(right))
        return false;
      if(lex.get_token(tk2) != ')')
        return false;
      // Treat as the pack expression itself (the fold is lowered
      // during template instantiation, same as right folds)
      exp.swap(right);
      return true;
    }

    if(lex.LookAhead(0)=='{') // GCC extension
    {
      if(auto code = rCompoundStatement())
      {
        exp = exprt(ID_side_effect);
        exp.set(ID_statement, ID_statement_expression);
        set_location(exp, tk);
        exp.add_to_operands(std::move(*code));
      }
      else
        return false;

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

  case '[':
    return rLambdaExpr(exp);

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
          exp.add_to_operands(std::move(exp2));
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

        if(lex.LookAhead(0) == '{')
        {
          // C++11: name followed by braced-init-list is explicit type
          // conversion (simple-type-specifier braced-init-list)
          lex.LookAhead(0, tk);

          exprt exp2;
          if(!rInitializeExpr(exp2))
            return false;

          typet type2;
          type2.swap(exp);
          exp = exprt("explicit-constructor-call");
          exp.type().swap(type2);
          exp.add_to_operands(std::move(exp2));
          set_location(exp, tk);
        }
        else if(lex.LookAhead(0) == TOK_SCOPE)
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
  id.expression (in expression context)               [expr.prim]
  : unqualified.id
  | qualified.id

  Uses maybeTemplateArgs() to disambiguate '<' as template arguments
  vs. less-than operator.  If the name ends with a template type,
  the next token must be '(' or '{'.

  C++11 [expr.prim] (A.4)
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

  bool template_keyword_seen = false;

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
      template_keyword_seen = true;
      // Skip template token, next will be identifier
      if(!is_identifier(lex.LookAhead(0)))
        return false;
      break;

    case TOK_GCC_IDENTIFIER:
    case TOK_MSC_IDENTIFIER:
#ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rVarNameCore 3\n";
#endif

      lex.get_token(tk);
      components.push_back(cpp_namet::namet(tk.data.get(ID_C_base_name)));
      set_location(components.back(), tk);

      {
        // may be followed by template arguments, but only if the
        // identifier could be a type or template name.
        // When the identifier is a known template but maybeTemplateArgs()
        // fails (e.g., non-type args containing '<' that confuse the
        // balanced-bracket heuristic), we still attempt rTemplateArgs
        // with save/restore.  In expression context, an identifier
        // immediately after '>' indicates a declaration (e.g.,
        // unique_lock<T> var), not a template-id expression, so we
        // reject that case to avoid stealing tokens from the
        // declaration parser.
        bool try_template_args =
          (maybeTemplateArgs() && MaybeTypeNameOrClassTemplate(tk));
        if(!try_template_args && lex.LookAhead(0) == '<')
        {
          irep_idt id = tk.data.get(ID_C_base_name);
          if(!id.empty())
          {
            new_scopet *s = lookup_id(id);
            if(s != nullptr && s->is_template())
                try_template_args = true;
          }
        }
        if(try_template_args)
        {
          // For qualified names where the member is not found by
          // lookup, treat '<' as less-than per [temp.names]/4
          // only when the qualifier is dependent.
          bool is_dependent_member = false;
          if(!template_keyword_seen && components.size() >= 2)
          {
            irep_idt mid = tk.data.get(ID_C_base_name);
            new_scopet *mfound = lookup_id(mid);
            if(mfound == nullptr)
            {
                for(std::size_t i = components.size(); i >= 2; --i)
                {
                  if(components[i - 1].id() != "::")
                    continue;

                  if(i >= 2 && components[i - 2].id() == ID_template_args)
                  {
                    is_dependent_member = true;
                    break;
                  }

                  if(components[i - 2].id() == ID_name)
                  {
                    irep_idt qid = components[i - 2].get(ID_identifier);
                    new_scopet *qfound = lookup_id(qid);
                    if(
                      qfound != nullptr &&
                      qfound->kind ==
                        new_scopet::kindt::TYPE_TEMPLATE_PARAMETER)
                    {
                      is_dependent_member = true;
                    }
                  }
                  break;
                }
            }
          }

          if(!is_dependent_member)
          {
            cpp_token_buffert::post pos = lex.Save();

#ifdef DEBUG
            std::cout << std::string(__indent, ' ')
                      << "Parser::rVarNameCore 4\n";
#endif

          irept args;
          if(!rTemplateArgs(args))
          {
            lex.Restore(pos);
            return true;
          }

          // In expression context, a plain identifier after '>'
          // means this is really a declaration (e.g.,
          // unique_lock<T> var{...}), not a template-id expression.
          // Restore and let the declaration parser handle it.
          if(
            is_identifier(lex.LookAhead(0)) && lex.LookAhead(0) != TOK_OPERATOR)
          {
            lex.Restore(pos);
            return true;
          }

          components.push_back(irept(ID_template_args));
          components.back().add(ID_arguments).swap(args);
          }
          template_keyword_seen = false;
        }
      } // end of template-args block

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

      if(!is_identifier(lex.LookAhead(0)))
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

    case TOK_DECLTYPE:
      // C++11: decltype(expr)::member
      lex.get_token(tk);
      {
        components.push_back(typet{ID_decltype});
        set_location(components.back(), tk);

        if(lex.get_token(tk) != '(')
          return false;

        exprt expr;
        if(!rCommaExpression(expr))
          return false;

        if(lex.get_token(tk) != ')')
          return false;

        components.back().add(ID_expr_arg).swap(expr);

        if(lex.LookAhead(0) != TOK_SCOPE)
          return false;
      }
      break;

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
    if(is_identifier(t) || t == '~' || t == TOK_OPERATOR || t == TOK_TEMPLATE)
      return true;
  }

  return false;
}

/*
  template.args (in expression context)               [temp.names]
  : '<' template.argument.list? '>'

  Nesting-aware: tracks '<>' depth and parenthesized sub-expressions.
  Returns true only when a matching '>' is found and followed by a
  valid follow token ('::', '(', ')', '{', ',', ';').

  C++11 [temp.names] (A.12)
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
    int n = 1;
    for(;;)
    {
      int u=lex.LookAhead(i++);
      if(u=='\0' || u==';' || u=='}')
        return false;
      else if(u == '<')
        ++n;
      else if(u=='>')
        --n;
      else if(u=='(')
      {
        int m=1;
        while(m>0)
        {
          int v = lex.LookAhead(i++);
          if(v=='(')
            ++m;
          else if(v==')')
            --m;
          else if(v=='\0' || v==';' || v=='}')
            return false;
        }
      }
      else if(u==TOK_SHIFTRIGHT && n>=2)
        n-=2;

      if(n == 0)
        break;
    }

    t=lex.LookAhead(i);
    return t == TOK_SCOPE || t == '(' || t == ')' || t == '{' || t == ';' ||
           t == ',';
  }

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::maybeTemplateArgs 7\n";
#endif

  return false;
}

/*
  function.body                                       [dcl.fct.def]
  : ctor.initializer? compound.statement
  | function.try.block
  | '=' DEFAULT ';'
  | '=' DELETE ';'

  C++11 [dcl.fct.def] (A.7)
*/

/// Parse C++26 contract attributes: pre(expr) and post(name: expr).
/// Attaches parsed contracts to the function type as ID_C_spec_requires
/// and ID_C_spec_ensures, matching the C front-end contract IR.
bool Parser::rContractAttributes(typet &type)
{
  if(config.cpp.cpp_standard < configt::cppt::cpp_standardt::CPP26)
    return true;

  for(;;)
  {
    cpp_tokent pk;
    int t = lex.LookAhead(0, pk);
    if(!is_identifier(t))
      break;

    irep_idt name = pk.data.get(ID_C_base_name);
    if(name == "pre")
    {
      lex.get_token(pk);
      if(lex.get_token(pk) != '(')
        return false;

      exprt expr;
      if(!rExpression(expr, false))
        return false;

      if(lex.get_token(pk) != ')')
        return false;

      static_cast<exprt &>(type.add(ID_C_spec_requires))
        .operands()
        .push_back(std::move(expr));
    }
    else if(name == "post")
    {
      lex.get_token(pk);
      if(lex.get_token(pk) != '(')
        return false;

      // Check for optional "name:" return value binding
      irep_idt return_value_name;
      cpp_tokent id_tk;
      if(is_identifier(lex.LookAhead(0, id_tk)) && lex.LookAhead(1) == ':')
      {
        return_value_name = id_tk.data.get(ID_C_base_name);
        lex.get_token(id_tk); // consume identifier
        lex.get_token(id_tk); // consume ':'
      }

      exprt expr;
      if(!rExpression(expr, false))
        return false;

      if(lex.get_token(pk) != ')')
        return false;

      // Replace the named return value with __CPROVER_return_value
      if(!return_value_name.empty())
      {
        std::function<void(exprt &)> replace_return_value = [&](exprt &e)
        {
          // At parse time, identifiers are cpp_name with a single
          // "name" sub-element.
          if(
            e.id() == ID_cpp_name && e.get_sub().size() == 1 &&
            e.get_sub().front().id() == ID_name &&
            e.get_sub().front().get(ID_identifier) == return_value_name)
          {
            e.get_sub().front().set(
              ID_identifier, CPROVER_PREFIX "return_value");
          }
          for(auto &op : e.operands())
            replace_return_value(op);
        };
        replace_return_value(expr);
      }

      static_cast<exprt &>(type.add(ID_C_spec_ensures))
        .operands()
        .push_back(std::move(expr));
    }
    else
    {
      break;
    }
  }

  return true;
}

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

    if(auto body = rCompoundStatement())
      declarator.value() = std::move(*body);
    else
    {
      current_function.clear();
      return false;
    }

    current_function.clear();

    return true;
  }
}

/*
  compound.statement                                  [stmt.block]
  : '{' statement.seq? '}'

  C++11 [stmt.block] (A.5)
*/
std::optional<codet> Parser::rCompoundStatement()
{
  cpp_tokent ob, cb;

#ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rCompoundStatement 1\n";
#endif

  if(lex.get_token(ob)!='{')
    return {};

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rCompoundStatement 2\n";
#endif

  code_blockt statement;
  set_location(statement, ob);

  while(lex.LookAhead(0)!='}')
  {
    if(auto statement2 = rStatement())
      statement.add(std::move(*statement2));
    else
    {
      if(!SyntaxError())
        return {}; // too many errors

      SkipTo('}');
      lex.get_token(cb);
      return std::move(statement); // error recovery
    }
  }

  if(lex.get_token(cb)!='}')
    return {};

  return std::move(statement);
}

/*
  statement                                           [gram.stmt]
  : labeled.statement
  | attribute.specifier.seq? expression.statement
  | attribute.specifier.seq? compound.statement
  | attribute.specifier.seq? selection.statement
  | attribute.specifier.seq? iteration.statement
  | attribute.specifier.seq? jump.statement
  | declaration.statement
  | attribute.specifier.seq? try.block

  labeled.statement
  : attribute.specifier.seq? identifier ':' statement
  | attribute.specifier.seq? CASE constant.expression ':' statement
  | attribute.specifier.seq? DEFAULT ':' statement

  jump.statement
  : BREAK ';'
  | CONTINUE ';'
  | RETURN expression? ';'
  | RETURN braced.init.list ';'
  | GOTO identifier ';'

  C++11 [stmt.stmt] (A.5).  Also handles USING declarations and
  STATIC_ASSERT in statement context.
*/
std::optional<codet> Parser::rStatement()
{
  cpp_tokent tk1, tk2, tk3;
  int k;

#ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rStatement 0 "
            << lex.LookAhead(0) << '\n';
#endif

  switch(k=lex.LookAhead(0))
  {
  case '{':
    return rCompoundStatement();

  case TOK_TYPEDEF:
    return rTypedefStatement();

  case TOK_IF:
    return rIfStatement();

  case TOK_SWITCH:
    return rSwitchStatement();

  case TOK_WHILE:
    return rWhileStatement();

  case TOK_DO:
    return rDoStatement();

  case TOK_FOR:
    return rForStatement();

  case TOK_TRY:
    return rTryStatement();

  case TOK_MSC_TRY:
    return rMSC_tryStatement();

  case TOK_MSC_LEAVE:
    return rMSC_leaveStatement();

  case TOK_BREAK:
  case TOK_CONTINUE:
  {
    lex.get_token(tk1);

    codet statement(k == TOK_BREAK ? ID_break : ID_continue);
    set_location(statement, tk1);

    if(lex.get_token(tk2)!=';')
      return {};

    return std::move(statement);
  }
  case TOK_RETURN:
  {
#ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rStatement RETURN 0\n";
#endif

    lex.get_token(tk1);

    code_frontend_returnt statement;
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

      if(lex.LookAhead(0) == '{')
      {
        if(!rInitializeExpr(statement.return_value()))
          return {};
      }
      else if(!rCommaExpression(statement.return_value()))
        return {};

#ifdef DEBUG
      std::cout << std::string(__indent, ' ')
                << "Parser::rStatement RETURN 3\n";
#endif

      if(lex.get_token(tk2)!=';')
        return {};
    }

    return std::move(statement);
  }
  // C++20 co_return: treat as return for verification purposes
  case TOK_CO_RETURN:
  {
    lex.get_token(tk1);

    // co_return in a coroutine doesn't return a value to the caller;
    // the coroutine machinery does.  Model as skip.
    codet statement(ID_skip);
    set_location(statement, tk1);

    if(lex.LookAhead(0) == ';')
    {
      lex.get_token(tk2);
    }
    else
    {
      // co_return expr; — parse and discard the expression
      exprt discard;
      if(lex.LookAhead(0) == '{')
      {
        if(!rInitializeExpr(discard))
          return {};
      }
      else if(!rCommaExpression(discard))
        return {};

      if(lex.get_token(tk2) != ';')
        return {};
    }

    return std::move(statement);
  }
  case TOK_GOTO:
  {
    lex.get_token(tk1);

    if(!is_identifier(lex.get_token(tk2)))
      return {};

    if(lex.get_token(tk3)!=';')
      return {};

    code_gotot statement(tk2.data.get(ID_C_base_name));
    set_location(statement, tk1);

    return std::move(statement);
  }
  case TOK_CASE:
    {
      lex.get_token(tk1);

      exprt case_expr;
      if(!rExpression(case_expr, false))
        return {};

      if(lex.LookAhead(0)==TOK_ELLIPSIS)
      {
        // This is a gcc extension for case ranges.
        // Should really refuse in non-GCC modes.
        lex.get_token(tk2);

        exprt range_end;
        if(!rExpression(range_end, false))
          return {};

        if(lex.get_token(tk2)!=':')
          return {};

        if(auto statement2 = rStatement())
        {
          code_gcc_switch_case_ranget code(
            std::move(case_expr), std::move(range_end), std::move(*statement2));
          set_location(code, tk1);
          return std::move(code);
        }
        else
          return {};
      }
      else
      {
        if(lex.get_token(tk2)!=':')
          return {};

        if(auto statement2 = rStatement())
        {
          code_switch_caset statement(
            std::move(case_expr), std::move(*statement2));
          set_location(statement, tk1);
          return std::move(statement);
        }
        else
          return {};
      }
    }

  case TOK_DEFAULT:
    {
      lex.get_token(tk1);

      if(lex.get_token(tk2)!=':')
        return {};

      if(auto statement2 = rStatement())
      {
        code_switch_caset statement(exprt{}, std::move(*statement2));
        statement.set_default();
        set_location(statement, tk1);
        return std::move(statement);
      }
      else
        return {};
    }

  case TOK_GCC_ASM:
    return rGCCAsmStatement();

  case TOK_MSC_ASM:
    return rMSCAsmStatement();

  case TOK_MSC_IF_EXISTS:
  case TOK_MSC_IF_NOT_EXISTS:
    return rMSC_if_existsStatement();

  case TOK_GCC_IDENTIFIER:
  case TOK_MSC_IDENTIFIER:
    if(lex.LookAhead(1)==':')        // label statement
    {
      // the label
      lex.get_token(tk1);
      // the colon
      lex.get_token(tk2);

      if(auto statement2 = rStatement())
      {
        code_labelt label(tk1.data.get(ID_C_base_name), std::move(*statement2));
        set_location(label, tk1);
        return std::move(label);
      }
      else
        return {};
    }

    return rExprStatement();

  case TOK_USING:
    {
      if(is_identifier(lex.LookAhead(1)) && lex.LookAhead(2) == '=')
      {
        cpp_declarationt declaration;
        if(!rTypedefUsing(declaration))
          return {};
        code_frontend_declt statement(
          static_cast<symbol_exprt &>(static_cast<exprt &>(declaration)));
        statement.add_source_location() = declaration.source_location();
        return std::move(statement);
      }

      cpp_usingt cpp_using;

      if(!rUsing(cpp_using))
        return {};

      // Process using declaration (including using enum)
      codet code("cpp-using");
      code.add("cpp_using", cpp_using);
      return std::move(code);
    }

  case TOK_STATIC_ASSERT:
    {
      cpp_static_assertt cpp_static_assert{nil_exprt(), nil_exprt()};

      if(!rStaticAssert(cpp_static_assert))
        return {};

      codet statement(ID_static_assert);
      statement.add_source_location()=cpp_static_assert.source_location();
      statement.operands().swap(cpp_static_assert.operands());

      return std::move(statement);
    }

    case TOK_GCC_ATTRIBUTE:
    {
      // __attribute__((...)) as a statement (e.g., __attribute__((__assume__(...))))
      typet discard;
      lex.get_token();
      if(!rGCCAttribute(discard))
        return {};
      if(lex.LookAhead(0) == ';')
        lex.get_token();
      return code_skipt();
    }

  default:
    return rExprStatement();
  }
}

/*
  selection.statement: if                             [stmt.if]
  : IF '(' condition ')' statement
  | IF '(' condition ')' statement ELSE statement

  C++11 [stmt.select] (A.5)
*/
std::optional<codet> Parser::rIfStatement()
{
  cpp_tokent tk1, tk2, tk3, tk4;

  if(lex.get_token(tk1)!=TOK_IF)
    return {};

  // C++17 if constexpr
  bool is_constexpr_if = false;
  if(lex.LookAhead(0) == TOK_CONSTEXPR)
  {
    lex.get_token(tk2);
    is_constexpr_if = true;
  }

  // C++23 if consteval: CBMC evaluates constexpr functions at compile
  // time, so always take the consteval (true) branch.
  if(lex.LookAhead(0) == TOK_CONSTEVAL)
  {
    lex.get_token(tk2);

    auto consteval_body = rCompoundStatement();
    if(!consteval_body.has_value())
        return {};

    // Discard else branch if present
    if(lex.LookAhead(0) == TOK_ELSE)
    {
        lex.get_token(tk2);
        auto else_body = rStatement();
        if(!else_body.has_value())
          return {};
    }

    return consteval_body;
  }

  if(lex.get_token(tk2)!='(')
    return {};

  // C++17 if with init-statement: if(init; condition)
  exprt exp;
  codet init_stmt(ID_skip);
  {
    // Try: declaration ';' condition
    auto saved_pos = lex.Save();
    cpp_declarationt init_decl;
    if(rSimpleDeclaration(init_decl) && lex.LookAhead(0) == ';')
    {
        lex.get_token(tk3); // consume ';'
        init_stmt = codet(ID_decl);
        init_stmt.add_to_operands(std::move(init_decl));
        set_location(init_stmt, tk2);
    }
    else
    {
        lex.Restore(saved_pos);

        // Try: structured binding ';' condition
        // auto [a, b] = expr ;
        // auto& [a, b] = expr ;
        bool sb_parsed = false;
        if(lex.LookAhead(0) == TOK_AUTO)
        {
          auto sb_pos = lex.Save();
          lex.get_token(tk3); // consume 'auto'

          bool is_ref = false;
          int t0 = lex.LookAhead(0);
          if(
            t0 == '[' || (t0 == '&' && lex.LookAhead(1) == '[') ||
            (t0 == TOK_ANDAND && lex.LookAhead(1) == '['))
          {
          while(lex.LookAhead(0) == '&' || lex.LookAhead(0) == TOK_ANDAND)
          {
            lex.get_token(tk3);
            is_ref = true;
          }

          if(lex.get_token(tk3) == '[')
          {
            irept bindings(ID_nil);
            bool ok = true;
            while(lex.LookAhead(0) != ']')
            {
            if(lex.LookAhead(0) == ',')
            {
                  lex.get_token(tk3);
                  continue;
            }
            cpp_tokent name_tk;
            if(!is_identifier(lex.get_token(name_tk)))
            {
                  ok = false;
                  break;
            }
            irept binding(name_tk.data.get(ID_C_base_name));
            set_location(binding, name_tk);
            bindings.get_sub().push_back(std::move(binding));
            }
            if(ok)
            {
            lex.get_token(tk3); // ]
            if(lex.LookAhead(0) == '=')
            {
                  lex.get_token(tk3);
                  exprt init;
                  if(rExpression(init, false) && lex.LookAhead(0) == ';')
                  {
                    lex.get_token(tk3); // ;
                    codet sb(irep_idt("structured_binding"), {std::move(init)});
                    sb.add(irep_idt("bindings")) = std::move(bindings);
                    if(is_ref)
                      sb.set(ID_C_reference, true);
                    set_location(sb, tk3);
                    init_stmt = std::move(sb);
                    sb_parsed = true;
                  }
            }
            }
          }
          }

          if(!sb_parsed)
          lex.Restore(sb_pos);
        }

        if(!sb_parsed)
        {
          // Try: expression ';' condition
          exprt init_expr;
          if(rExpression(init_expr, false) && lex.LookAhead(0) == ';')
          {
          lex.get_token(tk3); // consume ';'
          init_stmt = codet(ID_expression);
          init_stmt.add_to_operands(std::move(init_expr));
          set_location(init_stmt, tk2);
          }
          else
          {
          lex.Restore(saved_pos);
          }
        }
    }
  }

  if(!rCondition(exp))
    return {};

  if(lex.get_token(tk3)!=')')
    return {};

  auto then = rStatement();
  if(!then.has_value())
    return {};

  code_ifthenelset if_stmt =
    lex.LookAhead(0) == TOK_ELSE
      ? (lex.get_token(tk4),
         [&]() -> code_ifthenelset
         {
           auto otherwise = rStatement();
           if(!otherwise.has_value())
             return code_ifthenelset{
               std::move(exp), std::move(*then), codet(ID_skip)};
           return code_ifthenelset{
             std::move(exp), std::move(*then), std::move(*otherwise)};
         }())
      : code_ifthenelset{std::move(exp), std::move(*then)};
  set_location(if_stmt, tk1);

  if(is_constexpr_if)
    if_stmt.set(ID_constexpr, true);

  if(init_stmt.get_statement() != ID_skip)
  {
    code_blockt block;
    block.add(std::move(init_stmt));
    block.add(std::move(if_stmt));
    set_location(block, tk1);
    return std::move(block);
  }

  return std::move(if_stmt);
}

/*
  selection.statement: switch                         [stmt.switch]
  : SWITCH '(' condition ')' statement

  C++11 [stmt.select] (A.5)
*/
std::optional<codet> Parser::rSwitchStatement()
{
  cpp_tokent tk1, tk2, tk3;

  if(lex.get_token(tk1)!=TOK_SWITCH)
    return {};

  if(lex.get_token(tk2)!='(')
    return {};

  // C++17 switch with init-statement: switch(init; condition)
  codet init_stmt(ID_skip);
  {
    auto saved_pos = lex.Save();
    cpp_declarationt init_decl;
    if(rSimpleDeclaration(init_decl) && lex.LookAhead(0) == ';')
    {
        lex.get_token(tk3); // consume ';'
        init_stmt = codet(ID_decl);
        init_stmt.add_to_operands(std::move(init_decl));
        set_location(init_stmt, tk2);
    }
    else
    {
        lex.Restore(saved_pos);
        exprt init_expr;
        if(rExpression(init_expr, false) && lex.LookAhead(0) == ';')
        {
          lex.get_token(tk3); // consume ';'
          init_stmt = codet(ID_expression);
          init_stmt.add_to_operands(std::move(init_expr));
          set_location(init_stmt, tk2);
        }
        else
        {
          lex.Restore(saved_pos);
        }
    }
  }

  exprt exp;
  if(!rCondition(exp))
    return {};

  if(lex.get_token(tk3)!=')')
    return {};

  if(auto body = rStatement())
  {
    code_switcht switch_stmt(std::move(exp), std::move(*body));
    set_location(switch_stmt, tk1);

    if(init_stmt.get_statement() != ID_skip)
    {
        code_blockt block;
        block.add(std::move(init_stmt));
        block.add(std::move(switch_stmt));
        set_location(block, tk1);
        return std::move(block);
    }

    return std::move(switch_stmt);
  }
  else
    return {};
}

/*
  iteration.statement: while                          [stmt.while]
  : WHILE '(' condition ')' statement

  C++11 [stmt.iter] (A.5)
*/
std::optional<codet> Parser::rWhileStatement()
{
  cpp_tokent tk1, tk2, tk3;

  if(lex.get_token(tk1)!=TOK_WHILE)
    return {};

  if(lex.get_token(tk2)!='(')
    return {};

  exprt exp;
  if(!rCondition(exp))
    return {};

  if(lex.get_token(tk3)!=')')
    return {};

  if(auto body = rStatement())
  {
    code_whilet statement(std::move(exp), std::move(*body));
    set_location(statement, tk1);
    return std::move(statement);
  }
  else
    return {};
}

/*
  iteration.statement: do                             [stmt.do]
  : DO statement WHILE '(' expression ')' ';'

  C++11 [stmt.iter] (A.5)
*/
std::optional<codet> Parser::rDoStatement()
{
  cpp_tokent tk0, tk1, tk2, tk3, tk4;

  if(lex.get_token(tk0)!=TOK_DO)
    return {};

  auto body = rStatement();
  if(!body.has_value())
    return {};

  if(lex.get_token(tk1)!=TOK_WHILE)
    return {};

  if(lex.get_token(tk2)!='(')
    return {};

  exprt exp;
  if(!rCommaExpression(exp))
    return {};

  if(lex.get_token(tk3)!=')')
    return {};

  if(lex.get_token(tk4)!=';')
    return {};

  code_dowhilet statement(std::move(exp), std::move(*body));
  set_location(statement, tk0);
  return std::move(statement);
}

/*
  iteration.statement: for                            [stmt.for]
  : FOR '(' for.init.statement condition? ';' expression? ')' statement
  | FOR '(' for.range.declaration ':' for.range.initializer ')' statement

  for.init.statement
  : expression.statement
  | simple.declaration

  C++11 [stmt.iter] (A.5)
*/
std::optional<codet> Parser::rForStatement()
{
  cpp_tokent tk1, tk2, tk3, tk4;

  if(lex.get_token(tk1)!=TOK_FOR)
    return {};

  if(lex.get_token(tk2)!='(')
    return {};

  // C++11: try range-based for — for(decl : range)
  {
    cpp_token_buffert::post pos = lex.Save();

    cpp_declarationt declaration;
    if(rTypeSpecifier(declaration.type(), true))
    {
      cpp_declaratort declarator;
      if(
        rDeclarator(declarator, kArgDeclarator, true, false) &&
        lex.LookAhead(0) == ':')
      {
          lex.get_token(tk3); // consume ':'

          exprt range;
          if(rInitializeExpr(range) && lex.get_token(tk4) == ')')
          {
          if(auto body = rStatement())
          {
            declaration.declarators().push_back(declarator);

            codet statement("for_range");
            statement.add_to_operands(
              static_cast<exprt &>(static_cast<irept &>(declaration)));
            statement.add_to_operands(std::move(range));
            statement.add_to_operands(std::move(*body));
            set_location(statement, tk1);
            return std::move(statement);
          }
          return {};
          }
      }
    }

    lex.Restore(pos);
  }

  auto exp1 = rExprStatement();

  if(!exp1.has_value())
    return {};

  // C++20: try for(init; decl : range) after parsing init-statement
  {
    cpp_token_buffert::post pos = lex.Save();

    cpp_declarationt declaration;
    if(rTypeSpecifier(declaration.type(), true))
    {
      cpp_declaratort declarator;
      if(
        rDeclarator(declarator, kArgDeclarator, true, false) &&
        lex.LookAhead(0) == ':')
      {
          lex.get_token(tk3); // consume ':'

          exprt range;
          if(rInitializeExpr(range) && lex.get_token(tk4) == ')')
          {
          if(auto body = rStatement())
          {
            declaration.declarators().push_back(declarator);

            // Wrap init + range-for into a block
            code_blockt block;
            block.add(std::move(*exp1));

            codet range_for("for_range");
            range_for.add_to_operands(
              static_cast<exprt &>(static_cast<irept &>(declaration)));
            range_for.add_to_operands(std::move(range));
            range_for.add_to_operands(std::move(*body));
            set_location(range_for, tk1);
            block.add(std::move(range_for));
            set_location(block, tk1);
            return std::move(block);
          }
          return {};
          }
      }
    }

    lex.Restore(pos);
  }

  exprt exp2;

  if(lex.LookAhead(0)==';')
    exp2.make_nil();
  else
    if(!rCommaExpression(exp2))
    return {};

  if(lex.get_token(tk3)!=';')
    return {};

  exprt exp3;

  if(lex.LookAhead(0)==')')
    exp3.make_nil();
  else
  {
    if(!rCommaExpression(exp3))
      return {};
  }

  if(lex.get_token(tk4)!=')')
    return {};

  if(auto body = rStatement())
  {
    code_fort statement(
      std::move(*exp1), std::move(exp2), std::move(exp3), std::move(*body));
    set_location(statement, tk1);
    return std::move(statement);
  }
  else
    return {};
}

/*
  try.block                                           [except.handle]
  : TRY compound.statement handler.seq

  handler.seq
  : handler handler.seq?

  handler
  : CATCH '(' exception.declaration ')' compound.statement

  exception.declaration
  : attribute.specifier.seq? type.specifier.seq declarator
  | attribute.specifier.seq? type.specifier.seq abstract.declarator?
  | '...'

  C++11 [except] (A.13)
*/
std::optional<codet> Parser::rTryStatement()
{
  cpp_tokent try_token;

  // The 'try' block
  if(lex.get_token(try_token) != TOK_TRY)
    return {};

  auto try_body = rCompoundStatement();
  if(!try_body.has_value())
    return {};

  code_try_catcht statement(std::move(*try_body));
  set_location(statement, try_token);

  // iterate while there are catch clauses
  do
  {
    cpp_tokent catch_token, op_token, cp_token;

    if(lex.get_token(catch_token)!=TOK_CATCH)
      return {};

    if(lex.get_token(op_token)!='(')
      return {};

    std::optional<codet> catch_op;

    if(lex.LookAhead(0)==TOK_ELLIPSIS)
    {
      cpp_tokent ellipsis_token;
      lex.get_token(ellipsis_token);
      codet ellipsis(ID_ellipsis);
      set_location(ellipsis, ellipsis_token);
      catch_op = std::move(ellipsis);
    }
    else
    {
      cpp_declarationt declaration;

      if(!rArgDeclaration(declaration))
        return {};

      // No name in the declarator? Make one.
      DATA_INVARIANT(
        declaration.declarators().size() == 1, "exactly one declarator");

      if(declaration.declarators().front().name().is_nil())
        declaration.declarators().front().name() = cpp_namet("#anon");

      code_frontend_declt code_decl(
        static_cast<symbol_exprt &>(static_cast<exprt &>(declaration)));
      set_location(code_decl, catch_token);

      catch_op = std::move(code_decl);
    }

    if(lex.get_token(cp_token)!=')')
      return {};

    if(auto body = rCompoundStatement())
    {
      code_blockt &block = to_code_block(*body);

      block.statements().insert(block.statements().begin(), *catch_op);

      statement.add_to_operands(std::move(*body));
    }
    else
      return {};
  }
  while(lex.LookAhead(0)==TOK_CATCH);

  return std::move(statement);
}

std::optional<codet> Parser::rMSC_tryStatement()
{
  // These are for 'structured exception handling',
  // and are a relic from Visual C.

  cpp_tokent tk, tk2, tk3;

  if(lex.get_token(tk)!=TOK_MSC_TRY)
    return {};

  auto body1 = rCompoundStatement();

  if(!body1.has_value())
    return {};

  if(lex.LookAhead(0)==TOK_MSC_EXCEPT)
  {
    codet statement(ID_msc_try_except);
    set_location(statement, tk);

    lex.get_token(tk);

    // get '(' comma.expression ')'

    if(lex.get_token(tk2)!='(')
      return {};

    exprt exp;
    if(!rCommaExpression(exp))
      return {};

    if(lex.get_token(tk3)!=')')
      return {};

    if(auto body2 = rCompoundStatement())
    {
      statement.add_to_operands(
        std::move(*body1), std::move(exp), std::move(*body2));
      return std::move(statement);
    }
    else
      return {};
  }
  else if(lex.LookAhead(0)==TOK_MSC_FINALLY)
  {
    codet statement(ID_msc_try_finally);
    set_location(statement, tk);

    lex.get_token(tk);

    if(auto body2 = rCompoundStatement())
    {
      statement.add_to_operands(std::move(*body1), std::move(*body2));
      return std::move(statement);
    }
    else
      return {};
  }
  else
    return {};
}

std::optional<codet> Parser::rMSC_leaveStatement()
{
  // These are for 'structured exception handling',
  // and are a relic from Visual C.

  cpp_tokent tk;

  if(lex.get_token(tk)!=TOK_MSC_LEAVE)
    return {};

  codet statement(ID_msc_leave);
  set_location(statement, tk);

  return std::move(statement);
}

std::optional<codet> Parser::rGCCAsmStatement()
{
  cpp_tokent tk;

#ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rGCCAsmStatement 1\n";
#endif // DEBUG

  // asm [volatile] ("stuff" [ : ["=S" [(__res)], ... ]]) ;

  if(lex.get_token(tk)!=TOK_GCC_ASM)
    return {};

  code_asm_gcct statement;
  set_location(statement, tk);

  if(lex.LookAhead(0)==TOK_VOLATILE)
    lex.get_token(tk);

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rGCCAsmStatement 3\n";
#endif // DEBUG

  if(lex.get_token(tk)!='(')
    return {};
  if(!rString(tk))
    return {};

  statement.asm_text() = tk.data;

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
      return {};

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
          return {};

#ifdef DEBUG
        std::cout << std::string(__indent, ' ')
                  << "Parser::rGCCAsmStatement 6\n";
#endif // DEBUG

        if(lex.get_token(tk)!=')')
          return {};
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
    return {};
  if(lex.get_token(tk)!=';')
    return {};

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rGCCAsmStatement 8\n";
#endif // DEBUG

  return std::move(statement);
}

std::optional<codet> Parser::rMSCAsmStatement()
{
  cpp_tokent tk;

#ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rMSCAsmStatement 1\n";
#endif // DEBUG

  // asm "STUFF"
  // asm { "STUFF" }

  if(lex.get_token(tk)!=TOK_MSC_ASM)
    return {};

  code_asmt statement;
  statement.set_flavor(ID_msc);
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
      return {};

    lex.get_token(tk);

    statement.add_to_operands(std::move(tk.data));
    if(lex.get_token(tk)!='}')
      return {};

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
      return std::move(statement);

    lex.get_token(tk);
    statement.add_to_operands(std::move(tk.data));

#ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rMSCAsmStatement 6\n";
#endif // DEBUG
  }

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rMSCAsmStatement 7\n";
#endif // DEBUG

  return std::move(statement);
}

/*
  expression.statement                                [stmt.expr]
  : expression? ';'

  Also handles declaration.statement when the expression turns out to
  be a declaration.

  C++11 [stmt.expr] (A.5)
*/
std::optional<codet> Parser::rExprStatement()
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
    code_skipt statement;
    set_location(statement, tk);
    return std::move(statement);
  }
  else
  {
#ifdef DEBUG
    std::cout << std::string(__indent, ' ') << "Parser::rExprStatement 2\n";
#endif

    cpp_token_buffert::post pos=lex.Save();

    if(auto statement = rDeclarationStatement())
    {
#ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "rDe " << statement->pretty()
                << '\n';
#endif
      return statement;
    }
    else
    {
      exprt exp;

      lex.Restore(pos);

#ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rExprStatement 3\n";
#endif

      if(!rCommaExpression(exp))
        return {};

#ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rExprStatement 4\n";
#endif

#ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rExprStatement 5 "
                << lex.LookAhead(0) << '\n';
#endif

      if(lex.get_token(tk)!=';')
        return {};

#ifdef DEBUG
      std::cout << std::string(__indent, ' ') << "Parser::rExprStatement 6\n";
#endif

      code_expressiont expr_statement(exp);
      expr_statement.add_source_location() = exp.source_location();
      return std::move(expr_statement);
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
    statement.add_to_operands(std::move(declaration));
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
  declaration.statement                               [stmt.dcl]
  : block.declaration

  block.declaration                                   [dcl.dcl]
  : simple.declaration
  | asm.definition
  | namespace.alias.definition
  | using.declaration
  | using.directive
  | static_assert.declaration
  | alias.declaration

  Note: if you modify this function, take a look at rDeclaration(), too.

  C++11 [stmt.dcl], [dcl.dcl] (A.5, A.6)
*/
std::optional<codet> Parser::rDeclarationStatement()
{
  cpp_storage_spect storage_spec;
  typet cv_q, integral;
  cpp_member_spect member_spec;

#ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ')
            << "Parser::rDeclarationStatement 1\n";
#endif

  cv_q.make_nil();

  if(!optAlignas(cv_q))
    return {};

  if(!optStorageSpec(storage_spec))
    return {};

  if(!optCvQualify(cv_q))
    return {};

  // added for junk like const volatile static ...
  if(!optStorageSpec(storage_spec))
    return {};

  if(!optCvQualify(cv_q))
    return {};

  if(!optIntegralTypeOrClassSpec(integral))
    return {};

#ifdef DEBUG
  std::cout << std::string(__indent, ' ')
            << "Parser::rDeclarationStatement 2\n";
#endif

  if(integral.is_not_nil())
    return rIntegralDeclStatement(storage_spec, integral, cv_q);
  else
  {
    int t=lex.LookAhead(0);

#ifdef DEBUG
    std::cout << std::string(__indent, ' ')
              << "Parser::rDeclarationStatement 3 " << t << '\n';
#endif

    if(
      cv_q.is_not_nil() &&
      ((is_identifier(t) && lex.LookAhead(1) == '=') || t == '*'))
    {
#ifdef DEBUG
      std::cout << std::string(__indent, ' ')
                << "Parser::rDeclarationStatement 4\n";
#endif

      cpp_declarationt declaration;
      if(!rConstDeclaration(declaration))
        return {};
      return code_frontend_declt(
        static_cast<symbol_exprt &>(static_cast<exprt &>(declaration)));
    }
    else
      return rOtherDeclStatement(storage_spec, cv_q);
  }
}

/*
  integral.decl.statement
  : decl.head integral.or.class.spec {cv.qualify} {declarators} ';'
*/
std::optional<codet> Parser::rIntegralDeclStatement(
  cpp_storage_spect &storage_spec,
  typet &integral,
  typet &cv_q)
{
  cpp_tokent tk;

  if(!optCvQualify(cv_q))
    return {};

  merge_types(cv_q, integral);

  cpp_declarationt declaration;
  declaration.type().swap(integral);
  declaration.storage_spec().swap(storage_spec);

  if(lex.LookAhead(0)==';')
  {
    lex.get_token(tk);
    code_frontend_declt statement(
      static_cast<symbol_exprt &>(static_cast<exprt &>(declaration)));
    set_location(statement, tk);
    return std::move(statement);
  }
  else
  {
    // C++17 structured bindings: auto [a, b] = expr;
    // Also auto& [a, b] = expr; and auto&& [a, b] = expr;
    int t0 = lex.LookAhead(0);
    if(
      t0 == '[' || (t0 == '&' && lex.LookAhead(1) == '[') ||
      (t0 == TOK_ANDAND && lex.LookAhead(1) == '[') ||
      (t0 == '&' && lex.LookAhead(1) == '&' && lex.LookAhead(2) == '[') ||
      (t0 == '*' && lex.LookAhead(1) == '['))
    {
      // Parse ref qualifiers
      bool is_ref = false;
      while(lex.LookAhead(0) == '&' || lex.LookAhead(0) == '*' ||
            lex.LookAhead(0) == TOK_ANDAND)
      {
        lex.get_token(tk);
        is_ref = true;
      }

      // Consume [ identifier-list ]
      if(lex.get_token(tk) != '[')
        return {};

      // Collect binding names
      irept bindings(ID_nil);
      while(lex.LookAhead(0) != ']')
      {
        if(lex.LookAhead(0) == ',')
        {
          lex.get_token(tk);
          continue;
        }
        cpp_tokent name_tk;
        if(!is_identifier(lex.get_token(name_tk)))
          return {};
        irept binding(name_tk.data.get(ID_C_base_name));
        set_location(binding, name_tk);
        bindings.get_sub().push_back(std::move(binding));
      }
      lex.get_token(tk); // ]

      // Consume = initializer ;
      exprt init = nil_exprt();
      if(lex.LookAhead(0) == '=')
      {
        lex.get_token(tk);
        if(!rExpression(init, false))
          return {};
      }
      if(lex.get_token(tk) != ';')
        return {};

      codet sb(irep_idt("structured_binding"), {std::move(init)});
      sb.add(irep_idt("bindings")) = std::move(bindings);
      if(is_ref)
        sb.set(ID_C_reference, true);
      set_location(sb, tk);
      return std::move(sb);
    }

    if(!rDeclarators(declaration.declarators(), false, true))
      return {};

    if(lex.get_token(tk)!=';')
      return {};

    code_frontend_declt statement(
      static_cast<symbol_exprt &>(static_cast<exprt &>(declaration)));
    set_location(statement, tk);
    return std::move(statement);
  }
}

/*
   other.decl.statement
   :decl.head name {cv.qualify} declarators ';'
*/
std::optional<codet>
Parser::rOtherDeclStatement(cpp_storage_spect &storage_spec, typet &cv_q)
{
  typet type_name;
  cpp_tokent tk;

#ifdef DEBUG
  indenter _i;
  std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclStatement 1\n";
#endif // DEBUG

  if(!rName(type_name))
    return {};

  // C++20 constrained auto: ConceptName auto
  if(lex.LookAhead(0) == TOK_AUTO)
  {
    cpp_tokent auto_tk;
    lex.get_token(auto_tk);
    type_name = typet(ID_auto);
    set_location(type_name, auto_tk);
  }

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclStatement 2\n";
#endif // DEBUG

  if(!optCvQualify(cv_q))
    return {};

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclStatement 3\n";
#endif // DEBUG

  merge_types(cv_q, type_name);

  cpp_declarationt declaration;
  declaration.type().swap(type_name);
  declaration.storage_spec().swap(storage_spec);

  if(!rDeclarators(declaration.declarators(), false, true))
    return {};

#ifdef DEBUG
  std::cout << std::string(__indent, ' ') << "Parser::rOtherDeclStatement 4\n";
#endif // DEBUG

  if(lex.get_token(tk)!=';')
    return {};

  code_frontend_declt statement(
    static_cast<symbol_exprt &>(static_cast<exprt &>(declaration)));
  set_location(statement, tk);
  return std::move(statement);
}

bool Parser::MaybeTypeNameOrClassTemplate(cpp_tokent &tk)
{
  if(!is_identifier(tk.kind))
    return true;

  irep_idt id = tk.data.get(ID_C_base_name);
  if(id.empty())
    return true;

  new_scopet *found = lookup_id(id);

  // Unknown identifier: assume it could be a type
  if(found == nullptr)
    return true;

  return found->is_type() || found->is_template();
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
    parse_tree.items.push_back(item);
    item.clear();
  }

#if 0
  root_scope.print(std::cout);
#endif

  return number_of_errors!=0;
}

bool cpp_parse(cpp_parsert &cpp_parser, message_handlert &message_handler)
{
  Parser parser(cpp_parser, message_handler);
  return parser();
}
