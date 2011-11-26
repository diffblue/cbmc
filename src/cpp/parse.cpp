#include <assert.h>

#include <expr.h>
#include <std_code.h>
#include <std_types.h>
#include <i2string.h>

#include <ansi-c/concatenate_strings.h>

#include "tokens.h"
#include "cpp_token_buffer.h"
#include "cpp_parser.h"
#include "cpp_member_spec.h"
#include "cpp_enum_type.h"

//#define DEBUG

class Parser
{
public:
  cpp_token_buffert *lex;
  cpp_parsert *parser;

  bool parse();

protected:
  typedef irept Ptree;

  enum DeclKind { kDeclarator, kArgDeclarator, kCastDeclarator };
  enum TemplateDeclKind { tdk_unknown, tdk_decl, tdk_instantiation,
                          tdk_specialization, num_tdks };
  typedef cpp_tokent Token;

  // rules
  bool rProgram(cpp_itemt &item);

  bool SyntaxError();
  void ShowMessageHead(char*);

  bool rDefinition(cpp_itemt &);
  bool rNullDeclaration(cpp_declarationt &);
  bool rTypedef(cpp_declarationt &);
  bool rTypedefStatement(codet &);
  bool rTypeSpecifier(typet &, bool);
  bool isTypeSpecifier();
  bool rLinkageSpec(cpp_linkage_spect &);
  bool rNamespaceSpec(cpp_namespace_spect &);
  bool rUsing(cpp_usingt &);
  bool rLinkageBody(cpp_linkage_spect::itemst &);
  bool rTemplateDecl(cpp_declarationt &);
  bool rTemplateDecl2(typet &, TemplateDeclKind &kind);
  bool rTempArgList(irept &);
  bool rTempArgDeclaration(cpp_declarationt &);
  bool rExternTemplateDecl(irept &);

  bool rDeclaration(cpp_declarationt &);
  bool rIntegralDeclaration(cpp_declarationt &, cpp_storage_spect &, cpp_member_spect &, typet &, typet &);
  bool rConstDeclaration(cpp_declarationt &, cpp_storage_spect &, cpp_member_spect &, typet &);
  bool rOtherDeclaration(cpp_declarationt &, cpp_storage_spect &, cpp_member_spect &, typet &);
  bool rCondition(exprt &);
  bool rSimpleDeclaration(cpp_declarationt &);

  bool isConstructorDecl();
  bool isPtrToMember(int);
  bool optMemberSpec(cpp_member_spect &);
  bool optStorageSpec(cpp_storage_spect &);
  bool optCvQualify(typet &);
  bool rAttribute();
  bool optIntegralTypeOrClassSpec(typet &);
  bool rConstructorDecl(cpp_declaratort &, typet &);
  bool optThrowDecl(irept &);

  bool rDeclarators(cpp_declarationt::declaratorst &, bool, bool=false);
  bool rDeclaratorWithInit(cpp_declaratort &, bool, bool);
  bool rDeclarator(cpp_declaratort &, DeclKind, bool, bool, bool=false);
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
  bool rAccessDecl(irept &);

  bool rCommaExpression(exprt &);

  bool rExpression(exprt &);
  bool rConditionalExpr(exprt &);
  bool rLogicalOrExpr(exprt &, bool);
  bool rLogicalAndExpr(exprt &, bool);
  bool rInclusiveOrExpr(exprt &, bool);
  bool rExclusiveOrExpr(exprt &, bool);
  bool rAndExpr(exprt &, bool);
  bool rEqualityExpr(exprt &, bool);
  bool rRelationalExpr(exprt &, bool);
  bool rShiftExpr(exprt &);
  bool rAdditiveExpr(exprt &);
  bool rMultiplyExpr(exprt &);
  bool rPmExpr(exprt &);
  bool rCastExpr(exprt &);
  bool rTypeName(typet &);
  bool rUnaryExpr(exprt &);
  bool rThrowExpr(exprt &);
  bool rSizeofExpr(exprt &);
  bool rTypeidExpr(exprt &);
  bool isAllocateExpr(int);
  bool rAllocateExpr(exprt &);
  bool rAllocateType(exprt &, typet &, exprt &);
  bool rNewDeclarator(typet &);
  bool rAllocateInitializer(exprt &);
  bool rPostfixExpr(exprt &);
  bool rPrimaryExpr(exprt &);
  bool rMSCTypePredicate(exprt &);
  bool rMSCuuidof(exprt &);
  bool rMSC_if_existsExpr(exprt &);
  bool rVarName(exprt &);
  bool rVarNameCore(exprt &);
  bool isTemplateArgs();

  bool rFunctionBody(codet &);
  bool rCompoundStatement(codet &);
  bool rStatement(codet &);
  bool rIfStatement(codet &);
  bool rSwitchStatement(codet &);
  bool rWhileStatement(codet &);
  bool rDoStatement(codet &);
  bool rForStatement(codet &);
  bool rTryStatement(codet &);
  bool rMSC_tryStatement(codet &);
  bool rMSC_leaveStatement(codet &);
  bool rGCCAsmStatement(codet &);
  bool rMSCAsmStatement(codet &);
  bool rMSC_if_existsStatement(codet &);

  bool rExprStatement(codet &);
  bool rDeclarationStatement(codet &);
  bool rIntegralDeclStatement(codet &, cpp_storage_spect &, typet &, typet &);
  bool rOtherDeclStatement(codet &, cpp_storage_spect &, typet &);

  bool MaybeTypeNameOrClassTemplate(Token&);
  void SkipTo(int token);
  bool moreVarName();

  bool rString(Token &tk);

  unsigned number_of_errors;

  void merge_types(typet &src, typet &dest);

  void set_location(irept &dest, const cpp_tokent &token)
  {
    locationt &location=(locationt &)dest.add(ID_C_location);
    location.set_file(token.filename);
    location.set_line(token.line_no);
  }

  void make_subtype(typet &src, typet &dest)
  {
    typet *p=&dest;
    while(p->id()!=irep_idt() && p->is_not_nil())
      p=&p->subtype();
    p->swap(src);
  }
};

const unsigned int MaxErrors=10;

bool Parser::rString(Token &tk)
{
  if(lex->GetToken(tk)!=TOK_STRING)
    return false;

  // merge with following string literals
  if(lex->LookAhead(0)==TOK_STRING)
  {
    exprt &dest=tk.data;

    while(lex->LookAhead(0)==TOK_STRING)
    {
      Token tk2;
      lex->GetToken(tk2);
      concatenate_strings(dest, tk2.data);
    }
  }

  return true;
}

void Parser::merge_types(typet &src, typet &dest)
{
  if(src.is_nil()) return;

  if(dest.is_nil())
    dest.swap(src);
  else
  {
    if(dest.id()!=ID_merged_type)
    {
      typet tmp(ID_merged_type);
      tmp.move_to_subtypes(dest);
      dest.swap(tmp);
    }

    dest.move_to_subtypes(src);
  }
}

bool Parser::SyntaxError()
{
  #define ERROR_TOKENS 4

  Token t[ERROR_TOKENS];

  for(unsigned i=0; i<ERROR_TOKENS; i++)
    lex->LookAhead(i, t[i]);

  if(t[0].kind!='\0')
  {
    locationt location;
    location.set_file(t[0].filename);
    location.set_line(i2string(t[0].line_no));

    std::string message="parse error before `";

    for(unsigned i=0; i<ERROR_TOKENS; i++)
      if(t[i].kind!='\0')
      {
        if(i!=0) message+=' ';
        message+=t[i].text;
      }

    message+="'";

    parser->print(1, message, -1, location);
  }

  return bool(++number_of_errors < MaxErrors);
}

bool Parser::rProgram(cpp_itemt &item)
{
  while(lex->LookAhead(0)!='\0')
    if(rDefinition(item))
      return true;
    else
    {
      Token tk;

      if(!SyntaxError())
        return false;                // too many errors

      SkipTo(';');
      lex->GetToken(tk);        // ignore ';'
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
  bool res;

  int t=lex->LookAhead(0);

  if(t==';')
    res=rNullDeclaration(item.make_declaration());
  else if(t==TOK_TYPEDEF)
    res=rTypedef(item.make_declaration());
  else if(t==TOK_TEMPLATE)
    res=rTemplateDecl(item.make_declaration());
  else if(t==TOK_EXTERN && lex->LookAhead(1)==TOK_STRING)
    res=rLinkageSpec(item.make_linkage_spec());
  else if(t==TOK_EXTERN && lex->LookAhead(1)==TOK_TEMPLATE)
    res=rExternTemplateDecl(item.make_declaration());
  else if(t==TOK_NAMESPACE)
    res=rNamespaceSpec(item.make_namespace_spec());
  else if(t==TOK_USING)
    res=rUsing(item.make_using());
  else
    res=rDeclaration(item.make_declaration());

  return res;
}

bool Parser::rNullDeclaration(cpp_declarationt &decl)
{
  Token tk;

  if(lex->GetToken(tk)!=';')
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
  Token tk;
  typet type_name;

  if(lex->GetToken(tk)!=TOK_TYPEDEF)
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rTypedef 1\n";
  #endif

  declaration=cpp_declarationt();
  set_location(declaration, tk);

  declaration.type()=typet(ID_typedef);

  if(!rTypeSpecifier(type_name, false))
    return false;

  merge_types(type_name, declaration.type());

  #ifdef DEBUG
  std::cout << "Parser::rTypedef 2\n";
  #endif

  if(!rDeclarators(declaration.declarators(), true))
    return false;

  if(lex->GetToken(tk)!=';')
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rTypedef 3\n";
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
  typet cv_q;

  cv_q.make_nil();

  if(!optCvQualify(cv_q))
    return false;

  if(!optIntegralTypeOrClassSpec(tspec))
    return false;

  if(tspec.is_nil())
  {
    Token tk;
    lex->LookAhead(0, tk);

    if(check)
      if(!MaybeTypeNameOrClassTemplate(tk))
        return false;

    if(!rName(tspec))
      return false;
  }

  if(!optCvQualify(cv_q))
    return false;

  merge_types(cv_q, tspec);

  return true;
}

// isTypeSpecifier() returns true if the next is probably a type specifier.

bool Parser::isTypeSpecifier()
{
  int t=lex->LookAhead(0);

  if(t==TOK_IDENTIFIER || t==TOK_SCOPE
       || t==TOK_CONST || t==TOK_VOLATILE
       || t==TOK_CHAR || t==TOK_INT || t==TOK_SHORT || t==TOK_LONG
       || t==TOK_WCHAR_T || t==TOK_COMPLEX // new !!!
       || t==TOK_SIGNED || t==TOK_UNSIGNED || t==TOK_FLOAT || t==TOK_DOUBLE
       || t==TOK_INT8 || t==TOK_INT16 || t==TOK_INT32 || t==TOK_INT64 || t==TOK_PTR32 || t==TOK_PTR64
       || t==TOK_VOID || t==TOK_BOOL
       || t==TOK_CLASS || t==TOK_STRUCT || t==TOK_UNION || t==TOK_ENUM || t==TOK_INTERFACE
       || t==TOK_TYPENAME
       || t==TOK_INT64
       || t==TOK_TYPEOF
       || t==TOK_DECLTYPE
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
  Token tk1, tk2;

  if(lex->GetToken(tk1)!=TOK_EXTERN)
    return false;

  if(!rString(tk2))
    return false;

  linkage_spec=cpp_linkage_spect();
  set_location(linkage_spec, tk1);
  linkage_spec.linkage().swap(tk2.data);
  set_location(linkage_spec.linkage(), tk2);

  if(lex->LookAhead(0)=='{')
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
  : NAMESPACE Identifier definition
  | NAMESPACE Identifier = name
  | NAMESPACE { Identifier } linkage.body
*/

bool Parser::rNamespaceSpec(cpp_namespace_spect &namespace_spec)
{
  Token tk1, tk2;

  if(lex->GetToken(tk1)!=TOK_NAMESPACE)
    return false;

  std::string name;

  if(lex->LookAhead(0)=='{')
    name="";
  else
  {
    if(lex->GetToken(tk2)==TOK_IDENTIFIER)
      name.swap(tk2.text);
    else
      return false;
  }

  namespace_spec=cpp_namespace_spect();
  set_location(namespace_spec, tk1);
  namespace_spec.set_namespace(name);

  switch(lex->LookAhead(0))
  {
  case '{':
    return rLinkageBody(namespace_spec.items());
    
  case '=': // namespace alias
    lex->GetToken(tk2); // eat =
    return rName(namespace_spec.alias());

  default:
    namespace_spec.items().push_back(cpp_itemt());
    return rDefinition(namespace_spec.items().back());
  }

  // unreachable
  return true;
}

/*
  using.declaration : USING { NAMESPACE } name ';'
*/
bool Parser::rUsing(cpp_usingt &cpp_using)
{
  Token tk;

  if(lex->GetToken(tk)!=TOK_USING)
    return false;

  cpp_using=cpp_usingt();
  set_location(cpp_using, tk);

  if(lex->LookAhead(0)==TOK_NAMESPACE)
  {
    lex->GetToken(tk);
    cpp_using.set_namespace(true);
  }

  if(!rName(cpp_using.name()))
    return false;

  if(lex->GetToken(tk)!=';')
    return false;

  return true;
}

/*
  linkage.body : '{' (definition)* '}'

  Note: this is also used to construct namespace.spec
*/
bool Parser::rLinkageBody(cpp_linkage_spect::itemst &items)
{
  Token op, cp;

  if(lex->GetToken(op)!='{')
    return false;

  items.clear();
  while(lex->LookAhead(0)!='}')
  {
    cpp_itemt item;

    if(!rDefinition(item))
    {
      if(!SyntaxError())
        return false;                // too many errors

      SkipTo('}');
      lex->GetToken(cp);
      items.push_back(item);
      return true;                // error recovery
    }

    items.push_back(item);
  }

  lex->GetToken(cp);
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

  typet template_type;
  if(!rTemplateDecl2(template_type, kind))
    return false;

  cpp_declarationt body;
  if(!rDeclaration(body))
    return false;

  // Repackage the decl and body depending upon what kind of template
  // declaration was observed.
  switch(kind)
  {
  case tdk_decl:
    #ifdef DEBUG
    std::cout << "BODY: " << body << std::endl;
    std::cout << "TEMPLATE_TYPE: " << template_type << std::endl;
    #endif

    body.add(ID_template_type).swap(template_type);
    body.set(ID_is_template, true);
    decl.swap(body);
    break;

  case tdk_instantiation:
    // Repackage the decl
    decl=body;
    assert(0);
    // assumes that decl has the form: [nil [class ...] ;]
    #if 0
    if(Ptree::Length(decl)!=3)
      return false;

    if(Ptree::First(decl).is_not_nil())
      return false;

    if(Ptree::Second(decl)->What()!=ntClassSpec)
      return false;

    if(!Ptree::Eq(Ptree::Third(decl), ';'))
      return false;
    #endif

    //decl=new PtreeTemplateInstantiation(Ptree::Second(decl));
    break;

  case tdk_specialization:
    body.add(ID_template_type).swap(template_type);
    body.set(ID_is_template, true);
    decl.swap(body);
    break;

   default:
    assert(0);
    break;
  }

  return true;
}

bool Parser::rTemplateDecl2(typet &decl, TemplateDeclKind &kind)
{
  Token tk;

  if(lex->GetToken(tk)!=TOK_TEMPLATE)
    return false;

  decl=typet(ID_template);
  set_location(decl, tk);

  if(lex->LookAhead(0)!='<')
  {
    // template instantiation
    kind=tdk_instantiation;
    return true;        // ignore TEMPLATE
  }

  if(lex->GetToken(tk)!='<')
    return false;

  irept &args=decl.add(ID_arguments);

  if(!rTempArgList(args))
      return false;

  if(lex->GetToken(tk)!='>')
      return false;

  // ignore nested TEMPLATE
  while (lex->LookAhead(0)==TOK_TEMPLATE)
  {
    lex->GetToken(tk);
    if(lex->LookAhead(0)!='<')
      break;

    lex->GetToken(tk);
    irept dummy_args;
    if(!rTempArgList(dummy_args))
      return false;

    if(lex->GetToken(tk)!='>')
      return false;
  }

  if(args.get_sub().empty())
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
  if(lex->LookAhead(0)=='>')
    return true;

  cpp_declarationt a;
  if(!rTempArgDeclaration(a))
    return false;

  args.get_sub().push_back(get_nil_irep());
  args.get_sub().back().swap(a);

  while(lex->LookAhead(0)==',')
  {
    Token tk;

    lex->GetToken(tk);
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
  | type.specifier arg.declarator {'=' additive.expr}
  | template.decl2 CLASS Identifier {'=' type.name}
*/
bool Parser::rTempArgDeclaration(cpp_declarationt &declaration)
{
  int t0=lex->LookAhead(0);

  if((t0==TOK_CLASS || t0==TOK_TYPENAME))
  {
    Token tk1;
    lex->GetToken(tk1);

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

    if(lex->LookAhead(0) == TOK_IDENTIFIER)
    {
      cpp_namet cpp_name;
      Token tk2;
      lex->GetToken(tk2);

      exprt name(ID_name);
      set_location(name, tk2);
      name.set(ID_identifier, tk2.text);
      set_location(name,tk1);
      cpp_name.get_sub().push_back(name);
      declarator.name().swap(cpp_name);
    }

    if(lex->LookAhead(0)=='=')
    {
      typet default_type;

      lex->GetToken(tk1);
      if(!rTypeName(default_type))
          return false;

      declarator.value()=exprt(ID_type);
      declarator.value().type().swap(default_type);
    }
  }
  else if(t0==TOK_TEMPLATE)
  {
    TemplateDeclKind kind;

    typet template_type;

    if(!rTemplateDecl2(template_type, kind))
      return false;

    // TODO!

    Token tk1, tk2;

    if(lex->GetToken(tk1)!=TOK_CLASS ||
       lex->GetToken(tk2)!=TOK_IDENTIFIER)
      return false;

    //Ptree cspec=new PtreeClassSpec(new LeafReserved(tk1),
    //                                  Ptree::Cons(new Leaf(tk2),nil),
    //                                  nil);
    //decl=Ptree::Snoc(decl, cspec);
    if(lex->LookAhead(0)=='=')
    {
      typet default_type;
      lex->GetToken(tk1);
      if(!rTypeName(default_type))
          return false;

      //decl=Ptree::Nconc(decl, Ptree::List(new Leaf(tk1),
      //                                      default_type));
    }
  }
  else
  {
    declaration=cpp_declarationt();
    declaration.set(ID_is_type, false);

    if(!rTypeSpecifier(declaration.type(), true))
      return false;

    declaration.declarators().resize(1);
    cpp_declaratort &declarator=declaration.declarators().front();

    if(!rDeclarator(declarator, kArgDeclarator, false, true))
      return false;

    exprt &value=declarator.value();

    if(lex->LookAhead(0)=='=')
    {
      Token tk;

      lex->GetToken(tk);
      if(!rAdditiveExpr(value))
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
bool Parser::rExternTemplateDecl(irept &decl)
{
  Token tk1, tk2;

  if(lex->GetToken(tk1)!=TOK_EXTERN)
    return false;

  if(lex->GetToken(tk2)!=TOK_TEMPLATE)
    return false;

  cpp_declarationt body;
  if(!rDeclaration(body))
    return false;

  //decl=new PtreeExternTemplate(new Leaf(tk1),
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
  std::cout << "Parser::rDeclaration 0.1  token: " << lex->LookAhead(0) << std::endl;
  #endif

  cpp_member_spect member_spec;
  if(!optMemberSpec(member_spec))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rDeclaration 0.2\n";
  #endif

  cpp_storage_spect storage_spec;
  if(!optStorageSpec(storage_spec))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rDeclaration 1\n";
  #endif

  if(member_spec.is_empty())
    if(!optMemberSpec(member_spec))
      return false;

  #ifdef DEBUG
  std::cout << "Parser::rDeclaration 3\n";
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
  std::cout << "Parser::rDeclaration 4\n";
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
    std::cout << "Parser::rDeclaration 5\n";
    #endif
    return rIntegralDeclaration(declaration, storage_spec, member_spec, integral, cv_q);
  }
  else
  {
    int t=lex->LookAhead(0);

    #ifdef DEBUG
    std::cout << "Parser::rDeclaration 6 " << t << "\n";
    #endif

    if(cv_q.is_not_nil() &&
       ((t==TOK_IDENTIFIER && lex->LookAhead(1)=='=') || t=='*'))
      return rConstDeclaration(declaration, storage_spec, member_spec, cv_q);
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

  cpp_declaratort declarator;
  if(!rDeclarator(declarator, kDeclarator, false, true, true))
    return false;

  if(lex->LookAhead(0)!='=')
    return false;

  Token eqs;
  lex->GetToken(eqs);

  //int t=lex->LookAhead(0);

  exprt e;
  if(!rExpression(e))
    return false;

  //Ptree::Nconc(d, Ptree::List(new Leaf(eqs), e));

  //statement=new PtreeDeclaration(0, Ptree::List(integral,
  //                                                Ptree::List(d)));
  // TODO
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
  std::cout << "Parser::rIntegralDeclaration 1  token: "
            << (char) lex->LookAhead(0) << "\n";
  #endif

  if(!optCvQualify(cv_q))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rIntegralDeclaration 2\n";
  #endif

  merge_types(cv_q, integral);

  #ifdef DEBUG
  std::cout << "Parser::rIntegralDeclaration 3\n";
  #endif

  declaration.type().swap(integral);
  declaration.storage_spec().swap(storage_spec);
  declaration.member_spec().swap(member_spec);

  Token tk;

  switch(lex->LookAhead(0))
  {
  case ';':
    #ifdef DEBUG
    std::cout << "Parser::rIntegralDeclaration 4\n";
    #endif

    lex->GetToken(tk);
    return true;

  case ':':        // bit field
    #ifdef DEBUG
    std::cout << "Parser::rIntegralDeclaration 5\n";
    #endif

    lex->GetToken(tk);

    {
      exprt width;

      if(!rExpression(width))
        return false;

      if(lex->GetToken(tk)!=';')
        return false;

      // TODO
    }
    return true;

  default:
    #ifdef DEBUG
    std::cout << "Parser::rIntegralDeclaration 6 "
              << lex->LookAhead(0) << "\n";
    #endif

    if(!rDeclarators(declaration.declarators(), true))
      return false;

    #ifdef DEBUG
    std::cout << "Parser::rIntegralDeclaration 7\n";
    #endif

    if(lex->LookAhead(0)==';')
    {
      #ifdef DEBUG
      std::cout << "Parser::rIntegralDeclaration 8 "
                << declaration << "\n";
      #endif

      lex->GetToken(tk);
      return true;
    }
    else
    {
      #ifdef DEBUG
      std::cout << "Parser::rIntegralDeclaration 9\n";
      #endif

      if(declaration.declarators().size()!=1)
        return false;

      codet body;
      if(!rFunctionBody(body))
        return false;

      if(declaration.declarators().size()!=1)
        return false;

      declaration.declarators().front().value().swap(body);

      #ifdef DEBUG
      std::cout << "Parser::rIntegralDeclaration 10\n";
      #endif

      return true;
    }
  }
}

bool Parser::rConstDeclaration(
  cpp_declarationt &declaration,
  cpp_storage_spect &storage_spec,
  cpp_member_spect &member_spec,
  typet &cv_q)
{
  #ifdef DEBUG
  std::cout << "Parser::rConstDeclaration\n";
  #endif

  cpp_declarationt::declaratorst declarators;

  if(!rDeclarators(declarators, false))
    return false;

  if(lex->LookAhead(0)!=';')
    return false;

  Token tk;
  lex->GetToken(tk);

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
  std::cout << "Parser::rOtherDeclaration 1\n";
  #endif

  if(!rName(type_name))
    return false;
    
  merge_types(cv_q, type_name);

  #ifdef DEBUG
  std::cout << "Parser::rOtherDeclaration 2\n";
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
  std::cout << "Parser::rOtherDeclaration 3\n";
  #endif

  bool is_constructor = isConstructorDecl();
  bool is_operator = false;

  if(is_constructor)
  {
    #ifdef DEBUG
    std::cout << "Parser::rOtherDeclaration 4\n";
    #endif

    assert(!type_name.get_sub().empty());

    for(unsigned i=0; i < type_name.get_sub().size(); i++)
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
    std::cout << "Parser::rOtherDeclaration 5\n";
    #endif
    
    // it's a conversion operator
    typet type = type_name;
    type.get_sub().erase(type.get_sub().begin());

    cpp_declaratort conv_operator_declarator;
    if(!rConstructorDecl(conv_operator_declarator, type_name))
      return false;

    type_name=typet("cpp-cast-operator");

    declaration.declarators().push_back(conv_operator_declarator);
  }
  else if(cv_q.is_nil() && is_constructor)
  {
    #ifdef DEBUG
    std::cout << "Parser::rOtherDeclaration 6\n";
    #endif

    assert(!type_name.get_sub().empty());

    bool is_destructor=false;
    forall_irep(it, type_name.get_sub())
      if(it->id()=="~") { is_destructor=true; break; }

    cpp_declaratort constructor_declarator;
    if(!rConstructorDecl(constructor_declarator, type_name))
      return false;

    #ifdef DEBUG
    std::cout << "Parser::rOtherDeclaration 7\n";
    #endif

    // it's the name (declarator), not the return type

    type_name=typet(is_destructor?ID_destructor:ID_constructor);
    declaration.declarators().push_back(constructor_declarator);
  }
  else if(!member_spec.is_empty() && lex->LookAhead(0)==';')
  {
    #ifdef DEBUG
    std::cout << "Parser::rOtherDeclaration 8\n";
    #endif

    // FRIEND name ';'
    //if(Ptree::Length(member_spec)==1 && member_spec->Car()->What()==FRIEND)
    {
      Token tk;
      lex->GetToken(tk);
      //statement=new PtreeDeclaration(head, Ptree::List(type_name,
      //                                                   new Leaf(tk)));
      return true;
    }
    //else
    //  return false;
  }
  else
  {
    #ifdef DEBUG
    std::cout << "Parser::rOtherDeclaration 9\n";
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
  std::cout << "Parser::rOtherDeclaration 10\n";
  #endif

  if(lex->LookAhead(0)==';')
  {
    #ifdef DEBUG
    std::cout << "Parser::rOtherDeclaration 11\n";
    #endif

    Token tk;
    lex->GetToken(tk);
  }
  else
  {
    #ifdef DEBUG
    std::cout << "Parser::rOtherDeclaration 12;\n";
    #endif

    if(declaration.declarators().size()!=1)
      return false;

    if(!rFunctionBody((codet &)declaration.declarators().front().value()))
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
  std::cout << "Parser::isConstructorDecl "<< lex->LookAhead(0)
            << "  "<< lex->LookAhead(1) << "\n";
  #endif

  if(lex->LookAhead(0)!='(')
    return false;
  else
  {
    int t=lex->LookAhead(1);
    if(t=='*' || t=='&' || t=='(')
      return false;        // it's a declarator
    else if(t==TOK_STDCALL || t==TOK_FASTCALL || t==TOK_CLRCALL || t==TOK_CDECL)
      return false;        // it's a declarator
    else if(isPtrToMember(1))
      return false;        // declarator (::*)

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
  int t0=lex->LookAhead(i++);

  if(t0==TOK_SCOPE)
      t0=lex->LookAhead(i++);

  while(t0==TOK_IDENTIFIER)
  {
    int t=lex->LookAhead(i++);
    if(t=='<')
    {
      int n=1;
      while(n > 0)
      {
        int u=lex->LookAhead(i++);
        if(u=='<')
          ++n;
        else if(u=='>')
          --n;
        else if(u=='(')
        {
          int m=1;
          while(m > 0)
          {
            int v=lex->LookAhead(i++);
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

      t=lex->LookAhead(i++);
    }

    if(t!=TOK_SCOPE)
      return false;

    t0=lex->LookAhead(i++);

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

  int t=lex->LookAhead(0);

  while(t==TOK_FRIEND || t==TOK_INLINE || t==TOK_VIRTUAL || t==TOK_EXPLICIT)
  {
    Token tk;
    lex->GetToken(tk);

    switch(t)
    {
    case TOK_INLINE:   member_spec.set_inline(true); break;
    case TOK_VIRTUAL:  member_spec.set_virtual(true); break;
    case TOK_FRIEND:   member_spec.set_friend(true); break;
    case TOK_EXPLICIT: member_spec.set_explicit(true); break;
    default: assert(false);
    }

    t=lex->LookAhead(0);
  }

  return true;
}

/*
  storage.spec : STATIC | EXTERN | AUTO | REGISTER | MUTABLE
*/
bool Parser::optStorageSpec(cpp_storage_spect &storage_spec)
{
  int t=lex->LookAhead(0);

  if(t==TOK_STATIC ||
     t==TOK_EXTERN ||
     t==TOK_AUTO ||
     t==TOK_REGISTER ||
     t==TOK_MUTABLE)
  {
    Token tk;
    lex->GetToken(tk);

    switch(t)
    {
    case TOK_STATIC: storage_spec.set_static(); break;
    case TOK_EXTERN: storage_spec.set_extern(); break;
    case TOK_AUTO: storage_spec.set_auto(); break;
    case TOK_REGISTER: storage_spec.set_register(); break;
    case TOK_MUTABLE: storage_spec.set_mutable(); break;
    default: assert(false);
    }

    set_location(storage_spec, tk);
  }

  return true;
}

/*
  cv.qualify : (CONST | VOLATILE)+
*/
bool Parser::optCvQualify(typet &cv)
{
  for(;;)
  {
    int t=lex->LookAhead(0);
    if(t==TOK_CONST || t==TOK_VOLATILE ||
       t==TOK_PTR32 || t==TOK_PTR64 ||
       t==TOK_ATTRIBUTE)
    {
      Token tk;
      lex->GetToken(tk);
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

      case TOK_ATTRIBUTE:
        if(!rAttribute())
          return false;
        break;

      default:
        assert(false);
        break;
      }
    }
    else
      break;
  }

  return true;
}

bool Parser::rAttribute()
{
  Token tk;
  lex->GetToken(tk);

  switch(tk.kind)
  {
   case '(':
    rAttribute();
    if(lex->LookAhead(0)!=')') return false;
    lex->GetToken(tk);
    break;

   case TOK_IDENTIFIER:
    break;

   default:
    return false;
  }

  return true;
}

/*

  !!! added WCHAR_T

  integral.or.class.spec
  : (CHAR | WCHAR_T | INT | SHORT | LONG | SIGNED | UNSIGNED | FLOAT | DOUBLE
     | VOID | BOOLEAN | COMPLEX)+
  | class.spec
  | enum.spec

  Note: if editing this, see also isTypeSpecifier().
*/
bool Parser::optIntegralTypeOrClassSpec(typet &p)
{
  bool is_integral;
  int t;

  #ifdef DEBUG
  std::cout << "Parser::optIntegralTypeOrClassSpec 0\n";
  #endif // DEBUG

  is_integral=false;
  p.make_nil();

  for(;;)
  {
    t=lex->LookAhead(0);

    #ifdef DEBUG
    std::cout << "Parser::optIntegralTypeOrClassSpec 1\n";
    #endif // DEBUG

    if(t==TOK_CHAR || t==TOK_INT || t==TOK_SHORT || t==TOK_LONG || t==TOK_SIGNED
       || t==TOK_WCHAR_T || t==TOK_COMPLEX // new !!!
       || t==TOK_UNSIGNED || t==TOK_FLOAT || t==TOK_DOUBLE || t==TOK_VOID
       || t==TOK_INT8 || t==TOK_INT16 || t==TOK_INT32 || t==TOK_INT64
       || t==TOK_BOOL
       )
    {
      Token tk;
      typet kw;
      lex->GetToken(tk);
      kw=typet(tk.text);
      set_location(kw, tk);

      merge_types(kw, p);

      is_integral=true;
    }
    else
      break;
  }

  #ifdef DEBUG
  std::cout << "Parser::optIntegralTypeOrClassSpec 2\n";
  #endif // DEBUG

  if(is_integral)
    return true;

  #ifdef DEBUG
  std::cout << "Parser::optIntegralTypeOrClassSpec 3\n";
  #endif // DEBUG

  if(t==TOK_CLASS || t==TOK_STRUCT || t==TOK_UNION || t==TOK_INTERFACE)
    return rClassSpec(p);
  else if(t==TOK_ENUM)
    return rEnumSpec(p);
  else if(t==TOK_TYPEOF)
  {
    #ifdef DEBUG
    std::cout << "Parser::optIntegralTypeOrClassSpec 4\n";
    #endif // DEBUG

    Token typeof_tk;
    lex->GetToken(typeof_tk);

    #ifdef DEBUG
    std::cout << "Parser::optIntegralTypeOrClassSpec 5\n";
    #endif // DEBUG

    p=typet(ID_typeof);
    set_location(p, typeof_tk);

    Token tk;
    if(lex->GetToken(tk)!='(') return false;
    
    // the argument can be a type or an expression

    {
      typet tname;
      cpp_token_buffert::post pos=lex->Save();

      if(rTypeName(tname))
        if(lex->GetToken(tk)==')')
        {
          p.add(ID_type_arg).swap(tname);
          return true;
        }

      lex->Restore(pos);
    }

    #ifdef DEBUG
    std::cout << "Parser::optIntegralTypeOrClassSpec 6\n";
    #endif // DEBUG

    exprt expr;
    if(!rCommaExpression(expr)) return false;

    #ifdef DEBUG
    std::cout << "Parser::optIntegralTypeOrClassSpec 7\n";
    #endif // DEBUG

    if(lex->GetToken(tk)!=')') return false;

    #ifdef DEBUG
    std::cout << "Parser::optIntegralTypeOrClassSpec 8\n";
    #endif // DEBUG

    p.add(ID_expr_arg).swap(expr);

    return true;
  }
  else if(t==TOK_DECLTYPE)
  {
    Token decltype_tk;
    lex->GetToken(decltype_tk);

    p=typet(ID_decltype);
    set_location(p, decltype_tk);

    Token tk;
    if(lex->GetToken(tk)!='(') return false;
    
    // the argument is always an expression

    exprt expr;
    if(!rCommaExpression(expr)) return false;

    if(lex->GetToken(tk)!=')') return false;

    p.add(ID_expr_arg).swap(expr);

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
  typet &type_name)
{
  #ifdef DEBUG
  std::cout << "Parser::rConstructorDecl 0\n";
  #endif

  constructor=cpp_declaratort(typet("function_type"));
  constructor.type().subtype().make_nil();
  constructor.name().swap(type_name);

  Token op;
  if(lex->GetToken(op)!='(')
    return false;

  irept &arguments=constructor.type().add(ID_arguments);

  if(lex->LookAhead(0)!=')')
    if(!rArgDeclList(arguments))
      return false;

  Token cp;
  lex->GetToken(cp);

  typet &cv=(typet &)constructor.add(ID_method_qualifier);
  cv.make_nil();
  optCvQualify(cv);

  optThrowDecl(constructor.throw_decl());

  if(lex->LookAhead(0)==':')
  {
    irept mi;

    if(rMemberInitializers(mi))
      constructor.member_initializers().swap(mi);
    else
      return false;
  }

  if(lex->LookAhead(0)=='=')
  {
    Token eq, zero;
    lex->GetToken(eq);

    if(lex->GetToken(zero)!=TOK_INTEGER)
      return false;

    exprt pure_virtual(ID_code);
    pure_virtual.set(ID_statement, "cpp-pure-virtual");

    constructor.add(ID_value).swap(pure_virtual);
  }
  else
    constructor.add(ID_value).make_nil();

  return true;
}

/*
  throw.decl : THROW '(' (name {','})* {name} ')'
             : THROW '(' '...' ')'
*/
bool Parser::optThrowDecl(irept &throw_decl)
{
  Token tk;
  int t;
  irept p=get_nil_irep();

  if(lex->LookAhead(0)==TOK_THROW)
  {
    lex->GetToken(tk);
    //p=Ptree::Snoc(p, new LeafReserved(tk));

    if(lex->GetToken(tk)!='(')
      return false;

    //p=Ptree::Snoc(p, new Leaf(tk));

    for(;;)
    {
      irept q;
      t=lex->LookAhead(0);
      if(t=='\0')
        return false;
      else if(t==')')
        break;
      else if(t==TOK_ELLIPSIS)
      {
        lex->GetToken(tk);
      }
      else if(rName(q))
      {
        //  p=Ptree::Snoc(p, q);
      }
      else
        return false;

      if(lex->LookAhead(0)==',')
      {
        lex->GetToken(tk);
        //p=Ptree::Snoc(p, new Leaf(tk));
      }
      else
        break;
    }

    if(lex->GetToken(tk)!=')')
      return false;

    //p=Ptree::Snoc(p, new Leaf(tk));
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
  Token tk;

  for(;;)
  {
    cpp_declaratort declarator;
    if(!rDeclaratorWithInit(declarator, should_be_declarator, is_statement))
      return false;

    declarators.push_back(declarator);

    if(lex->LookAhead(0)==',')
      lex->GetToken(tk);
    else
      return true;
  }
}

/*
  declarator.with.init
  : ':' expression
  | declarator {'=' initialize.expr | ':' expression}
*/
bool Parser::rDeclaratorWithInit(
  cpp_declaratort &dw,
  bool should_be_declarator,
  bool is_statement)
{
  if(lex->LookAhead(0)==':')        // bit field
  {
    Token tk;
    lex->GetToken(tk);

    exprt e;
    if(!rExpression(e))
      return false;

    //dw=Ptree::List(new Leaf(tk), e);
    return true;
  }
  else
  {
    cpp_declaratort declarator;

    if(!rDeclarator(declarator, kDeclarator, false,
                    should_be_declarator, is_statement))
      return false;
    
    // asm post-declarator
    if(lex->LookAhead(0)==TOK_GCC_ASM)
    {
      // this is stuff like
      // int x __asm("asd")=1, y;
      Token tk;
      lex->GetToken(tk); // TOK_GCC_ASM

      if(lex->GetToken(tk)!='(') return false;
      if(!rString(tk)) return false;
      if(lex->GetToken(tk)!=')') return false;
    }
    
    int t=lex->LookAhead(0);
    if(t=='=')
    {
      // initializer
      Token tk;
      lex->GetToken(tk);
      if(!rInitializeExpr(declarator.value()))
        return false;

      dw.swap(declarator);
      return true;
    }
    else if(t==':')
    {
      // bit field
      exprt e;

      Token tk;
      lex->GetToken(tk);
      if(!rExpression(e))
        return false;

      //dw=Ptree::Nconc(d, Ptree::List(new Leaf(tk), e));
      // TODO
      dw.swap(declarator);
      return true;
    }
    else
    {
      dw.swap(declarator);
      return true;
    }
  }
}

/* __stdcall, __fastcall, __clrcall, __cdecl 

   These are Visual-Studio specific.
   
*/

bool Parser::rDeclaratorQualifier()
{
  int t=lex->LookAhead(0);

  // we just eat these

  while(t==TOK_STDCALL || t==TOK_FASTCALL || t==TOK_CLRCALL || t==TOK_CDECL)
  {
    Token op;
    lex->GetToken(op);
    t=lex->LookAhead(0);
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
  bool recursive,
  bool should_be_declarator,
  bool is_statement)
{
  int t;

  #ifdef DEBUG
  std::cout << "Parser::rDeclarator2 1\n";
  #endif
  
  // we can have one or more declatator qualifiers
  if(!rDeclaratorQualifier())
    return false;

  typet d_outer, d_inner;
  irept name;

  name.make_nil();
  d_outer.make_nil();
  d_inner.make_nil();
  
  if(!optPtrOperator(d_outer))
    return false;

  // we can have another sequence of declatator qualifiers
  if(!rDeclaratorQualifier())
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rDeclarator2 2\n";
  #endif

  t=lex->LookAhead(0);

  if(t=='(')
  {
    #ifdef DEBUG
    std::cout << "Parser::rDeclarator2 3\n";
    #endif

    Token op;
    lex->GetToken(op);

    cpp_declaratort declarator2;
    if(!rDeclarator(declarator2, kind, true, true, false))
      return false;

    Token cp;

    if(lex->GetToken(cp)!=')')
      return false;

    if(!should_be_declarator)
      if(kind==kDeclarator && d_outer.is_nil())
      {
        t=lex->LookAhead(0);
        if(t!='[' && t!='(')
          return false;
      }

    d_inner.swap(declarator2.type());
    name.swap(declarator2.name());
  }
  else if(kind!=kCastDeclarator &&
          (kind==kDeclarator || t==TOK_IDENTIFIER || t==TOK_SCOPE))
  {
    #ifdef DEBUG
    std::cout << "Parser::rDeclarator2 4\n";
    #endif
    
    // if this is an argument declarator, "int (*)()" is valid.
    if(!rName(name))
      return false;
  }

  #ifdef DEBUG
  std::cout << "Parser::rDeclarator2 5\n";
  #endif

  exprt init_args(static_cast<const exprt &>(get_nil_irep()));
  typet method_qualifier(static_cast<const typet &>(get_nil_irep())); // const...

  for(;;)
  {
    t=lex->LookAhead(0);
    if(t=='(') // function
    {
      Token op, cp;
      exprt args;
      bool is_args=true;

      lex->GetToken(op);

      if(lex->LookAhead(0)==')')
        args.clear();
      else
        if(!rArgDeclListOrInit(args, is_args, is_statement))
          return false;

      if(lex->GetToken(cp)!=')')
        return false;

      if(is_args)
      {
        typet function_type("function_type");
        function_type.subtype().swap(d_outer);
        function_type.add(ID_arguments).swap(args);

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

      irept throw_decl;
      optThrowDecl(throw_decl); // ignore in this version

      if(lex->LookAhead(0)==':')
      {
        Ptree mi;
        if(rMemberInitializers(mi))
        {
          // TODO
        }
        else
          return false;
      }

      break;                // "T f(int)(char)" is invalid.
    }
    else if(t=='[')         // array
    {
      Token ob, cb;
      exprt expr;
      lex->GetToken(ob);
      if(lex->LookAhead(0)==']')
        expr.make_nil();
      else
        if(!rCommaExpression(expr))
          return false;

      if(lex->GetToken(cb)!=']')
        return false;

        std::list<typet> tl;
        tl.push_back(d_outer);
        while(tl.back().id() == ID_array)
        {
          tl.push_back(tl.back().subtype());
        }

        typet array_type(ID_array);
        array_type.add(ID_size).swap(expr);
        array_type.subtype().swap(tl.back());
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
  std::cout << "Parser::optPtrOperator 1\n";
  #endif // DEBUG

  std::list<typet> t_list;

  for(;;)
  {
    int t=lex->LookAhead(0);

    #ifdef DEBUG
    std::cout << "Parser::optPtrOperator 2 " << t << "\n";
    #endif
    
    if(t!='*' && !isPtrToMember(0))
      break;
    else
    {
      typet op;
      if(t=='*')
      {
        Token tk;
        lex->GetToken(tk);
        op.id(ID_pointer);
        set_location(op, tk);
      }
      else
        if(!rPtrToMember(op))
          return false;

      typet cv;
      cv.make_nil();
      optCvQualify(cv);
      op.add(ID_C_qualifier).swap(cv);

      t_list.push_back(typet());
      t_list.back().swap(op);
    }
  }

  {
    int t=lex->LookAhead(0);
    
    if(t=='&')
    {
      Token tk;
      lex->GetToken(tk);
      typet op(ID_pointer);
      op.set(ID_C_reference, true);
      set_location(op, tk);
      t_list.push_front(op);
    }
    else if(t==TOK_ANDAND) // &&, these are C++0x rvalue refs
    {
      Token tk;
      lex->GetToken(tk);
      typet op(ID_pointer);
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
    it->subtype().swap(ptrs);
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
  Token tk;

  if(lex->GetToken(tk)!=':')
    return false;

  init=irept(ID_member_initializers);
  set_location(init, tk);

  exprt m;
  if(!rMemberInit(m))
    return false;

  init.move_to_sub(m);

  while(lex->LookAhead(0)==',')
  {
    lex->GetToken(tk);
    if(!rMemberInit(m))
      return false;

    init.move_to_sub(m);
  }

  return true;
}

/*
  member.init
  : name '(' function.arguments ')'
*/
bool Parser::rMemberInit(exprt &init)
{
  irept name;

  if(!rName(name))
    return false;

  init=codet(ID_member_initializer);
  init.add(ID_member).swap(name);

  Token tk1, tk2;

  if(lex->GetToken(tk1)!='(')
    return false;

  set_location(init, tk1);

  exprt args;

  if(!rFunctionArguments(args))
    return false;

  if(lex->GetToken(tk2)!=')')
    return false;

  init.operands().swap(args.operands());

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
  std::cout << "Parser::rName 0\n";
  #endif

  name=irept(ID_cpp_name);
  irept::subt &components=name.get_sub();

  if(lex->LookAhead(0)==TOK_TYPENAME)
  {
    Token tk;
    lex->GetToken(tk);
    name.set(ID_typename, true);
  }

  {
    Token tk;
    lex->LookAhead(0, tk);
    set_location(name, tk);
  }

  #ifdef DEBUG
  std::cout << "Parser::rName 1\n";
  #endif

  for(;;)
  {
    Token tk;

    #ifdef DEBUG
    std::cout << "Parser::rName 1.1 " << "\n";
    #endif

    switch(lex->LookAhead(0))
    {
    case TOK_TEMPLATE:
      lex->GetToken(tk);
      // Skip template token, next will be identifier
      if(lex->LookAhead(0)!=TOK_IDENTIFIER) return false;
      break;

    case '<':
      {
        irept args;
        if(!rTemplateArgs(args))
          return false;

        components.push_back(irept(ID_template_args));
        components.back().add(ID_arguments).swap(args);

        // done unless scope is next
        if(lex->LookAhead(0)!=TOK_SCOPE) return true;
      }
      break;

    case TOK_IDENTIFIER:
      lex->GetToken(tk);
      components.push_back(irept(ID_name));
      components.back().set(ID_identifier, tk.text);
      set_location(components.back(), tk);

      {
        int t=lex->LookAhead(0);
        // done unless scope or template args is next
        if(t!=TOK_SCOPE && t!='<') return true;
      }
      break;

    case TOK_SCOPE:
      lex->GetToken(tk);
      components.push_back(irept("::"));
      set_location(components.back(), tk);
      break;

    case '~':
      lex->GetToken(tk);

      // identifier must be next
      if(lex->LookAhead(0)!=TOK_IDENTIFIER)
        return false;

      components.push_back(irept("~"));
      set_location(components.back(), tk);
      break;

    case TOK_OPERATOR:
      lex->GetToken(tk);
      {
        components.push_back(irept(ID_operator));
        set_location(components.back(), tk);

        components.push_back(irept());

        if(!rOperatorName(components.back()))
          return false;
      }

      // done unless template args are next
      if(lex->LookAhead(0)!='<') return true;
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
  Token tk;

  int t=lex->LookAhead(0);
  if(t=='+' || t=='-' || t=='*' || t=='/' || t=='%' || t=='^' ||
     t=='&' || t=='|' || t=='~' || t=='!' || t=='=' || t=='<' ||
     t=='>' || 
     t==TOK_MULTASSIGN || t==TOK_DIVASSIGN || t==TOK_MODASSIGN ||
     t==TOK_PLUSASSIGN || t==TOK_MINUSASSIGN || t==TOK_SHLASSIGN ||
     t==TOK_SHRASSIGN  || t==TOK_ANDASSIGN ||
     t==TOK_XORASSIGN  || t==TOK_ORASSIGN ||     
     t==TOK_SHIFTLEFT  || t==TOK_SHIFTRIGHT ||
     t==TOK_EQ || t==TOK_NE ||
     t==TOK_LE || t==TOK_GE || 
     t==TOK_ANDAND || t==TOK_OROR || 
     t==TOK_INCR || t==TOK_DECR ||
     t==',' || t==TOK_DOTPM || t==TOK_ARROWPM || t==TOK_ARROW)
  {
    lex->GetToken(tk);
    name=irept(tk.text);
    set_location(name, tk);
  }
  else if(t==TOK_NEW || t==TOK_DELETE)
  {
    lex->GetToken(tk);

    if(lex->LookAhead(0)!='[')
    {
      name=irept(t==TOK_NEW?ID_cpp_new:ID_cpp_delete);
      set_location(name, tk);
    }
    else
    {
      name=irept(t==TOK_NEW?ID_cpp_new_array:ID_cpp_delete_array);
      set_location(name, tk);

      lex->GetToken(tk);

      if(lex->GetToken(tk)!=']')
        return false;
    }
  }
  else if(t=='(')
  {
    lex->GetToken(tk);
    name=irept("()");
    set_location(name, tk);

    if(lex->GetToken(tk)!=')')
      return false;
  }
  else if(t=='[')
  {
    lex->GetToken(tk);
    name=irept("[]");
    set_location(name, tk);

    if(lex->GetToken(tk)!=']')
      return false;
  }
  else
    return rCastOperatorName(name);

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

  merge_types(cv1,type_name);

  if(!optCvQualify(cv2))
    return false;

  if(!optPtrOperator(ptr))
    return false;

  if(ptr.is_nil())
  {
    name=type_name;
    return true;
  }
  else
  {
    std::list<typet> t_list;
    do
    {
      t_list.push_back(ptr);
      typet tmp = ptr.subtype();
      ptr = tmp;
    }while(ptr.is_not_nil());

    ptr = type_name;
    while(!t_list.empty())
    {
      t_list.back().subtype() = ptr;
      ptr = t_list.back();
      t_list.pop_back();
    }
    merge_types(cv2,ptr);
    name = ptr;
    return true;
  }
}

/*
  ptr.to.member
  : {'::'} (identifier {template.args} '::')+ '*'
*/
bool Parser::rPtrToMember(irept &ptr_to_mem)
{
  #ifdef DEBUG
  std::cout << "Parser::rPtrToMember 0\n";
  #endif

  irept ptm(ID_pointer);
  irept& name = ptm.add("to-member");
  name.id(ID_cpp_name);

  irept::subt &components=name.get_sub();

  {
    Token tk;
    lex->LookAhead(0, tk);
    set_location(name, tk);
  }

  bool loop_cond = true;
  while(loop_cond)
  {
    Token tk;

    switch(lex->LookAhead(0))
    {
    case TOK_TEMPLATE:
      lex->GetToken(tk);
      // Skip template token, next will be identifier
      if(lex->LookAhead(0)!=TOK_IDENTIFIER) return false;
      break;

    case '<':
      {
        irept args;
        if(!rTemplateArgs(args))
          return false;

        components.push_back(irept(ID_template_args));
        components.back().add(ID_arguments).swap(args);

        if(lex->LookAhead(0)!=TOK_SCOPE) return false;
      }
      break;

    case TOK_IDENTIFIER:
      lex->GetToken(tk);
      components.push_back(irept(ID_name));
      components.back().set(ID_identifier, tk.text);
      set_location(components.back(), tk);

      {
        int t=lex->LookAhead(0);
        if(t!=TOK_SCOPE && t!='<') return false;
      }
      break;

    case TOK_SCOPE:
      lex->GetToken(tk);
      components.push_back(irept("::"));
      set_location(components.back(), tk);

      // done if next token is '*'
      if(lex->LookAhead(0) == '*')
      {
        lex->GetToken(tk);
        ptr_to_mem.swap(ptm);


        #ifdef DEBUG
        std::cout << "Parser::rPtrToMember 1\n";
        #endif

        return true;
      }

      if(lex->LookAhead(0) != TOK_IDENTIFIER)
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
  std::cout << "Parser::rTemplateArgs 0\n";
  #endif

  Token tk1;

  if(lex->GetToken(tk1)!='<')
    return false;

  set_location(template_args, tk1);

  #ifdef DEBUG
  std::cout << "Parser::rTemplateArgs 1\n";
  #endif

  // in case of Foo<>
  if(lex->LookAhead(0)=='>')
  {
    Token tk2;
    lex->GetToken(tk2);
    return true;
  }

  #ifdef DEBUG
  std::cout << "Parser::rTemplateArgs 2\n";
  #endif

  for(;;)
  {
    exprt exp;
    cpp_token_buffert::post pos=lex->Save();

    #ifdef DEBUG
    std::cout << "Parser::rTemplateArgs 3\n";
    #endif

    typet a;

    // try type name first
    if(rTypeName(a) &&
        (lex->LookAhead(0) == '>' || lex->LookAhead(0) == ','))
    {
      #ifdef DEBUG
      std::cout << "Parser::rTemplateArgs 4\n";
      #endif

      // ok
      exp=exprt(ID_type);
      exp.location()=a.location();
      exp.type().swap(a);

      // but could also be an expr
      lex->Restore(pos);
      exprt tmp;
      if(rLogicalOrExpr(tmp, true))
        exp.id("ambiguous");
      lex->Restore(pos);
      rTypeName(a);
    }
    else
    {
      // parsing failed, try expression
      #ifdef DEBUG
      std::cout << "Parser::rTemplateArgs 5\n";
      #endif

      lex->Restore(pos);

      if(!rLogicalOrExpr(exp, true))
        return false;
    }

    #ifdef DEBUG
    std::cout << "Parser::rTemplateArgs 6\n";
    #endif

    template_args.get_sub().push_back(irept(irep_idt()));
    template_args.get_sub().back().swap(exp);

    Token tk2;
    switch(lex->GetToken(tk2))
    {
    case '>':
      return true;

    case ',':
      break;

    case TOK_SHIFTRIGHT: // turn >> into > >
      // the newer C++ standards frown on this!

      // turn >> into > > // TODO
      //lex->GetOnlyClosingBracket(tk2);
      //temp_args=Ptree::List(new Leaf(tk1), args,
      //                      new Leaf(tk2.ptr, 1));
      return false;

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
  cpp_token_buffert::post pos=lex->Save();
  if(maybe_init)
  {
    if(rFunctionArguments(arglist))
      if(lex->LookAhead(0)==')')
      {
        is_args=false;
        //encode.Clear();
        return true;
      }

    lex->Restore(pos);
    return(is_args=rArgDeclList(arglist));
  }
  else
  {
    if((is_args=rArgDeclList(arglist)))
      return true;
    else
    {
      lex->Restore(pos);
      //encode.Clear();
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

    int t=lex->LookAhead(0);
    if(t==')')
    {
      arglist.swap(list);
      break;
    }
    else if(t==TOK_ELLIPSIS)
    {
      Token tk;
      lex->GetToken(tk);
      arglist.swap(list);
      arglist.get_sub().push_back(irept(ID_ellipsis));
      break;
    }
    else if(rArgDeclaration(declaration))
    {
      Token tk;

      list.get_sub().push_back(irept(irep_idt()));
      list.get_sub().back().swap(declaration);
      t=lex->LookAhead(0);
      if(t==',')
        lex->GetToken(tk);
      else if(t!=')' && t!=TOK_ELLIPSIS)
        return false;
    }
    else
    {
      arglist.clear();
      return false;
    }
  }

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
  Token tk;

  switch(lex->LookAhead(0))
  {
  case TOK_REGISTER:
    lex->GetToken(tk);
    header=typet(ID_register);
    break;

  default:
    header.make_nil();
    break;
  }

  if(!rTypeSpecifier(declaration.type(), true))
    return false;

  cpp_declaratort arg_declarator;

  if(!rDeclarator(arg_declarator, kArgDeclarator, false, true))
    return false;

  declaration.declarators().push_back(arg_declarator);

  int t=lex->LookAhead(0);
  if(t=='=')
  {
    lex->GetToken(tk);
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
  if(lex->LookAhead(0)!='{')
    return rExpression(expr);

  // we want { initialize_expr, ... }

  Token tk;
  lex->GetToken(tk);

  exprt e;

  expr.id(ID_initializer_list);
  expr.type().id(ID_incomplete_array);
  set_location(expr, tk);

  int t=lex->LookAhead(0);

  while(t!='}')
  {
    exprt tmp;

    if(t==TOK_MSC_IF_EXISTS ||
       t==TOK_MSC_IF_NOT_EXISTS)
    {
      // TODO
      Token tk;
      exprt name;
      lex->GetToken(tk);
      if(lex->GetToken(tk)!='(') return false;
      if(!rVarName(name)) return false;
      if(lex->GetToken(tk)!=')') return false;
      if(lex->GetToken(tk)!='{') return false;
      if(!rInitializeExpr(name)) return false;
      if(lex->LookAhead(0)==',') lex->GetToken(tk);
      if(lex->GetToken(tk)!='}') return false;
    }
    
    if(!rInitializeExpr(tmp))
    {
      if(!SyntaxError())
        return false;        // too many errors

      SkipTo('}');
      lex->GetToken(tk);
      return true;           // error recovery
    }

    expr.move_to_operands(tmp);

    t=lex->LookAhead(0);
    if(t=='}')
    {
      // done!
    }
    else if(t==',')
    {
      lex->GetToken(tk);
      t=lex->LookAhead(0);
    }
    else
    {
      if(!SyntaxError())
        return false;        // too many errors

      SkipTo('}');
      lex->GetToken(tk);
      return true;           // error recovery
    }
  }

  lex->GetToken(tk);

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
  Token tk;

  args=exprt(irep_idt());
  if(lex->LookAhead(0)==')')
    return true;

  for(;;)
  {
    if(!rExpression(exp))
      return false;

    args.move_to_operands(exp);

    if(lex->LookAhead(0)!=',')
      return true;
    else
      lex->GetToken(tk);
  }
}

/*
  enum.spec
  : ENUM Identifier
  | ENUM {Identifier} '{' {enum.body} '}'
*/
bool Parser::rEnumSpec(typet &spec)
{
  Token tk;

  if(lex->GetToken(tk)!=TOK_ENUM)
    return false;

  spec=cpp_enum_typet();
  set_location(spec, tk);

  int t=lex->GetToken(tk);

  if(t==TOK_IDENTIFIER)
  {
    spec.set(ID_name, tk.text);

    if(lex->LookAhead(0)=='{')
      t=lex->GetToken(tk);
    else
      return true;
  }
  else
    spec.set(ID_name, irep_idt());

  if(t!='{')
    return false;

  if(lex->LookAhead(0)=='}')
  {
    // there is still a body, just an empty one!
    spec.add(ID_body);
  }
  else
    if(!rEnumBody(spec.add(ID_body)))
      return false;

  if(lex->GetToken(tk)!='}')
    return false;

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
    Token tk, tk2;

    if(lex->LookAhead(0)=='}')
      return true;

    if(lex->GetToken(tk)!=TOK_IDENTIFIER)
      return false;

    body.get_sub().push_back(irept());
    irept &n=body.get_sub().back();
    set_location(n, tk);
    n.set(ID_name, tk.text);

    if(lex->LookAhead(0, tk2)=='=') // set the constant
    {
      lex->GetToken(tk2); // read the '='

      exprt exp;

      if(!rExpression(exp))
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

    if(lex->LookAhead(0)!=',')
      return true;

    lex->GetToken(tk);
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
  Token tk;

  #ifdef DEBUG
  std::cout << "Parser::rClassSpec 1\n";
  #endif

  int t=lex->GetToken(tk);
  if(t!=TOK_CLASS && t!=TOK_STRUCT && 
     t!=TOK_UNION && t!=TOK_INTERFACE)
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rClassSpec 2\n";
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
    assert(false);

  set_location(spec, tk);

  #ifdef DEBUG
  std::cout << "Parser::rClassSpec 3\n";
  #endif

  if(lex->LookAhead(0)=='{')
  {
    // no tag
    #ifdef DEBUG
    std::cout << "Parser::rClassSpec 4\n";
    #endif
  }
  else
  {
    irept name;

    if(!rName(name))
      return false;

    spec.add(ID_tag).swap(name);

    #ifdef DEBUG
    std::cout << "Parser::rClassSpec 5\n";
    #endif

    t=lex->LookAhead(0);

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
  std::cout << "Parser::rClassSpec 6\n";
  #endif

  exprt body;

  if(!rClassBody(body))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rClassSpec 7\n";
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
  Token tk;

  if(lex->GetToken(tk)!=':')
    return false;

  for(;;)
  {
    int t=lex->LookAhead(0);
    irept base(ID_base);

    if(t==TOK_VIRTUAL)
    {
      lex->GetToken(tk);
      base.set(ID_virtual, true);
      t=lex->LookAhead(0);
    }

    if(t==TOK_PUBLIC || t==TOK_PROTECTED || t==TOK_PRIVATE)
    {
      switch(lex->GetToken(tk))
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
        assert(0);
      }

      t=lex->LookAhead(0);
    }

    if(t==TOK_VIRTUAL)
    {
      lex->GetToken(tk);
      base.set(ID_virtual, true);
    }

    if(!rName(base.add(ID_name)))
      return false;

    bases.get_sub().push_back(irept());
    bases.get_sub().back().swap(base);

    if(lex->LookAhead(0)!=',')
      return true;
    else
      lex->GetToken(tk);
  }
}

/*
  class.body : '{' (class.members)* '}'
*/
bool Parser::rClassBody(exprt &body)
{
  Token tk;

  #ifdef DEBUG
  std::cout << "Parser::rClassBody 0\n";
  #endif

  if(lex->GetToken(tk)!='{')
    return false;

  //Ptree ob=new Leaf(tk);

  exprt members=exprt("cpp-class-body");

  set_location(members, tk);

  while(lex->LookAhead(0)!='}')
  {
    cpp_itemt member;

    if(!rClassMember(member))
    {
      if(!SyntaxError())
        return false;        // too many errors

      SkipTo('}');
      lex->GetToken(tk);
      //body=Ptree::List(ob, nil, new Leaf(tk));
      return true;        // error recovery
    }

    //lex->GetComments();
    //mems=Ptree::Snoc(mems, m);

    #ifdef DEBUG
    std::cout << "Parser::rClassBody " << member << std::endl;
    #endif

    members.move_to_operands(static_cast<exprt &>(static_cast<irept &>(member)));
  }

  lex->GetToken(tk);
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

  Note: if you modify this function, see ClassWalker::TranslateClassSpec()
  as well.
*/
bool Parser::rClassMember(cpp_itemt &member)
{
  Token tk1, tk2;

  int t=lex->LookAhead(0);

  #ifdef DEBUG
  std::cout << "Parser::rClassMember 0 " << t << std::endl;
  #endif // DEBUG

  if(t==TOK_PUBLIC || t==TOK_PROTECTED || t==TOK_PRIVATE)
  {
    switch(lex->GetToken(tk1))
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
      assert(0);
    }

    set_location(member, tk1);

    if(lex->GetToken(tk2)!=':')
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
    return rUsing(member.make_using());
  else
  {
    cpp_token_buffert::post pos=lex->Save();
    if(rDeclaration(member.make_declaration()))
      return true;

    lex->Restore(pos);
    return rAccessDecl(member);
  }
}

/*
  access.decl
  : name ';'                e.g. <qualified class>::<member name>;
*/
bool Parser::rAccessDecl(irept &mem)
{
  irept name;
  Token tk;

  if(!rName(name))
    return false;

  if(lex->GetToken(tk)!=';')
    return false;

  //mem=new PtreeAccessDecl(new PtreeName(name, encode),
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
  std::cout << "Parser::rCommaExpression 0\n";
  #endif

  if(!rExpression(exp))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rCommaExpression 1\n";
  #endif

  while(lex->LookAhead(0)==',')
  {
    Token tk;

    lex->GetToken(tk);

    exprt right;
    if(!rExpression(right))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt(ID_comma);
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  #ifdef DEBUG
  std::cout << "Parser::rCommaExpression 2\n";
  #endif

  return true;
}

/*
  expression
  : conditional.expr {(AssignOp | '=') expression}        right-to-left
*/
bool Parser::rExpression(exprt &exp)
{
  Token tk;

  #ifdef DEBUG
  std::cout << "Parser::rExpression 0\n";
  #endif

  if(!rConditionalExpr(exp))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rExpression 1\n";
  #endif

  int t=lex->LookAhead(0);

  if(t=='=' || 
     t==TOK_MULTASSIGN || t==TOK_DIVASSIGN || t==TOK_MODASSIGN ||
     t==TOK_PLUSASSIGN || t==TOK_MINUSASSIGN || t==TOK_SHLASSIGN ||
     t==TOK_SHRASSIGN  || t==TOK_ANDASSIGN ||
     t==TOK_XORASSIGN  || t==TOK_ORASSIGN)
  {
    lex->GetToken(tk);

    #ifdef DEBUG
    std::cout << "Parser::rExpression 2\n";
    #endif

    exprt right;
    if(!rExpression(right))
      return false;

    #ifdef DEBUG
    std::cout << "Parser::rExpression 3\n";
    #endif

    exprt left;
    left.swap(exp);

    exp=exprt(ID_sideeffect);

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
  std::cout << "Parser::rExpression 4\n";
  #endif

  return true;
}

/*
  conditional.expr
  : logical.or.expr {'?' comma.expression ':' conditional.expr}  right-to-left
*/
bool Parser::rConditionalExpr(exprt &exp)
{
  #ifdef DEBUG
  std::cout << "Parser::rConditionalExpr 0\n";
  #endif

  if(!rLogicalOrExpr(exp, false))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rConditionalExpr 1\n";
  #endif

  if(lex->LookAhead(0)=='?')
  {
    Token tk1, tk2;
    exprt then, otherwise;

    lex->GetToken(tk1);
    if(!rCommaExpression(then))
      return false;

    #ifdef DEBUG
    std::cout << "Parser::rConditionalExpr 2\n";
    #endif

    if(lex->GetToken(tk2)!=':')
      return false;

    if(!rExpression(otherwise))
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
bool Parser::rLogicalOrExpr(exprt &exp, bool temp_args)
{
  #ifdef DEBUG
  std::cout << "Parser::rLogicalOrExpr 0\n";
  #endif

  if(!rLogicalAndExpr(exp, temp_args))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rLogicalOrExpr 1\n";
  #endif

  while(lex->LookAhead(0)==TOK_OROR)
  {
    Token tk;
    lex->GetToken(tk);

    exprt right;
    if(!rLogicalAndExpr(right, temp_args))
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
bool Parser::rLogicalAndExpr(exprt &exp, bool temp_args)
{
  #ifdef DEBUG
  std::cout << "Parser::rLogicalAndExpr 1\n";
  #endif

  if(!rInclusiveOrExpr(exp, temp_args))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rLogicalAndExpr 1\n";
  #endif

  while(lex->LookAhead(0)==TOK_ANDAND)
  {
    Token tk;
    lex->GetToken(tk);

    exprt right;
    if(!rInclusiveOrExpr(right, temp_args))
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
bool Parser::rInclusiveOrExpr(exprt &exp, bool temp_args)
{
  #ifdef DEBUG
  std::cout << "Parser::rInclusiveOrExpr 0\n";
  #endif

  if(!rExclusiveOrExpr(exp, temp_args))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rInclusiveOrExpr 1\n";
  #endif

  while(lex->LookAhead(0)=='|')
  {
    Token tk;
    lex->GetToken(tk);

    exprt right;
    if(!rExclusiveOrExpr(right, temp_args))
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
bool Parser::rExclusiveOrExpr(exprt &exp, bool temp_args)
{
  #ifdef DEBUG
  std::cout << "Parser::rExclusiveOrExpr 0\n";
  #endif

  if(!rAndExpr(exp, temp_args))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rExclusiveOrExpr 1\n";
  #endif

  while(lex->LookAhead(0)=='^')
  {
    Token tk;
    lex->GetToken(tk);

    exprt right;
    if(!rAndExpr(right, temp_args))
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
bool Parser::rAndExpr(exprt &exp, bool temp_args)
{
  #ifdef DEBUG
  std::cout << "Parser::rAndExpr 0\n";
  #endif

  if(!rEqualityExpr(exp, temp_args))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rAndExpr 1\n";
  #endif

  while(lex->LookAhead(0)=='&')
  {
    Token tk;
    lex->GetToken(tk);

    exprt right;
    if(!rEqualityExpr(right, temp_args))
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
bool Parser::rEqualityExpr(exprt &exp, bool temp_args)
{
  #ifdef DEBUG
  std::cout << "Parser::rEqualityExpr 0\n";
  #endif

  if(!rRelationalExpr(exp, temp_args))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rEqualityExpr 1\n";
  #endif

  while(lex->LookAhead(0)==TOK_EQ ||
        lex->LookAhead(0)==TOK_NE)
  {
    Token tk;
    lex->GetToken(tk);

    exprt right;
    if(!rRelationalExpr(right, temp_args))
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
bool Parser::rRelationalExpr(exprt &exp, bool temp_args)
{
  #ifdef DEBUG
  std::cout << "Parser::rRelationalExpr 0\n";
  #endif

  if(!rShiftExpr(exp))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rRelationalExpr 1\n";
  #endif

  int t;

  while(t=lex->LookAhead(0),
        (t==TOK_LE || t==TOK_GE || t=='<' || (t=='>' && !temp_args)))
  {
    Token tk;
    lex->GetToken(tk);

    exprt right;
    if(!rShiftExpr(right))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt(tk.text);
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
bool Parser::rShiftExpr(exprt &exp)
{
  #ifdef DEBUG
  std::cout << "Parser::rShiftExpr 0\n";
  #endif

  if(!rAdditiveExpr(exp))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rShiftExpr 1\n";
  #endif

  while(lex->LookAhead(0)==TOK_SHIFTLEFT ||
        lex->LookAhead(0)==TOK_SHIFTRIGHT)
  {
    Token tk;
    lex->GetToken(tk);

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
  std::cout << "Parser::rAdditiveExpr 0\n";
  #endif

  if(!rMultiplyExpr(exp))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rAdditiveExpr 1\n";
  #endif

  int t;
  while(t=lex->LookAhead(0), (t=='+' || t=='-'))
  {
    Token tk;
    lex->GetToken(tk);

    exprt right;
    if(!rMultiplyExpr(right))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt(tk.text);
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
  std::cout << "Parser::rMultiplyExpr 0\n";
  #endif

  if(!rPmExpr(exp))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rMultiplyExpr 1\n";
  #endif

  int t;
  while(t=lex->LookAhead(0), (t=='*' || t=='/' || t=='%'))
  {
    Token tk;
    lex->GetToken(tk);

    exprt right;
    if(!rPmExpr(right))
      return false;

    exprt left;
    left.swap(exp);

    exp=exprt((tk.text=="%")?ID_mod:tk.text);
    exp.move_to_operands(left, right);
    set_location(exp, tk);
  }

  #ifdef DEBUG
  std::cout << "Parser::rMultiplyExpr 2\n";
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
  std::cout << "Parser::rPmExpr 0\n";
  #endif

  if(!rCastExpr(exp))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rPmExpr 1\n";
  #endif

  while(lex->LookAhead(0)==TOK_DOTPM ||
        lex->LookAhead(0)==TOK_ARROWPM)
  {
    Token tk;
    lex->GetToken(tk);

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
  std::cout << "Parser::rPmExpr 2\n";
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
  std::cout << "Parser::rCastExpr 0\n";
  #endif

  if(lex->LookAhead(0)!='(')
    return rUnaryExpr(exp);
  else
  {
    Token tk1, tk2;

    #ifdef DEBUG
    std::cout << "Parser::rCastExpr 1\n";
    #endif

    cpp_token_buffert::post pos=lex->Save();
    lex->GetToken(tk1);

    typet tname;

    if(rTypeName(tname))
      if(lex->GetToken(tk2)==')')
        if(rCastExpr(exp))
        {
          exprt op;
          op.swap(exp);

          exp=exprt("explicit-typecast");
          exp.type().swap(tname);
          exp.move_to_operands(op);
          set_location(exp, tk1);
          return true;
        }

    lex->Restore(pos);
    return rUnaryExpr(exp);
  }
}

/*
  type.name
  : type.specifier cast.declarator
*/
bool Parser::rTypeName(typet &tname)
{
  typet type_name;

  if(!rTypeSpecifier(type_name, true))
    return false;

  cpp_declaratort declarator;

  if(!rDeclarator(declarator, kCastDeclarator, false, false))
    return false;

  tname.swap(declarator.type());

  // make type_name subtype of arg
  make_subtype(type_name, tname);

  return true;
}

/*
  unary.expr
  : postfix.expr
  | ('*' | '&' | '+' | '-' | '!' | '~' | IncOp) cast.expr
  | sizeof.expr
  | allocate.expr
  | throw.expression
*/

bool Parser::rUnaryExpr(exprt &exp)
{
  int t=lex->LookAhead(0);

  #ifdef DEBUG
  std::cout << "Parser::rUnaryExpr 0\n";
  #endif

  if(t=='*' || t=='&' || t=='+' ||
     t=='-' || t=='!' || t=='~' ||
     t==TOK_INCR || t==TOK_DECR)
  {
    Token tk;
    lex->GetToken(tk);

    #ifdef DEBUG
    std::cout << "Parser::rUnaryExpr 1\n";
    #endif

    exprt right;
    if(!rCastExpr(right))
      return false;

    #ifdef DEBUG
    std::cout << "Parser::rUnaryExpr 2\n";
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
    case TOK_DECR:
      exp=exprt(ID_sideeffect);
      exp.set(ID_statement,
        tk.text=="++"?ID_preincrement:ID_predecrement);
      break;

    default:
      assert(0);
    }

    exp.move_to_operands(right);
    set_location(exp, tk);

    return true;
  }
  else if(t==TOK_SIZEOF)
    return rSizeofExpr(exp);
  else if(t==TOK_THROW)
    return rThrowExpr(exp);
  else if(t==TOK_REAL || t==TOK_IMAG)
  {
    // a GCC extension for complex floating-point arithmetic
    Token tk;
    lex->GetToken(tk);

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
  Token tk;

  #ifdef DEBUG
  std::cout << "Parser::rThrowExpr 0\n";
  #endif

  if(lex->GetToken(tk)!=TOK_THROW)
    return false;

  int t=lex->LookAhead(0);

  exp=exprt(ID_sideeffect);
  exp.set(ID_statement, ID_throw);
  set_location(exp, tk);

  if(t==':' || t==';')
  {
    // done
  }
  else
  {
    exprt e;
  
    if(!rExpression(e))
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
  Token tk;

  #ifdef DEBUG
  std::cout << "Parser::rTypeidExpr 0\n";
  #endif

  if(lex->GetToken(tk)!=TOK_TYPEID)
    return false;

  if(lex->LookAhead(0)=='(')
  {
    typet tname;
    exprt subexp;
    Token op, cp;

    cpp_token_buffert::post pos=lex->Save();
    lex->GetToken(op);
    if(rTypeName(tname))
      if(lex->GetToken(cp)==')')
      {
        //exp=new PtreeTypeidExpr(new Leaf(tk),
        //                        Ptree::List(new Leaf(op), tname,
        //                        new Leaf(cp)));

        exp=exprt("typeid");
        set_location(exp, tk);
        return true;
      }

    lex->Restore(pos);
    lex->GetToken(op);

    if(rExpression(subexp))
      if(lex->GetToken(cp)==')')
      {
        // exp=new PtreeTypeidExpr(new Leaf(tk),
        //                              Ptree::List(
        //                                  Ptree::List(new Leaf(op), subexp, new Leaf(cp))
        //                              ));

        exp=exprt("typeid");
        set_location(exp, tk);
        return true;
      }

    lex->Restore(pos);
  }

  return false;
}

/*
  sizeof.expr
  : SIZEOF unary.expr
  | SIZEOF '(' type.name ')'
*/

bool Parser::rSizeofExpr(exprt &exp)
{
  Token tk;

  #ifdef DEBUG
  std::cout << "Parser::rSizeofExpr 0\n";
  #endif

  if(lex->GetToken(tk)!=TOK_SIZEOF)
    return false;

  if(lex->LookAhead(0)=='(')
  {
    typet tname;
    Token op, cp;

    cpp_token_buffert::post pos=lex->Save();
    lex->GetToken(op);

    if(rTypeName(tname))
      if(lex->GetToken(cp)==')')
      {
        exp=exprt(ID_sizeof);
        exp.add(ID_type_arg).swap(tname);
        set_location(exp, tk);
        return true;
      }

    lex->Restore(pos);
  }

  exprt unary;

  if(!rUnaryExpr(unary))
    return false;

  exp=exprt(ID_sizeof);
  exp.move_to_operands(unary);
  set_location(exp, tk);
  return true;
}

bool Parser::isAllocateExpr(int t)
{
  if(t==TOK_SCOPE)
    t=lex->LookAhead(1);

  return t==TOK_NEW || t==TOK_DELETE;
}

/*
  allocate.expr
  : {Scope | userdef.keyword} NEW allocate.type
  | {Scope} DELETE {'[' ']'} cast.expr
*/
bool Parser::rAllocateExpr(exprt &exp)
{
  Token tk;
  irept head=get_nil_irep();

  #ifdef DEBUG
  std::cout << "Parser::rAllocateExpr 0\n";
  #endif

  int t=lex->LookAhead(0);
  if(t==TOK_SCOPE)
  {
    lex->GetToken(tk);
    // TODO, one can put 'new'/'delete' into a namespace!
  }

  #ifdef DEBUG
  std::cout << "Parser::rAllocateExpr 1\n";
  #endif

  t=lex->GetToken(tk);

  #ifdef DEBUG
  std::cout << "Parser::rAllocateExpr 2\n";
  #endif

  if(t==TOK_DELETE)
  {
    exprt obj;

    if(lex->LookAhead(0)=='[')
    {
      lex->GetToken(tk);

      if(lex->GetToken(tk)!=']')
        return false;

      exp=exprt(ID_sideeffect);
      exp.set(ID_statement, ID_cpp_delete_array);
    }
    else
    {
      exp=exprt(ID_sideeffect);
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
    std::cout << "Parser::rAllocateExpr 3\n";
    #endif

    exp=exprt(ID_sideeffect);
    exp.set(ID_statement, ID_cpp_new);
    set_location(exp, tk);

    exprt arguments, initializer;

    if(!rAllocateType(arguments, exp.type(), initializer))
      return false;

    #ifdef DEBUG
    std::cout << "Parser::rAllocateExpr 4\n";
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
  if(lex->LookAhead(0)!='(')
  {
    atype.make_nil();
  }
  else
  {
    // reads the '('
    lex->GetToken();

    // we may need to backtrack
    cpp_token_buffert::post pos=lex->Save();

    if(rTypeName(atype))
    {
      if(lex->GetToken()==')')
      {
        // we have "( type.name )"
        
        if(lex->LookAhead(0)!='(')
        {
          if(!isTypeSpecifier())
            return true;
        }
        else if(rAllocateInitializer(initializer))
        {
          // the next token cannot be '('
          if(lex->LookAhead(0)!='(')
            return true;
        }
      }
    }

    // if we reach here, it's not '(' type.name ')',
    // and we have to process '(' function.arguments ')'.

    lex->Restore(pos);
    if(!rFunctionArguments(arguments))
      return false;

    if(lex->GetToken()!=')')
      return false;
  }

  if(lex->LookAhead(0)=='(')
  {
    lex->GetToken();

    typet tname;

    if(!rTypeName(tname))
      return false;

    if(lex->GetToken()!=')')
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

  if(lex->LookAhead(0)=='(')
  {
    if(!rAllocateInitializer(initializer))
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
  if(lex->LookAhead(0)!='[')
    if(!optPtrOperator(decl))
      return false;

  while(lex->LookAhead(0)=='[')
  {
    Token ob, cb;
    exprt expr;

    lex->GetToken(ob);
    if(!rCommaExpression(expr))
      return false;

    if(lex->GetToken(cb)!=']')
      return false;

    array_typet array_type;
    array_type.size().swap(expr);
    array_type.subtype().swap(decl);
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
  {
    if(lex->GetToken()!='(')
      return false;
  }

  init.clear();

  if(lex->LookAhead(0)==')')
  {
    lex->GetToken();
    return true;
  }

  for(;;)
  {
    exprt exp;
    if(!rInitializeExpr(exp))
      return false;

    init.move_to_operands(exp);

    if(lex->LookAhead(0)==',')
      lex->GetToken();
    else if(lex->LookAhead(0)==')')
    {
      lex->GetToken();
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
  std::cout << "Parser::rPostfixExpr 0\n";
  #endif

  if(!rPrimaryExpr(exp))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rPostfixExpr 1\n";
  #endif

  exprt e;
  Token cp, op;
  int t2;

  for(;;)
  {
    switch(lex->LookAhead(0))
    {
    case '[':
      lex->GetToken(op);
      if(!rCommaExpression(e))
        return false;

      #ifdef DEBUG
      std::cout << "Parser::rPostfixExpr 2\n";
      #endif

      if(lex->GetToken(cp)!=']')
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
      std::cout << "Parser::rPostfixExpr 3\n";
      #endif

      lex->GetToken(op);
      if(!rFunctionArguments(e))
        return false;

      if(lex->GetToken(cp)!=')')
        return false;

      #ifdef DEBUG
      std::cout << "Parser::rPostfixExpr 4\n";
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
    case TOK_DECR:
      lex->GetToken(op);

      {
        exprt tmp(ID_sideeffect);
        tmp.move_to_operands(exp);
        tmp.set(ID_statement,
          op.text=="++"?ID_postincrement:ID_postdecrement);
        set_location(tmp, op);

        exp.swap(tmp);
      }
      break;

    case '.':
    case TOK_ARROW:
      t2=lex->GetToken(op);

      #ifdef DEBUG
      std::cout << "Parser::rPostfixExpr 5\n";
      #endif

      if(!rVarName(e))
        return false;

      #ifdef DEBUG
      std::cout << "Parser::rPostfixExpr 6\n";
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

      exp.add("component_cpp_name").swap(e);

      break;

    default:
      return true;
    }
  }
}

/*
  __uuidof( expression )
  __uuidof( type )
*/  

bool Parser::rMSCuuidof(exprt &expr)
{
  Token tk;

  if(lex->GetToken(tk)!=TOK_MSC_UUIDOF)
    return false;

  if(lex->GetToken(tk)!='(')
    return false;

  {
    typet tname;
    Token cp;

    cpp_token_buffert::post pos=lex->Save();

    if(rTypeName(tname))
    {
      if(lex->GetToken(cp)==')')
      {
        expr=exprt(ID_msc_uuidof);
        expr.add(ID_type_arg).swap(tname);
        set_location(expr, tk);
        return true;
      }
    }

    lex->Restore(pos);
  }

  exprt unary;

  if(!rUnaryExpr(unary))
    return false;

  if(lex->GetToken(tk)!=')')
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
  Token tk1;

  lex->GetToken(tk1);
  
  if(tk1.kind!=TOK_MSC_IF_EXISTS &&
     tk1.kind!=TOK_MSC_IF_NOT_EXISTS)
    return false;
    
  Token tk2;

  if(lex->GetToken(tk2)!='(')
    return false;

  exprt name;

  if(!rVarName(name))
    return false;

  if(lex->GetToken(tk2)!=')')
    return false;

  if(lex->GetToken(tk2)!='{')
    return false;

  exprt op;

  if(!rUnaryExpr(op))
    return false;

  if(lex->GetToken(tk2)!='}')
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
  Token tk1;

  lex->GetToken(tk1);
  
  if(tk1.kind!=TOK_MSC_IF_EXISTS &&
     tk1.kind!=TOK_MSC_IF_NOT_EXISTS)
    return false;
    
  Token tk2;

  if(lex->GetToken(tk2)!='(')
    return false;

  exprt name;

  if(!rVarName(name))
    return false;

  if(lex->GetToken(tk2)!=')')
    return false;

  if(lex->GetToken(tk2)!='{')
    return false;

  codet block;

  while(lex->LookAhead(0)!='}')
  {
    codet statement;

    if(!rStatement(statement))
      return false;

    block.move_to_operands(statement);
  }

  if(lex->GetToken(tk2)!='}')
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

bool Parser::rMSCTypePredicate(exprt &expr)
{
  Token tk;

  lex->GetToken(tk);

  expr.id(irep_idt(tk.text));
  set_location(expr, tk);  

  typet tname1, tname2;
  
  switch(tk.kind)
  {
  case TOK_MSC_UNARY_TYPE_PREDICATE:
    if(lex->GetToken(tk)!='(') return false;
    if(!rTypeName(tname1)) return false;
    if(lex->GetToken(tk)!=')') return false;
    expr.add(ID_type_arg).swap(tname1);
    break;
  
  case TOK_MSC_BINARY_TYPE_PREDICATE:
    if(lex->GetToken(tk)!='(') return false;
    if(!rTypeName(tname1)) return false;
    if(lex->GetToken(tk)!=',') return false;
    if(!rTypeName(tname2)) return false;
    if(lex->GetToken(tk)!=')') return false;
    expr.add("type_arg1").swap(tname1);
    expr.add("type_arg2").swap(tname2);
    break;
    
  default:
    assert(false);
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
  | typeid.expr
  | openc++.primary.exp

  openc++.primary.exp
  : var.name '::' userdef.statement
*/
bool Parser::rPrimaryExpr(exprt &exp)
{
  Token tk, tk2;

  #ifdef DEBUG
  std::cout << "Parser::rPrimaryExpr 0 " << lex->LookAhead(0) << " " << lex->current_token().text <<"\n";
  #endif

  switch(lex->LookAhead(0))
  {
  case TOK_INTEGER:
  case TOK_CHARACTER:
  case TOK_FLOATING:
  case TOK_WideCharConst:
    lex->GetToken(tk);
    exp.swap(tk.data);
    set_location(exp, tk);
    return true;

  case TOK_WideStringL:
  case TOK_STRING:
    rString(tk);
    exp.swap(tk.data);
    set_location(exp, tk);
    return true;

  case TOK_THIS:
    lex->GetToken(tk);
    exp=exprt("cpp-this");
    set_location(exp, tk);
    return true;

  case '(':
    lex->GetToken(tk);

    if(lex->LookAhead(0)=='{') // GCC extension
    {
      codet code;

      if(!rCompoundStatement(code))
        return false;

      exp=exprt(ID_sideeffect);
      exp.set(ID_statement, ID_statement_expression);
      set_location(exp, tk);
      exp.move_to_operands(code);

      if(lex->GetToken(tk2)!=')')
        return false;
    }
    else
    {
      exprt exp2;

      if(!rCommaExpression(exp2))
        return false;

      #ifdef DEBUG
      std::cout << "Parser::rPrimaryExpr 1\n";
      #endif

      if(lex->GetToken(tk2)!=')')
        return false;

      exp.swap(exp2);
    }

    return true;

  case TOK_TYPEID:
    return rTypeidExpr(exp);
    
  case TOK_MSC_UNARY_TYPE_PREDICATE:
  case TOK_MSC_BINARY_TYPE_PREDICATE:
    return rMSCTypePredicate(exp);

  case TOK_MSC_UUIDOF:
    return rMSCuuidof(exp);

  // not quite appropriate: these allow more general
  // token streams, not just expressions
  case TOK_MSC_IF_EXISTS:
  case TOK_MSC_IF_NOT_EXISTS:
    return rMSC_if_existsExpr(exp);

  default:
    {
      typet type;

      if(!optIntegralTypeOrClassSpec(type))
        return false;

      if(type.is_not_nil())
      {
        if(lex->GetToken(tk)!='(')
          return false;

        exprt exp2;
        if(!rFunctionArguments(exp2))
            return false;

        if(lex->GetToken(tk2)!=')')
            return false;

        exp=exprt("explicit-constructor-call");
        exp.type().swap(type);
        exp.operands().swap(exp2.operands());
        set_location(exp, tk);
      }
      else
      {
        if(!rVarName(exp))
          return false;

        if(lex->LookAhead(0)==TOK_SCOPE)
        {
          lex->GetToken(tk);

          //exp=new PtreeStaticUserStatementExpr(exp,
          //                        Ptree::Cons(new Leaf(tk), exp2));
          // TODO
        }
      }
    }

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
  std::cout << "Parser::rVarName 0\n";
  #endif

  if(rVarNameCore(name))
    return true;
  else
    return false;
}

bool Parser::rVarNameCore(exprt &name)
{
  #ifdef DEBUG
  std::cout << "Parser::rVarNameCore 0\n";
  #endif

  name=exprt(ID_cpp_name);
  irept::subt &components=name.get_sub();

  if(lex->LookAhead(0)==TOK_TYPENAME)
  {
    Token tk;
    lex->GetToken(tk);
    name.set("typename", true);
  }

  {
    Token tk;
    lex->LookAhead(0, tk);
    set_location(name, tk);
  }

  #ifdef DEBUG
  std::cout << "Parser::rVarNameCore 1\n";
  #endif

  for(;;)
  {
    Token tk;

    #ifdef DEBUG
    std::cout << "Parser::rVarNameCore 1.1 " << lex->LookAhead(0)
              << std::endl;
    #endif

    switch(lex->LookAhead(0))
    {
    case TOK_IDENTIFIER:
      #ifdef DEBUG
      std::cout << "Parser::rVarNameCore 2\n";
      #endif

      lex->GetToken(tk);
      components.push_back(irept(ID_name));
      components.back().set(ID_identifier, tk.text);
      set_location(components.back(), tk);

      // may be followed by template arguments
      if(isTemplateArgs())
      {
        #ifdef DEBUG
        std::cout << "Parser::rVarNameCore 3\n";
        #endif

        irept args;
        if(!rTemplateArgs(args))
          return false;

        components.push_back(irept(ID_template_args));
        components.back().add(ID_arguments).swap(args);
      }

      if(!moreVarName()) return true;
      break;

    case TOK_SCOPE:
      #ifdef DEBUG
      std::cout << "Parser::rVarNameCore 4\n";
      #endif

      lex->GetToken(tk);
      components.push_back(irept("::"));
      set_location(components.back(), tk);
      break;

    case '~':
      #ifdef DEBUG
      std::cout << "Parser::rVarNameCore 5\n";
      #endif

      lex->GetToken(tk);

      if(lex->LookAhead(0)!=TOK_IDENTIFIER)
        return false;

      components.push_back(irept("~"));
      set_location(components.back(), tk);
      break;

    case TOK_OPERATOR:
      #ifdef DEBUG
      std::cout << "Parser::rVarNameCore 6\n";
      #endif

      lex->GetToken(tk);

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
  if(lex->LookAhead(0)==TOK_SCOPE)
  {
    int t=lex->LookAhead(1);
    if(t==TOK_IDENTIFIER || t=='~' || t==TOK_OPERATOR)
      return true;
  }

  return false;
}

/*
  template.args : '<' any* '>'

  template.args must be followed by '(' or '::'
*/
bool Parser::isTemplateArgs()
{
  int i=0;
  int t=lex->LookAhead(i++);

  #ifdef DEBUG
  std::cout << "Parser::isTemplateArgs 0\n";
  #endif

  if(t=='<')
  {
    int n=1;

    while(n>0)
    {
      #ifdef DEBUG
      std::cout << "Parser::isTemplateArgs 1\n";
      #endif

      int u=lex->LookAhead(i++);

      #ifdef DEBUG
      std::cout << "Parser::isTemplateArgs 2\n";
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
          int v=lex->LookAhead(i++);

          #ifdef DEBUG
          std::cout << "Parser::isTemplateArgs 3\n";
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

      #ifdef DEBUG
      std::cout << "Parser::isTemplateArgs 4\n";
      #endif
    }

    #ifdef DEBUG
    std::cout << "Parser::isTemplateArgs 5\n";
    #endif

    t=lex->LookAhead(i);

    #ifdef DEBUG
    std::cout << "Parser::isTemplateArgs 6\n";
    #endif

    return t==TOK_SCOPE || t=='(';
  }

  #ifdef DEBUG
  std::cout << "Parser::isTemplateArgs 7\n";
  #endif

  return false;
}

/*
  function.body  : compound.statement
*/
bool Parser::rFunctionBody(codet &body)
{
  return rCompoundStatement(body);
}

/*
  compound.statement
  : '{' (statement)* '}'
*/
bool Parser::rCompoundStatement(codet &statement)
{
  Token ob, cb;

  #ifdef DEBUG
  std::cout << "Parser::rCompoundStatement 1\n";
  #endif

  if(lex->GetToken(ob)!='{')
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rCompoundStatement 2\n";
  #endif

  statement=code_blockt();

  while(lex->LookAhead(0)!='}')
  {
    codet statement2;

    if(!rStatement(statement2))
    {
      if(!SyntaxError())
        return false;        // too many errors

      SkipTo('}');
      lex->GetToken(cb);
      return true;        // error recovery
    }

    statement.move_to_operands(statement2);
  }

  if(lex->GetToken(cb)!='}')
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
*/
bool Parser::rStatement(codet &statement)
{
  Token tk1, tk2, tk3;
  int k;

  #ifdef DEBUG
  std::cout << "Parser::rStatement 0 " << lex->LookAhead(0) << "\n";
  #endif

  switch(k=lex->LookAhead(0))
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
    lex->GetToken(tk1);

    if(k==TOK_BREAK)
      statement=codet(ID_break);
    else // CONTINUE
      statement=codet(ID_continue);

    set_location(statement, tk1);

    if(lex->GetToken(tk2)!=';')
      return false;

    return true;

  case TOK_RETURN:
    #ifdef DEBUG
    std::cout << "Parser::rStatement RETURN 0\n";
    #endif

    lex->GetToken(tk1);

    statement=codet(ID_return);
    set_location(statement, tk1);

    if(lex->LookAhead(0)==';')
    {
      #ifdef DEBUG
      std::cout << "Parser::rStatement RETURN 1\n";
      #endif
      lex->GetToken(tk2);
    }
    else
    {
      #ifdef DEBUG
      std::cout << "Parser::rStatement RETURN 2\n";
      #endif

      exprt exp;

      if(!rCommaExpression(exp))
        return false;

      #ifdef DEBUG
      std::cout << "Parser::rStatement RETURN 3\n";
      #endif

      if(lex->GetToken(tk2)!=';')
        return false;

      statement.move_to_operands(exp);
    }

    return true;

  case TOK_GOTO:
    lex->GetToken(tk1);

    statement=codet(ID_goto);
    set_location(statement, tk1);

    if(lex->GetToken(tk2)!=TOK_IDENTIFIER)
      return false;

    if(lex->GetToken(tk3)!=';')
      return false;

    statement.set(ID_destination, tk2.text);

    return true;

  case TOK_CASE:
    {
      lex->GetToken(tk1);

      statement=codet(ID_code);
      set_location(statement, tk1);
      statement.set(ID_statement, ID_label);

      exprt exp;
      if(!rExpression(exp))
        return false;

      exprt &case_ops=statement.add_expr(ID_case);
      case_ops.copy_to_operands(exp);

      if(lex->GetToken(tk2)!=':')
        return false;

      codet statement2;
      if(!rStatement(statement2))
        return false;

      statement.move_to_operands(statement2);
    }
    return true;

  case TOK_DEFAULT:
    {
      lex->GetToken(tk1);

      statement=codet(ID_code);
      set_location(statement, tk1);
      statement.set(ID_statement, ID_label);
      statement.set(ID_default, true);

      if(lex->GetToken(tk2)!=':')
        return false;

      codet statement2;
      if(!rStatement(statement2))
        return false;

      statement.move_to_operands(statement2);

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
    if(lex->LookAhead(1)==':')        // label statement
    {
      lex->GetToken(tk1);

      statement=codet(ID_label);
      set_location(statement, tk1);
      statement.set(ID_label, tk1.text);

      lex->GetToken(tk2);

      codet statement2;
      if(!rStatement(statement2))
        return false;

      statement.move_to_operands(statement2);
      return true;
    }

    return rExprStatement(statement);
    
  case TOK_USING:
    {
      cpp_usingt cpp_using;

      if(!rUsing(cpp_using))
        return false;
        
      // TODO
        
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
  Token tk1, tk2, tk3, tk4;

  if(lex->GetToken(tk1)!=TOK_IF)
    return false;

  statement=codet(ID_ifthenelse);
  set_location(statement, tk1);

  if(lex->GetToken(tk2)!='(')
    return false;

  exprt exp;
  if(!rCondition(exp))
    return false;

  if(lex->GetToken(tk3)!=')')
    return false;

  codet then;
  if(!rStatement(then))
    return false;

  statement.reserve_operands(3);
  statement.move_to_operands(exp);
  statement.move_to_operands(then);

  if(lex->LookAhead(0)==TOK_ELSE)
  {
    lex->GetToken(tk4);

    codet otherwise;
    if(!rStatement(otherwise))
      return false;

    statement.move_to_operands(otherwise);
  }

  return true;
}

/*
  switch.statement
  : SWITCH '(' comma.expression ')' statement
*/
bool Parser::rSwitchStatement(codet &statement)
{
  Token tk1, tk2, tk3;

  if(lex->GetToken(tk1)!=TOK_SWITCH)
    return false;

  statement=codet(ID_switch);
  set_location(statement, tk1);

  if(lex->GetToken(tk2)!='(')
    return false;

  exprt exp;
  if(!rCondition(exp))
    return false;

  if(lex->GetToken(tk3)!=')')
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
  Token tk1, tk2, tk3;

  if(lex->GetToken(tk1)!=TOK_WHILE)
    return false;

  statement=codet(ID_while);
  set_location(statement, tk1);

  if(lex->GetToken(tk2)!='(')
    return false;

  exprt exp;
  if(!rCondition(exp))
    return false;

  if(lex->GetToken(tk3)!=')')
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
  Token tk0, tk1, tk2, tk3, tk4;

  if(lex->GetToken(tk0)!=TOK_DO)
    return false;

  statement=codet(ID_dowhile);
  set_location(statement, tk0);

  codet body;
  if(!rStatement(body))
    return false;

  if(lex->GetToken(tk1)!=TOK_WHILE)
    return false;

  if(lex->GetToken(tk2)!='(')
    return false;

  exprt exp;
  if(!rCommaExpression(exp))
    return false;

  if(lex->GetToken(tk3)!=')')
    return false;

  if(lex->GetToken(tk4)!=';')
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
  Token tk1, tk2, tk3, tk4;

  if(lex->GetToken(tk1)!=TOK_FOR)
    return false;

  statement=codet(ID_for);
  set_location(statement, tk1);

  if(lex->GetToken(tk2)!='(')
    return false;

  codet exp1;

  if(!rExprStatement(exp1))
    return false;

  exprt exp2;

  if(lex->LookAhead(0)==';')
    exp2.make_nil();
  else
    if(!rCommaExpression(exp2))
      return false;

  if(lex->GetToken(tk3)!=';')
    return false;

  exprt exp3;

  if(lex->LookAhead(0)==')')
    exp3.make_nil();
  else
  {
    if(!rCommaExpression(exp3))
      return false;
  }

  if(lex->GetToken(tk4)!=')')
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
  Token tk, op, cp;

  if(lex->GetToken(tk)!=TOK_TRY)
    return false;

  statement=codet(ID_catch);
  set_location(statement, tk);

  codet body;
  cpp_declarationt handler;

  if(!rCompoundStatement(body))
    return false;

  statement.move_to_operands(body);

  do
  {
    if(lex->GetToken(tk)!=TOK_CATCH)
      return false;

    if(lex->GetToken(op)!='(')
      return false;

    if(lex->LookAhead(0)==TOK_ELLIPSIS)
    {
      lex->GetToken(cp);
      //handler=new Leaf(cp);
    }
    else
    {
      if(!rArgDeclaration(handler))
        return false;
    }

    if(lex->GetToken(cp)!=')')
      return false;

    if(!rCompoundStatement(body))
      return false;

    // TODO
    //st=Ptree::Snoc(st, Ptree::List(new LeafReserved(tk),
    //                 new Leaf(op), handler, new Leaf(cp),
    //                 body));
  }
  while(lex->LookAhead(0)==TOK_CATCH);

  return true;
}

bool Parser::rMSC_tryStatement(codet &statement)
{
  // These are for 'structured exception handling',
  // and are a relic from Visual C.
  
  Token tk, tk2, tk3;

  if(lex->GetToken(tk)!=TOK_MSC_TRY)
    return false;

  set_location(statement, tk);
    
  codet body1, body2;

  if(!rCompoundStatement(body1))
    return false;
    
  if(lex->LookAhead(0)==TOK_MSC_EXCEPT)
  {
    lex->GetToken(tk);
    statement.set_statement(ID_msc_try_except);
    
    // get '(' comma.expression ')'
    
    if(lex->GetToken(tk2)!='(')
      return false;

    exprt exp;
    if(!rCommaExpression(exp))
      return false;

    if(lex->GetToken(tk3)!=')')
      return false;
      
    if(!rCompoundStatement(body2))
      return false;
      
    statement.move_to_operands(body1, exp, body2);
  }
  else if(lex->LookAhead(0)==TOK_MSC_FINALLY)
  {
    lex->GetToken(tk);
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
  
  Token tk;

  if(lex->GetToken(tk)!=TOK_MSC_LEAVE)
    return false;

  statement=codet("msc_leave");
  set_location(statement, tk);

  return true;
}

bool Parser::rGCCAsmStatement(codet &statement)
{
  Token tk;

  #ifdef DEBUG
  std::cout << "Parser::rGCCAsmStatement 1\n";
  #endif // DEBUG

  // asm [volatile] ("stuff" [ : ["=S" [(__res)], ... ]]) ;

  if(lex->GetToken(tk)!=TOK_GCC_ASM) return false;

  statement=codet(ID_asm);
  statement.set(ID_flavor, ID_gcc);
  set_location(statement, tk);

  if(lex->LookAhead(0)==TOK_VOLATILE)
    lex->GetToken(tk);

  #ifdef DEBUG
  std::cout << "Parser::rGCCAsmStatement 3\n";
  #endif // DEBUG

  if(lex->GetToken(tk)!='(') return false;
  if(!rString(tk)) return false;

  statement.move_to_operands(tk.data);

  #ifdef DEBUG
  std::cout << "Parser::rGCCAsmStatement 3\n";
  #endif // DEBUG

  while(lex->LookAhead(0)!=')')
  {
    #ifdef DEBUG
    std::cout << "Parser::rGCCAsmStatement 4\n";
    #endif // DEBUG

    // get ':'
    if(lex->GetToken(tk)!=':') return false;

    for(;;)
    {
      if(lex->LookAhead(0)!=TOK_STRING) break;

      // get String
      rString(tk);

      if(lex->LookAhead(0)=='(')
      {
        // get '('
        lex->GetToken(tk);

        #ifdef DEBUG
        std::cout << "Parser::rGCCAsmStatement 5\n";
        #endif // DEBUG

        exprt expr;
        if(!rCommaExpression(expr)) return false;

        #ifdef DEBUG
        std::cout << "Parser::rGCCAsmStatement 6\n";
        #endif // DEBUG

        if(lex->GetToken(tk)!=')') return false;
      }

      // more?
      if(lex->LookAhead(0)!=',') break;
      lex->GetToken(tk);
    }
  }

  #ifdef DEBUG
  std::cout << "Parser::rGCCAsmStatement 7\n";
  #endif // DEBUG

  if(lex->GetToken(tk)!=')') return false;
  if(lex->GetToken(tk)!=';') return false;

  #ifdef DEBUG
  std::cout << "Parser::rGCCAsmStatement 8\n";
  #endif // DEBUG

  return true;
}

bool Parser::rMSCAsmStatement(codet &statement)
{
  Token tk;

  #ifdef DEBUG
  std::cout << "Parser::rMSCAsmStatement 1\n";
  #endif // DEBUG

  // asm "STUFF"
  // asm { "STUFF" }

  if(lex->GetToken(tk)!=TOK_MSC_ASM) return false;

  statement=codet(ID_asm);
  statement.set(ID_flavor, ID_msc);
  set_location(statement, tk);

  #ifdef DEBUG
  std::cout << "Parser::rMSCAsmStatement 2\n";
  #endif // DEBUG

  if(lex->LookAhead(0)=='{')
  {
    lex->GetToken(tk); // eat the '{'
  
    #ifdef DEBUG
    std::cout << "Parser::rMSCAsmStatement 3\n";
    #endif // DEBUG

    if(!rString(tk)) return false;
    statement.move_to_operands(tk.data);
    if(lex->GetToken(tk)!='}') return false;

    #ifdef DEBUG
    std::cout << "Parser::rMSCAsmStatement 4\n";
    #endif // DEBUG
  }
  else
  {
    #ifdef DEBUG
    std::cout << "Parser::rMSCAsmStatement 5\n";
    #endif // DEBUG

    if(!rString(tk)) return false;
    statement.move_to_operands(tk.data);

    #ifdef DEBUG
    std::cout << "Parser::rMSCAsmStatement 6\n";
    #endif // DEBUG
  }
  
  #ifdef DEBUG
  std::cout << "Parser::rMSCAsmStatement 7\n";
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
  Token tk;

  #ifdef DEBUG
  std::cout << "Parser::rExprStatement 0\n";
  #endif

  if(lex->LookAhead(0)==';')
  {
    #ifdef DEBUG
    std::cout << "Parser::rExprStatement 1\n";
    #endif

    lex->GetToken(tk);
    statement=codet(ID_skip);
    set_location(statement, tk);
    return true;
  }
  else
  {
    #ifdef DEBUG
    std::cout << "Parser::rExprStatement 2\n";
    #endif

    cpp_token_buffert::post pos=lex->Save();

    if(rDeclarationStatement(statement))
    {
      #ifdef DEBUG
      std::cout << "rDe: " << statement << std::endl;
      #endif
      return true;
    }
    else
    {
      exprt exp;

      lex->Restore(pos);

      #ifdef DEBUG
      std::cout << "Parser::rExprStatement 3\n";
      #endif

      if(!rCommaExpression(exp))
        return false;

      #ifdef DEBUG
      std::cout << "Parser::rExprStatement 4\n";
      #endif

      #ifdef DEBUG
      std::cout << "Parser::rExprStatement 5 " << lex->LookAhead(0) << "\n";
      #endif

      if(lex->GetToken(tk)!=';')
        return false;

      #ifdef DEBUG
      std::cout << "Parser::rExprStatement 6\n";
      #endif

      statement=codet(ID_expression);
      statement.location()=exp.location();
      statement.move_to_operands(exp);
      return true;
    }
  }
}

bool Parser::rCondition(exprt &statement)
{
  cpp_token_buffert::post pos=lex->Save();

  cpp_declarationt declaration;

  if(rSimpleDeclaration(declaration))
  {
    statement=codet(ID_decl);
    statement.move_to_operands(declaration);
    return true;
  }
  else
  {
    lex->Restore(pos);

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
  std::cout << "Parser::rDeclarationStatement 1\n";
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
  std::cout << "Parser::rDeclarationStatement 2\n";
  #endif

  if(integral.is_not_nil())
    return rIntegralDeclStatement(statement, storage_spec, integral, cv_q);
  else
  {
    int t=lex->LookAhead(0);

    #ifdef DEBUG
    std::cout << "Parser::rDeclarationStatement 3 " << t << "\n";
    #endif

    if(cv_q.is_not_nil() &&
       ((t==TOK_IDENTIFIER && lex->LookAhead(1)=='=') || t=='*'))
    {
      #ifdef DEBUG
      std::cout << "Parser::rDeclarationStatement 4\n";
      #endif

      statement=codet(ID_decl);
      statement.operands().resize(1);
      cpp_declarationt &declaration=(cpp_declarationt &)(statement.op0());
      return rConstDeclaration(declaration, storage_spec, member_spec, cv_q);
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
  Token tk;

  if(!optCvQualify(cv_q))
    return false;

  merge_types(cv_q, integral);

  cpp_declarationt declaration;
  declaration.type().swap(integral);
  declaration.storage_spec().swap(storage_spec);

  if(lex->LookAhead(0)==';')
  {
    lex->GetToken(tk);
    statement=codet(ID_decl);
    set_location(statement, tk);
    statement.move_to_operands(declaration);
  }
  else
  {
    if(!rDeclarators(declaration.declarators(), false, true))
      return false;

    if(lex->GetToken(tk)!=';')
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
  Token tk;

  #ifdef DEBUG
  std::cout << "Parser::rOtherDeclStatement 1\n";
  #endif // DEBUG

  if(!rName(type_name))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rOtherDeclStatement 2\n";
  #endif // DEBUG

  if(!optCvQualify(cv_q))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rOtherDeclStatement 3\n";
  #endif // DEBUG

  merge_types(cv_q, type_name);

  cpp_declarationt declaration;
  declaration.type().swap(type_name);
  declaration.storage_spec().swap(storage_spec);

  if(!rDeclarators(declaration.declarators(), false, true))
    return false;

  #ifdef DEBUG
  std::cout << "Parser::rOtherDeclStatement 4\n";
  #endif // DEBUG

  if(lex->GetToken(tk)!=';')
    return false;

  statement=codet(ID_decl);
  set_location(statement, tk);
  statement.move_to_operands(declaration);

  return true;
}

bool Parser::MaybeTypeNameOrClassTemplate(Token&)
{
  return true;
}

void Parser::SkipTo(int token)
{
  Token tk;

  for(;;)
  {
    int t=lex->LookAhead(0);
    if(t==token || t=='\0')
      break;
    else
      lex->GetToken(tk);
  }
}

/*******************************************************************\

Function: Parser::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool Parser::parse()
{
  number_of_errors=0;

  #if 1
  cpp_itemt item;

  while(rProgram(item))
  {
    parser->parse_tree.items.push_back(cpp_itemt());
    parser->parse_tree.items.back().swap(item);
  }

  #else
  Token tk;

  while(lex->GetToken(tk))
    std::cout << tk.text << ' ';

  std::cout << std::endl;
  #endif

  return number_of_errors!=0;
}

/*******************************************************************\

Function: cpp_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cpp_parse()
{
  Parser parser;
  parser.lex=&cpp_parser.token_buffer;
  parser.parser=&cpp_parser;
  return parser.parse();
}
