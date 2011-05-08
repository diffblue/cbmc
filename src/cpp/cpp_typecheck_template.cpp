/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <expr_util.h>
#include <i2string.h>
#include <simplify_expr_class.h>
#include <simplify_expr.h>

#include "cpp_type2name.h"
#include "cpp_typecheck.h"
#include "cpp_declarator_converter.h"
#include "cpp_template_type.h"
#include "cpp_convert_type.h"
#include "cpp_template_args.h"

/*******************************************************************\

Function: cpp_typecheckt::check_template_restrictions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::check_template_restrictions(
  const irept &cpp_name,
  const irep_idt &final_identifier,
  const typet &final_type)
{
  if(final_type.id()==ID_template)
  {
    // subtype must be class or function

    if(final_type.subtype().id()!=ID_struct &&
       final_type.subtype().id()!=ID_code)
    {
      err_location(cpp_name);
      str << "template only allowed with classes or functions,"
             " but got `" << to_string(final_type.subtype()) << "'";
      throw 0;
    }
  }
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_template_class

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_template_class(
  cpp_declarationt &declaration)
{
  // Do template arguments. This also sets up the template scope.
  cpp_scopet &template_scope=
    typecheck_template_parameters(declaration.template_type());

  typet &type=declaration.type();
  template_typet &template_type=declaration.template_type();

  bool has_body=type.find(ID_body).is_not_nil();

  const cpp_namet &cpp_name=
    static_cast<const cpp_namet &>(type.find(ID_tag));

  std::string identifier, base_name;
  cpp_name.convert(identifier, base_name);

  if(identifier!=base_name)
  {
    err_location(cpp_name.location());
    throw "no namespaces allowed here";
  }

  if(base_name.empty())
  {
    err_location(type.location());
    throw "template classes must not be anonymous";
  }
  
  const cpp_template_args_non_tct &partial_specialization_args=
    declaration.partial_specialization_args();
  
  const irep_idt symbol_name=
    template_class_identifier(
      base_name, template_type, partial_specialization_args);

  #if 0
  // Check if the name is already used by a different template
  // in the same scope.
  {
    cpp_scopet::id_sett id_set;
    cpp_scopes.current_scope().lookup(
      base_name,
      cpp_scopet::SCOPE_ONLY,
      cpp_scopet::TEMPLATE,
      id_set);

    if(!id_set.empty())
    {
      const symbolt &previous=lookup((*id_set.begin())->identifier);
      if(previous.name!=symbol_name || id_set.size()>1)
      {
        err_location(cpp_name.location());
        str << "template declaration of `" << base_name.c_str()
            << " does not match previous declaration\n";
        str << "location of previous definition: " << previous.location;
        throw 0;
      }
    }
  }
  #endif

  // check if we have it already
  
  contextt::symbolst::iterator previous_symbol=
    context.symbols.find(symbol_name);

  if(previous_symbol!=context.symbols.end())
  {
    // there already
  
    bool previous_has_body=
      previous_symbol->second.type.find(ID_type).find(ID_body).is_not_nil();

    if(has_body && previous_has_body)
    {
      err_location(cpp_name.location());
      str << "template struct `" << base_name
          << "' defined previously" << std::endl;
      str << "location of previous definition: "
          << previous_symbol->second.location;
      throw 0;
    }

    if(has_body)
    {
      // we replace the template!
      previous_symbol->second.type.swap(declaration);

      // we also replace the template scope (the old one could be deleted)
      cpp_scopes.id_map[symbol_name] = &template_scope;
    }

    assert(cpp_scopes.id_map[symbol_name]->id_class == cpp_idt::TEMPLATE_SCOPE);
    return;
  }
  
  // it's not there yet

  symbolt symbol;

  symbol.name=symbol_name;
  symbol.base_name=base_name;
  symbol.location=cpp_name.location();
  symbol.mode=current_mode;
  symbol.module=module;
  symbol.type.swap(declaration);
  symbol.is_macro=false;
  symbol.value=exprt("template_decls");

  symbol.pretty_name=
    cpp_scopes.current_scope().prefix+id2string(symbol.base_name);

  symbolt *new_symbol;
  if(context.move(symbol, new_symbol))
    throw "cpp_typecheckt::typecheck_compound_type: context.move() failed";

  // put into current scope
  cpp_idt &id=cpp_scopes.put_into_scope(*new_symbol);
  id.id_class=cpp_idt::TEMPLATE;
  id.prefix=cpp_scopes.current_scope().prefix+
            id2string(new_symbol->base_name);

  // link the template symbol with the template scope
  cpp_scopes.id_map[symbol_name]=&template_scope;
  assert(cpp_scopes.id_map[symbol_name]->id_class==cpp_idt::TEMPLATE_SCOPE);
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_template_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_template_function(
  cpp_declarationt &declaration)
{
  assert(declaration.declarators().size()==1);

  cpp_declaratort &declarator=declaration.declarators()[0];

  const cpp_namet &cpp_name = to_cpp_name(declarator.add(ID_name));
  std::string identifier, base_name;

  if(cpp_name.is_qualified() ||
     cpp_name.has_template_args())
  {
    // must be of the form: name1<template_args>::name2;
    if(cpp_name.get_sub().size() != 4 ||
       cpp_name.get_sub()[0].id() != ID_name ||
       cpp_name.get_sub()[1].id() != ID_template_args ||
       cpp_name.get_sub()[2].id() != "::" ||
       cpp_name.get_sub()[3].id() != ID_name)
    {
      if(cpp_name.get_sub().size() != 5 ||
         cpp_name.get_sub()[0].id() != ID_name ||
         cpp_name.get_sub()[1].id() != ID_template_args ||
         cpp_name.get_sub()[2].id() != "::" ||
         cpp_name.get_sub()[3].id() != ID_operator)
      {
        err_location(cpp_name);
        str << "bad template name";
        throw 0;
      }
    }

    // let's find the template class this function template belongs to.
    cpp_scopet::id_sett id_set;

    cpp_scopes.current_scope().lookup(
      cpp_name.get_sub().front().get(ID_identifier),
      cpp_scopet::SCOPE_ONLY,
      id_set);

    if(id_set.empty())
    {
      str << cpp_scopes.current_scope();
      err_location(cpp_name);
      str << "identifier `" << cpp_name.get_sub().front().get(ID_identifier)
          << "' not found";
      throw 0;
    }
    else if(id_set.size()>1)
    {
      err_location(cpp_name);
      str << "identifier `" << cpp_name.get_sub().front().get(ID_identifier)
          << "' is ambigious";
      throw 0;
    }
    else if((*(id_set.begin()))->id_class != cpp_idt::TEMPLATE)
    {
      std::cerr << *(*id_set.begin()) << std::endl;
      err_location(cpp_name);
      str << "identifier `" << cpp_name.get_sub().front().get(ID_identifier)
          << "' is not a template";
      throw 0;
    }

    const cpp_idt &cpp_id=**(id_set.begin());
    symbolt &template_symbol=
      context.symbols.find(cpp_id.identifier)->second;

    exprt &template_methods = static_cast<exprt &>(
      template_symbol.value.add("template_methods"));
      
    template_methods.copy_to_operands(declaration);

    // save current scope
    cpp_save_scopet cpp_saved_scope(cpp_scopes);

    const irept &instantiated_with = 
      template_symbol.value.add("instantiated_with");
      
    for(unsigned i=0; i<instantiated_with.get_sub().size(); i++)
    {
      const cpp_template_args_tct &tc_template_args=
        static_cast<const cpp_template_args_tct &>(instantiated_with.get_sub()[i]);

      cpp_declarationt decl_tmp=declaration;

      // do template arguments
      // this also sets up the template scope of the method
      cpp_scopet &method_scope=
        typecheck_template_parameters(decl_tmp.template_type());

      cpp_scopes.go_to(method_scope);

      // mapping from template arguments to values/types
      template_map.build(decl_tmp.template_type(), tc_template_args);

      decl_tmp.remove(ID_template_type);
      decl_tmp.remove(ID_is_template);

      convert(decl_tmp);
      cpp_saved_scope.restore();
    }

    return;
  }

  // do template arguments
  // this also sets up the template scope
  cpp_scopet &template_scope=
    typecheck_template_parameters(declaration.template_type());

  cpp_name.convert(identifier, base_name);
  if(identifier!=base_name)
  {
    err_location(declaration);
    str << "namespaces not supported in template declaration";
    throw 0;
  }

  template_typet &template_type=declaration.template_type();
    
  typet function_type=
    declarator.merge_type(declaration.type());

  cpp_convert_plain_type(function_type);

  irep_idt symbol_name=
    template_function_identifier(
      base_name,
      template_type,
      function_type);

  bool has_value=declarator.find(ID_value).is_not_nil();

  // check if we have it already

  contextt::symbolst::iterator previous_symbol=
    context.symbols.find(symbol_name);

  if(previous_symbol!=context.symbols.end())
  {
    bool previous_has_value =
     to_cpp_declaration(previous_symbol->second.type).
       declarators()[0].find(ID_value).is_not_nil();

    if(has_value && previous_has_value)
    {
      err_location(cpp_name.location());
      str << "function template symbol `" << base_name
          << "' declared previously" << std::endl;
      str << "location of previous definition: "
          << previous_symbol->second.location;
      throw 0;
    }

    if(has_value)
    {
      previous_symbol->second.type.swap(declaration);
      cpp_scopes.id_map[symbol_name]=&template_scope;
    }

    // todo: the old template scope now is useless,
    // and thus, we could delete it
    return;
  }

  symbolt symbol;
  symbol.name=symbol_name;
  symbol.base_name=base_name;
  symbol.location=cpp_name.location();
  symbol.mode=current_mode;
  symbol.module=module;
  symbol.value.make_nil();

  symbol.type.swap(declaration);
  symbol.pretty_name=
    cpp_scopes.current_scope().prefix+id2string(symbol.base_name);

  symbolt *new_symbol;
  if(context.move(symbol, new_symbol))
    throw "cpp_typecheckt::typecheck_compound_type: context.move() failed";

  // put into scope
  cpp_idt &id=cpp_scopes.put_into_scope(*new_symbol);
  id.id_class=cpp_idt::TEMPLATE;
  id.prefix=cpp_scopes.current_scope().prefix+
            id2string(new_symbol->base_name);

  // link the template symbol with the template scope
  assert(template_scope.id_class==cpp_idt::TEMPLATE_SCOPE);
  cpp_scopes.id_map[symbol_name] = &template_scope;
}

/*******************************************************************\

Function: cpp_typecheckt::template_class_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cpp_typecheckt::template_class_identifier(
  const irep_idt &base_name,
  const template_typet &template_type,
  const cpp_template_args_non_tct &partial_specialization_args)
{
  std::string identifier=
    cpp_identifier_prefix(current_mode)+"::"+
      cpp_scopes.current_scope().prefix+
      "template."+id2string(base_name) + "<";

  int counter=0;

  // these are probably not needed -- templates
  // should be unique in a namespace
  forall_expr(it, template_type.parameters())
  {
    if(counter!=0) identifier+=",";
  
    if(it->id()==ID_type)
      identifier+="Type"+i2string(counter);
    else
      identifier+="Non_Type"+i2string(counter);

    counter++;
  }

  identifier += ">";
  
  if(!partial_specialization_args.arguments().empty())
  {
    identifier+="_specialized_to_<";
  
    counter=0;
    for(cpp_template_args_non_tct::argumentst::const_iterator
        it=partial_specialization_args.arguments().begin();
        it!=partial_specialization_args.arguments().end();
        it++, counter++)
    {  
      if(counter!=0) identifier+=",";

      if(it->id()==ID_type || it->id()=="ambiguous")
        identifier+=cpp_type2name(it->type());
      else
        identifier+=cpp_expr2name(*it);
    }
    
    identifier+=">";
  }
  
  return identifier;
}

/*******************************************************************\

Function: cpp_typecheckt::template_function_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cpp_typecheckt::template_function_identifier(
  const irep_idt &base_name,
  const template_typet &template_type,
  const typet &function_type)
{
  // we first build something without function arguments
  cpp_template_args_non_tct partial_specialization_args;
  std::string identifier=
    template_class_identifier(base_name, template_type,
                              partial_specialization_args);

  // we must also add the signature of the function to the identifier
  identifier+=cpp_type2name(function_type);

  return identifier;
}

/*******************************************************************\

Function: cpp_typecheckt::convert_template_class_specialization

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::convert_template_class_specialization(
  cpp_declarationt &declaration)
{
  cpp_save_scopet saved_scope(cpp_scopes);

  typet &type=declaration.type();

  assert(type.id()==ID_struct);

  cpp_namet &cpp_name=
    static_cast<cpp_namet &>(type.add(ID_tag));

  if(cpp_name.is_qualified())
  {
    err_location(cpp_name.location());
    str << "qualifiers not excpected here";
    throw 0;
  }
  
  if(cpp_name.get_sub().size()!=2 ||
     cpp_name.get_sub()[0].id()!=ID_name ||
     cpp_name.get_sub()[1].id()!=ID_template_args)
  {
    // currently we are more restrictive
    // than the standard
    err_location(cpp_name.location());
    str << "bad template-class-sepcialization name";                                                
    throw 0;
  }

  irep_idt base_name=
    cpp_name.get_sub()[0].get(ID_identifier);

  // copy the template arguments    
  const cpp_template_args_non_tct template_args_non_tc=
    to_cpp_template_args_non_tc(cpp_name.get_sub()[1]);

  // Remove the template arguments from the name.
  cpp_name.get_sub().pop_back();

  // get the template symbol

  cpp_scopest::id_sett id_set;
  cpp_scopes.current_scope().lookup(
    base_name, cpp_scopet::SCOPE_ONLY, cpp_idt::TEMPLATE, id_set);

  // remove any specializations
  for(cpp_scopest::id_sett::iterator
      it=id_set.begin();
      it!=id_set.end();
      ) // no it++
  {
    cpp_scopest::id_sett::iterator next=it;
    next++;
    
    if(lookup((*it)->identifier).type.
         find("specialization_of").is_not_nil())
      id_set.erase(it);
    
    it=next;
  }

  // only one should be left
  if(id_set.empty())
  {
    err_location(type.location());
    str << "template `" << base_name << "' not found";
    throw 0;
  }
  else if(id_set.size()>1)
  {
    err_location(type);
    str << "template `" << base_name << "' is ambiguous";
    throw 0;
  }
  
  contextt::symbolst::iterator s_it=
    context.symbols.find((*id_set.begin())->identifier);
    
  assert(s_it!=context.symbols.end());
  
  symbolt &template_symbol=s_it->second;
    
  if(!template_symbol.type.get_bool(ID_is_template))
  {
    err_location(type);
    str << "expected a template";
  }

  #if 0
  // is this partial specialization?  
  if(declaration.template_type().parameters().empty())
  {
    // typecheck arguments -- these are for the 'primary' template!
    cpp_template_args_tct template_args_tc=
      typecheck_template_args(
        declaration.location(),
        to_cpp_declaration(template_symbol.type).template_type(),
        template_args_non_tc);
    
    // Full specialization, i.e., template<>.
    // We instantiate.
    instantiate_template(
      cpp_name.location(),
      template_symbol,
      template_args_tc,
      type);
  }
  else
  #endif
  
  {
    // partial -- we typecheck
    declaration.partial_specialization_args()=template_args_non_tc;
    declaration.set_specialization_of(template_symbol.name);

    // We can't typecheck arguments yet, they are used
    // for guessing later. But we can check the number.
    if(template_args_non_tc.arguments().size()!=
       to_cpp_declaration(template_symbol.type).template_type().parameters().size())
    {
      err_location(cpp_name.location());
      throw "template specialization with wrong number of arguments";
    }    
    
    typecheck_template_class(declaration);
  }
}

/*******************************************************************\

Function: cpp_typecheckt::convert_template_function_or_member_specialization

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::convert_template_function_or_member_specialization(
  cpp_declarationt &declaration)
{
  cpp_save_scopet saved_scope(cpp_scopes);
  
  if(declaration.declarators().size()!=1 ||
     declaration.declarators().front().type().id()!="function_type")
  {
    err_location(declaration.type());
    str << "expected function template specialization";
    throw 0;
  }

  assert(declaration.declarators().size()==1);
  cpp_declaratort declarator=declaration.declarators().front();
  cpp_namet &cpp_name=declarator.name();

  if(cpp_name.is_qualified())
  {
    err_location(cpp_name.location());
    str << "qualifiers not excpected here";
    throw 0;
  }
  
  // There is specialization (instantiation with template arguments)
  // but also function overloading (no template arguments)
  
  assert(!cpp_name.get_sub().empty());
  
  if(cpp_name.get_sub().back().id()==ID_template_args)
  {
    // proper specialization with arguments
    if(cpp_name.get_sub().size() != 2 ||
       cpp_name.get_sub()[0].id() != ID_name ||
       cpp_name.get_sub()[1].id() != ID_template_args)
    {
      // currently we are more restrictive
      // than the standard
      err_location(cpp_name.location());
      str << "bad template-function-specialization name";
      throw 0;
    }

    std::string base_name=
      cpp_name.get_sub()[0].get(ID_identifier).c_str();

    cpp_scopest::id_sett id_set;
    cpp_scopes.current_scope().lookup(
      base_name, cpp_scopet::SCOPE_ONLY, id_set);

    if(id_set.empty())
    {
      err_location(cpp_name.location());
      str << "template `" << base_name << "' not found";
      throw 0;
    }
    else if(id_set.size()>1)
    {
      err_location(cpp_name.location());
      str << "template `" << base_name << "' is ambiguous";
    }
    
    const symbolt &template_symbol=
      lookup((*id_set.begin())->identifier);

    cpp_template_args_tct template_args=
      typecheck_template_args(
        declaration.location(),
        template_symbol,
        to_cpp_template_args_non_tc(cpp_name.get_sub()[1]));

    cpp_name.get_sub().pop_back();

    typet specialization;
    specialization.swap(declarator);

    instantiate_template(
      cpp_name.location(),
      template_symbol,
      template_args,
      template_args,
      specialization);
  }
  else
  {
    // Just overloading, but this is still a template
    // for disambiguation purposes!
    // http://www.gotw.ca/publications/mill17.htm
    cpp_declarationt new_declaration=declaration;
    
    new_declaration.remove(ID_template_type);
    new_declaration.remove(ID_is_template);
    new_declaration.set(ID_C_template, ""); // todo, get identifier
    
    convert_non_template_declaration(new_declaration);
  }
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_template_parameters

  Inputs:

 Outputs:

 Purpose:/

\*******************************************************************/

cpp_scopet &cpp_typecheckt::typecheck_template_parameters(
  template_typet &type)
{
  cpp_save_scopet cpp_saved_scope(cpp_scopes);

  assert(type.id()==ID_template);

  std::string id_suffix="template::"+i2string(template_counter++);

  // produce a new scope for the template parameters
  cpp_scopet &template_scope=
    cpp_scopes.current_scope().new_scope(
      cpp_scopes.current_scope().prefix+id_suffix);

  template_scope.prefix=template_scope.get_parent().prefix+id_suffix;
  template_scope.id_class=cpp_idt::TEMPLATE_SCOPE;

  cpp_scopes.go_to(template_scope);

  // put template parameters into this scope
  template_typet::parameterst &parameters=type.parameters();

  unsigned anon_count=0;

  Forall_expr(it, parameters)
  {
    exprt &parameter=*it;

    cpp_declarationt declaration;
    declaration.swap(static_cast<cpp_declarationt &>(parameter));

    cpp_declarator_convertert cpp_declarator_converter(*this);

    // there must be _one_ declarator
    assert(declaration.declarators().size()==1);

    cpp_declaratort &declarator=declaration.declarators().front();

    // there might be a default type or value
    exprt default_expr=declarator.value();
    typet default_type=(const typet &)(declarator.value());

    // it may be anonymous
    if(declarator.name().is_nil())
    {
      irept name(ID_name);
      name.set(ID_identifier, "anon#"+i2string(++anon_count));
      declarator.name()=cpp_namet();
      declarator.name().get_sub().push_back(name);
    }

    cpp_declarator_converter.is_typedef=declaration.get_bool(ID_is_type);
    cpp_declarator_converter.is_template_argument=true;

    const symbolt &symbol=
      cpp_declarator_converter.convert(declaration, declarator);

    if(cpp_declarator_converter.is_typedef)
    {
      parameter=exprt(ID_type, typet(ID_symbol));
      parameter.type().set(ID_identifier, symbol.name);

      parameter.type().location()=declaration.find_location();

      if(default_type.is_not_nil())
      {
        parameter.add("#default") = default_type;
      }
    }
    else
    {
      parameter=symbol_expr(symbol);

      if(default_expr.is_not_nil())
      {
        typecheck_expr(default_expr);
        parameter.add("#default") = default_expr;
      }
    }

    parameter.location()=declaration.find_location();
  }

  // continue without adding to the prefix
  template_scope.prefix=template_scope.get_parent().prefix;

  return template_scope;
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_template_args

  Inputs: location, non-typechecked template arguments

 Outputs: typechecked template arguments

 Purpose:

\*******************************************************************/

cpp_template_args_tct cpp_typecheckt::typecheck_template_args(
  const locationt &location,
  const symbolt &template_symbol,
  const cpp_template_args_non_tct &template_args)
{
  // old stuff
  assert(template_args.id()!="already_typechecked");

  assert(template_symbol.type.get_bool(ID_is_template));

  const template_typet &template_type=
    to_cpp_declaration(template_symbol.type).template_type();

  // bad re-cast
  cpp_template_args_tct result=
    (const cpp_template_args_tct &)(template_args);

  cpp_template_args_tct::argumentst &args=
    result.arguments();
    
  const template_typet::parameterst &parameters=
    template_type.parameters();
    
  if(parameters.size()<args.size())
  {
    err_location(location);
    str << "too many template arguments (expected "
        << parameters.size() << ", got "
        << args.size() << ")";
    throw 0;
  }

  for(unsigned i=0; i<parameters.size(); i++)
  {
    const exprt &parameter=parameters[i];
    
    if(i>=args.size())
    {
      // Check for default parameter.
      // These may depend on previous arguments.
      exprt default_value=
        static_cast<const exprt &>(parameter.find("#default"));

      if(default_value.is_nil())
      {
        err_location(location);
        throw "not enough template arguments";
      }
      
      args.push_back(default_value);
      
      // we need to enter the template scope to typecheck these
    }

    exprt &arg=args[i];

    if(parameter.id()==ID_type)
    {
      if(arg.id()==ID_type)
      {
        typecheck_type(arg.type());
      }
      else if(arg.id()=="ambiguous")
      {
        typecheck_type(arg.type());
        typet t=arg.type();
        arg=exprt(ID_type, t);
      }
      else
      {
        err_location(arg);
        str << "expected type, but got expression";
        throw 0;
      }
    }
    else // expression
    {
      if(arg.id()==ID_type)
      {
        err_location(arg);
        str << "expected expression, but got type";
        throw 0;
      }
      else if(arg.id()=="ambiguous")
      {
        exprt e;
        e.swap(arg.type());
        arg.swap(e);
      }

      typecheck_expr(arg);
      simplify(arg, *this);
      implicit_typecast(arg, parameter.type());
    }    
  }

  assert(args.size()==parameters.size());
  
  return result;
}

/*******************************************************************\

Function: cpp_typecheckt::convert_template_declaration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::convert_template_declaration(
  cpp_declarationt &declaration)
{
  assert(declaration.is_template());

  if(declaration.member_spec().is_virtual())
  {
    err_location(declaration);
    str <<  "invalid use of 'virtual' in template declaration";
    throw 0;
  }

  if(convert_typedef(declaration.type()))
  {
    err_location(declaration);
    str << "template declaration for typedef";
    throw 0;
  }

  typet &type=declaration.type();

  // there are 1) function templates and 2) template classes

  if(declaration.is_template_class())
  {
    // there should not be declarators
    if(!declaration.declarators().empty())
    {
      err_location(declaration);
      throw "template class not expected to have declarators";
    }

    // it needs to be a template class
    if(type.id()!=ID_struct)
    {
      err_location(declaration);
      throw "expected template class";
    }

    // Is it class template specialization?
    // We can tell if there are template arguments in the class name,
    // like template<...> class tag<stuff> ...
    if((static_cast<const cpp_namet &>(
       type.find(ID_tag))).has_template_args())
    {
      convert_template_class_specialization(declaration);
      return;
    }

    typecheck_template_class(declaration);
    return;
  }
  else // maybe function template, maybe template class member
  {
    // there should be declarators
    if(declaration.declarators().empty())
    {
      err_location(declaration);
      throw "function template or member expected to have declarator";
    }

    // Is it function template specialization?
    // Only full specialization is allowed!
    if(declaration.template_type().parameters().empty())
    {
      convert_template_function_or_member_specialization(declaration);
      return;
    }
  
    typecheck_template_function(declaration);
    return;
  }
}

