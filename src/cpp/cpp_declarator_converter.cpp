/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <location.h>
#include <std_types.h>
#include <ansi-c/c_types.h>

#include "cpp_type2name.h"
#include "cpp_declarator_converter.h"
#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_declarator_convertert::cpp_declarator_convertert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cpp_declarator_convertert::cpp_declarator_convertert(
  class cpp_typecheckt &_cpp_typecheck):
  is_typedef(false),
  is_template(false),
  is_template_argument(false),
  is_friend(false),
  linkage_spec(_cpp_typecheck.current_linkage_spec),
  cpp_typecheck(_cpp_typecheck)
{
}

/*******************************************************************\

Function: cpp_declarator_convertert::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbolt &cpp_declarator_convertert::convert(
  const typet &type,
  const cpp_storage_spect &storage_spec,
  const cpp_member_spect &member_spec,
  cpp_declaratort &declarator)
{
  assert(type.is_not_nil());

  if(type.id()=="cpp-cast-operator")
  {
    typet type;
    type.swap(declarator.name().get_sub().back());
    declarator.type().subtype()=type;
    std::string tmp;
    cpp_typecheck.typecheck_type(type);
    irept name(ID_name);
    name.set(ID_identifier, "("+cpp_type2name(type)+")");
    declarator.name().get_sub().back().swap(name);
  }

  assert(declarator.id()==ID_cpp_declarator);
  final_type=declarator.merge_type(type);
  assert(final_type.is_not_nil());
  
  cpp_template_args_non_tct template_args;

  // run resolver on scope
  {
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

    cpp_typecheck_resolvet cpp_typecheck_resolve(cpp_typecheck);

    cpp_typecheck_resolve.resolve_scope(
      declarator.name(), base_name, template_args);

    scope=&cpp_typecheck.cpp_scopes.current_scope();
  }
  
  // check the type
  cpp_typecheck.typecheck_type(final_type);

  is_code=is_code_type(final_type);

  // global-scope arrays must have fixed size
  if(scope->is_global_scope())
    cpp_typecheck.check_fixed_size_array(final_type);

  get_final_identifier();

  // first see if it is a member
  if(scope->id_class==cpp_idt::CLASS && !is_friend)
  {
    // it's a member! it must be declared already

    typet &method_qualifier=
      static_cast<typet &>(declarator.method_qualifier());

    // adjust template type
    if(final_type.id()==ID_template)
    {
      assert(0);
      typet tmp;
      tmp.swap(final_type.subtype());
      final_type.swap(tmp);
    }

    // try static first
    contextt::symbolst::iterator c_it=
      cpp_typecheck.context.symbols.find(final_identifier);

    if(c_it==cpp_typecheck.context.symbols.end())
    {
      // adjust type if it's a non-static member function
      if(final_type.id()==ID_code)
        cpp_typecheck.adjust_method_type(
          scope->identifier, final_type, method_qualifier);

      get_final_identifier();

      // try again
      c_it=cpp_typecheck.context.symbols.find(final_identifier);

      if(c_it==cpp_typecheck.context.symbols.end())
      {
        cpp_typecheck.err_location(declarator.name());
        cpp_typecheck.str << "member `" << base_name
                          << "' not found in scope `"
                          << scope->identifier << "'";
        throw 0;
      }
    }

    assert(c_it!=cpp_typecheck.context.symbols.end());

    symbolt &symbol=c_it->second;

    combine_types(declarator.name().location(), final_type, symbol);
    enforce_rules(symbol);

    // If it is a constructor, we take care of the
    // object initialization
    if(final_type.get(ID_return_type)==ID_constructor)
    {
      const cpp_namet &name=declarator.name();

      exprt symbol_expr=
        cpp_typecheck.resolve(
          name,
          cpp_typecheck_resolvet::TYPE,
          cpp_typecheck_fargst());

      if(symbol_expr.id()!=ID_type ||
         symbol_expr.type().id()!=ID_symbol)
      {
        cpp_typecheck.err_location(name.location());
        cpp_typecheck.str << "error: expected type";
        throw 0;
      }

      irep_idt identifier=symbol_expr.type().get(ID_identifier);
      const symbolt &symb=cpp_typecheck.lookup(identifier);
      const typet &type = symb.type;
      assert(type.id()==ID_struct);

      if(declarator.find(ID_member_initializers).is_nil())
        declarator.set(ID_member_initializers, ID_member_initializers);

      cpp_typecheck.check_member_initializers(
        type.find(ID_bases),
        to_struct_type(type).components(),
        declarator.member_initializers());

      cpp_typecheck.full_member_initialization(
        to_struct_type(type),
        declarator.member_initializers());
    }

    if(!storage_spec.is_extern())
      symbol.is_extern=false;

    // initializer?
    handle_initializer(symbol, declarator);

    return symbol;
  }
  else
  {
    // no, it's no way a method
    
    // we won't allow the constructor/destructor type
    if(final_type.id()==ID_code &&
       to_code_type(final_type).return_type().id()==ID_constructor)
    {
      cpp_typecheck.err_location(declarator.name().location());
      cpp_typecheck.str << "function must have return type";
      throw 0;
    }

    // already there?
    contextt::symbolst::iterator c_it=
      cpp_typecheck.context.symbols.find(final_identifier);

    if(c_it==cpp_typecheck.context.symbols.end())
      return convert_new_symbol(storage_spec, member_spec, declarator);

    symbolt &symbol=c_it->second;
    
    if(!storage_spec.is_extern())
      symbol.is_extern = false;

    if(declarator.get_bool("#template_case"))
      return symbol;

    combine_types(declarator.name().location(), final_type, symbol);
    enforce_rules(symbol);

    // initializer?
    handle_initializer(symbol, declarator);

    if(symbol.type.id()=="cpp-template-type")
    {
      cpp_scopet::id_sett id_set;

      scope->lookup_identifier(symbol.name, cpp_idt::TEMPLATE_ARGUMENT, id_set);

      if(id_set.empty())
      {
        cpp_idt &identifier=
          cpp_typecheck.cpp_scopes.put_into_scope(symbol,*scope);
        identifier.id_class=cpp_idt::TEMPLATE_ARGUMENT;
      }
    }

    return symbol;
  }
}

/*******************************************************************\

Function: cpp_declarator_convertert::combine_types

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_declarator_convertert::combine_types(
  const locationt &location,
  const typet &decl_type,
  symbolt &symbol)
{
  if(symbol.type.id()==decl_type.id() &&
     decl_type.id()==ID_code)
  {
    // functions need special treatment due
    // to argument names, default values, and inlined-ness
    const code_typet &decl_code_type=to_code_type(decl_type);
    code_typet &symbol_code_type=to_code_type(symbol.type);
    
    if(decl_code_type.get_inlined())
      symbol_code_type.set_inlined(true);

    if(decl_code_type.return_type()==symbol_code_type.return_type() &&
       decl_code_type.arguments().size()==symbol_code_type.arguments().size())
    {
      for(unsigned i=0; i<decl_code_type.arguments().size(); i++)
      {
        const code_typet::argumentt &decl_argument=decl_code_type.arguments()[i];
        code_typet::argumentt &symbol_argument=symbol_code_type.arguments()[i];

        // first check type
        if(decl_argument.type()!=symbol_argument.type())
        {
          // The 'this' argument of virtual functions mismatches
          if(i!=0 || !symbol_code_type.get_bool("#is_virtual"))
          {
            cpp_typecheck.err_location(location);
            cpp_typecheck.str << "symbol `" << symbol.display_name()
                              << "': argument " << (i+1) << " type mismatch"
                              << std::endl;
            cpp_typecheck.str << "previous type: "
                              << cpp_typecheck.to_string(symbol_argument.type()) << std::endl;
            cpp_typecheck.str << "new type: "
                              << cpp_typecheck.to_string(decl_argument.type());
            throw 0;
          }
        }

        if(symbol.value.is_nil())
        {
          symbol_argument.set_base_name(decl_argument.get_base_name());
          symbol_argument.set_identifier(decl_argument.get_identifier());
          symbol_argument.location()=decl_argument.location();
        }
      }

      // ok
      return;
    }
  }
  else if(symbol.type==decl_type)
    return; // ok
  else if(symbol.type.id()==ID_array &&
          symbol.type.find(ID_size).is_nil() &&
          decl_type.id()==ID_array &&
          symbol.type.subtype()==decl_type.subtype())
  {
    symbol.type = decl_type;
    return; // ok
  }

  cpp_typecheck.err_location(location);
  cpp_typecheck.str << "symbol `" << symbol.display_name()
                    << "' already declared with different type"
                    << std::endl;
  cpp_typecheck.str << "previous type: "
                    << cpp_typecheck.to_string(symbol.type) << std::endl;
  cpp_typecheck.str << "new type: "
                    << cpp_typecheck.to_string(final_type);
  throw 0;
}

/*******************************************************************\

Function: cpp_declarator_convertert::enforce_rules

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_declarator_convertert::enforce_rules(const symbolt &symbol)
{
  // enforce rules for operator overloading
  operator_overloading_rules(symbol);

  // enforce rules about main()
  main_function_rules(symbol);
}

/*******************************************************************\

Function: cpp_declarator_convertert::handle_initializer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_declarator_convertert::handle_initializer(
  symbolt &symbol,
  cpp_declaratort &declarator)
{
  exprt &value=declarator.value();

  // moves member initializers into 'value'
  cpp_typecheck.move_member_initializers(
    declarator.member_initializers(),
    symbol.type,
    value);

  // any initializer to be done?
  if(value.is_nil())
    return;

  if(symbol.is_extern)
  {
    // the symbol is really located here
    symbol.is_extern=false;
  }
  
  if(symbol.value.is_nil())
  {
    // no initial value yet
    symbol.value.swap(value);

    if(is_code && declarator.type().id()!=ID_template)
      cpp_typecheck.add_function_body(&symbol);

    if(!is_code)
      cpp_typecheck.convert_initializer(symbol);
  }
  else
  {
    #if 0
    cpp_typecheck.err_location(declarator.name());

    if(is_code)
      cpp_typecheck.str << "body of function `"
                        << symbol.display_name()
                        << "' has already been defined";
    else
      cpp_typecheck.str << "symbol `"
                        << symbol.display_name()
                        << "' already has an initializer";

    throw 0;
    #endif
  }
}

/*******************************************************************\

Function: cpp_declarator_convertert::get_final_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_declarator_convertert::get_final_identifier()
{
  std::string identifier=id2string(base_name);

  // main is always "C" linkage, as a matter of principle
  if(is_code &&
     base_name==ID_main &&
     scope->prefix=="")
  {
    linkage_spec=ID_C;
  }

  if(is_code)
  {
    if(linkage_spec==ID_C)
    {
      // fine as is
    }
    else if(linkage_spec==ID_auto ||
            linkage_spec==ID_cpp)
    {
      // Is there already an `extern "C"' function with the same name
      // and the same signature?
      contextt::symbolst::const_iterator
        c_it=cpp_typecheck.context.symbols.find("c::"+identifier);
        
      if(c_it!=cpp_typecheck.context.symbols.end() &&
         cpp_typecheck.function_identifier(final_type)==
         cpp_typecheck.function_identifier(c_it->second.type))
      {
        // leave as is, no decoration
      }
      else
      {
        // add C++ decoration
        identifier+=id2string(cpp_typecheck.function_identifier(final_type));
      }
    }
  }

  final_identifier=
    "c::"+
    scope->prefix+
    identifier;
}

/*******************************************************************\

Function: cpp_declarator_convertert::convert_new_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbolt &cpp_declarator_convertert::convert_new_symbol(
  const cpp_storage_spect &storage_spec,
  const cpp_member_spect &member_spec,
  cpp_declaratort &declarator)
{
  irep_idt pretty_name=get_pretty_name();

  symbolt symbol;

  symbol.name=final_identifier;
  symbol.base_name=base_name;
  symbol.value=declarator.value();
  symbol.location=declarator.name().location();
  symbol.mode=linkage_spec==ID_auto?ID_cpp:linkage_spec;
  symbol.module=cpp_typecheck.module;
  symbol.type=final_type;
  symbol.is_type=is_typedef;
  symbol.is_macro=is_typedef && !is_template_argument;
  symbol.pretty_name=pretty_name;
  
  // Constant? These are propagated.
  if(symbol.type.get_bool(ID_C_constant) &&
     symbol.value.is_not_nil())
    symbol.is_macro=true;
  
  if(member_spec.is_inline())
    symbol.type.set(ID_C_inlined, true);

  if(!symbol.is_type)
  {
    if(!is_code)
    {
      // it is a variable
      symbol.is_state_var=true;
      symbol.is_lvalue = !is_reference(symbol.type) &&
                         !(symbol.type.get_bool(ID_C_constant) &&
                         is_number(symbol.type) &&
                         symbol.value.id() == ID_constant);

      if(cpp_typecheck.cpp_scopes.current_scope().is_global_scope())
      {
        symbol.is_static_lifetime=true;

        if(storage_spec.is_extern())
          symbol.is_extern=true;
      }
      else
      {
        if(storage_spec.is_static())
        {
          symbol.is_static_lifetime=true;
          symbol.is_file_local=true;
        }
        else if(storage_spec.is_extern())
        {
          cpp_typecheck.err_location(storage_spec);
          throw "external storage not permitted here";
        }
      }
    }
  }

  if(symbol.is_static_lifetime)
    cpp_typecheck.dynamic_initializations.push_back(symbol.name);

  // move early, it must be visible before doing any value
  symbolt *new_symbol;

  if(cpp_typecheck.context.move(symbol, new_symbol))
    throw "cpp_typecheckt::convert_declarator: context.move() failed";

  if(!is_code)
  {
    cpp_scopest::id_sett id_set;
  
    cpp_typecheck.cpp_scopes.current_scope().lookup(
      base_name, cpp_scopet::SCOPE_ONLY, id_set);
     
    for(cpp_scopest::id_sett::const_iterator
        id_it=id_set.begin();
        id_it!=id_set.end();
        id_it++)
    {
      const cpp_idt &id=**id_it;
      // the name is already in the scope
      // this is ok if they belong to different categories

      if(!id.is_class() && !id.is_enum())
      {
        cpp_typecheck.err_location(new_symbol->location);
        cpp_typecheck.str << "`" << base_name << "' already in scope";
        throw 0;
      }
    }
  }

  // put into scope
  cpp_idt &identifier=
    cpp_typecheck.cpp_scopes.put_into_scope(*new_symbol, *scope, is_friend);

  if(is_template)
    identifier.id_class=cpp_idt::TEMPLATE;
  else if(is_template_argument)
    identifier.id_class=cpp_idt::TEMPLATE_ARGUMENT;
  else if(is_typedef)
    identifier.id_class=cpp_idt::TYPEDEF;
  else
    identifier.id_class=cpp_idt::SYMBOL;

  // do the value
  if(!new_symbol->is_type)
  {
    if(is_code && declarator.type().id()!=ID_template)
      cpp_typecheck.add_function_body(new_symbol);

    if(!is_code)
      cpp_typecheck.convert_initializer(*new_symbol);
  }

  enforce_rules(*new_symbol);

  return *new_symbol;
}

/*******************************************************************\

Function: cpp_declarator_convertert::get_pretty_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt cpp_declarator_convertert::get_pretty_name()
{
  if(is_code)
  {
    const irept::subt &arguments=
      final_type.find(ID_arguments).get_sub();

    std::string result=scope->prefix+id2string(base_name)+"(";

    forall_irep(it, arguments)
    {
      const typet &argument_type=((exprt &)*it).type();

      if(it!=arguments.begin())
        result+=", ";

      result+=cpp_typecheck.to_string(argument_type);
    }

    result+=")";

    return result;
  }

  return scope->prefix+id2string(base_name);
}

/*******************************************************************\

Function: cpp_declarator_convertert::operator_overloading_rules

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_declarator_convertert::operator_overloading_rules(
  const symbolt &symbol)
{

}

/*******************************************************************\

Function: cpp_declarator_convertert::main_function_rules

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_declarator_convertert::main_function_rules(
  const symbolt &symbol)
{
  if(symbol.name=="c::main")
  {
    if(symbol.type.id()!=ID_code)
    {
      cpp_typecheck.err_location(symbol.location);
      throw "main must be function";
    }

    const typet &return_type=
      to_code_type(symbol.type).return_type();

    if(return_type!=signed_int_type())
    {
      // Too many embedded compilers ignore this rule.
      //
      //cpp_typecheck.err_location(symbol.location);
      //throw "main must return int";
    }
  }
}
