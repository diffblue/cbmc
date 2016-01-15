/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <algorithm>

#include <util/i2string.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/simplify_expr.h>

#include <ansi-c/c_qualifiers.h>

#include "cpp_type2name.h"
#include "cpp_declarator_converter.h"
#include "cpp_typecheck.h"
#include "cpp_convert_type.h"
#include "cpp_name.h"

/*******************************************************************\

Function: cpp_typecheckt::has_const

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool cpp_typecheckt::has_const(const typet &type)
{
  if(type.id()==ID_const)
    return true;
  else if(type.id()==ID_merged_type)
  {
    forall_subtypes(it, type)
      if(has_const(*it)) return true;
      
    return false;
  }
  else
    return false;
}

/*******************************************************************\

Function: cpp_typecheckt::has_volatile

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool cpp_typecheckt::has_volatile(const typet &type)
{
  if(type.id()==ID_volatile)
    return true;
  else if(type.id()==ID_merged_type)
  {
    forall_subtypes(it, type)
      if(has_volatile(*it)) return true;
      
    return false;
  }
  else
    return false;
}

/*******************************************************************\

Function: cpp_typecheckt::tag_scope

Inputs:

Outputs:

Purpose:

\*******************************************************************/

cpp_scopet &cpp_typecheckt::tag_scope(
  const irep_idt &base_name,
  bool has_body,
  bool tag_only_declaration)
{
  // The scope of a compound identifier is difficult,
  // and is different from C.
  //
  // For instance:
  // class A { class B {} }   --> A::B
  // class A { class B; }     --> A::B
  // class A { class B *p; }  --> ::B
  // class B { }; class A { class B *p; } --> ::B
  // class B { }; class A { class B; class B *p; } --> A::B

  // If there is a body, or it's a tag-only declaration,
  // it's always in the current scope, even if we already have
  // it in an upwards scope.

  if(has_body || tag_only_declaration)
    return cpp_scopes.current_scope();
    
  // No body. Not a tag-only-declaration.
  // Check if we have it already. If so, take it.

  // we should only look for tags, but we don't
  cpp_scopet::id_sett id_set;
  cpp_scopes.current_scope().lookup(base_name, cpp_scopet::RECURSIVE, id_set);

  for(cpp_scopet::id_sett::const_iterator it=id_set.begin();
      it!=id_set.end();
      it++)
    if((*it)->is_class())
      return static_cast<cpp_scopet &>((*it)->get_parent());
    
  // Tags without body that we don't have already
  // and that are not a tag-only declaration go into
  // the global scope of the namespace.
  return cpp_scopes.get_global_scope();
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_compound_type

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_compound_type(
  struct_union_typet &type)
{
  // first save qualifiers
  c_qualifierst qualifiers(type);

  // now clear them from the type
  type.remove(ID_C_constant);
  type.remove(ID_C_volatile);
  type.remove(ID_C_restricted);

  // get the tag name
  bool has_tag=type.find(ID_tag).is_not_nil();
  irep_idt base_name;
  cpp_scopet *dest_scope=NULL;
  bool has_body=type.find(ID_body).is_not_nil();
  bool tag_only_declaration=type.get_bool(ID_C_tag_only_declaration);

  if(!has_tag)
  {
    // most of these should be named by now; see
    // cpp_declarationt::name_anon_struct_union()

    base_name=std::string("#anon_")+i2string(++anon_counter);
    type.set(ID_C_is_anonymous, true);
    dest_scope=&cpp_scopes.current_scope();
  }
  else
  {
    const cpp_namet &cpp_name=
      to_cpp_name(type.find(ID_tag));

    // scope given?
    if(cpp_name.is_simple_name())
    {
      base_name=cpp_name.get_base_name();
     
      // anonymous structs always go into the current scope
      if(type.get_bool(ID_C_is_anonymous))
        dest_scope=&cpp_scopes.current_scope();
      else
        dest_scope=&tag_scope(base_name, has_body, tag_only_declaration);
    }
    else
    {
      cpp_save_scopet cpp_save_scope(cpp_scopes);
      cpp_typecheck_resolvet cpp_typecheck_resolve(*this);
      cpp_template_args_non_tct t_args;
      dest_scope=&cpp_typecheck_resolve.resolve_scope(cpp_name, base_name, t_args);
    }
  }
  
  // The identifier 'tag-X' matches what the C front-end does!
  // The hypen is deliberate to avoid collisions with other
  // identifiers.
  const irep_idt symbol_name=
    dest_scope->prefix+
    "tag-"+id2string(base_name)+
    dest_scope->suffix;
    
  // check if we have it already

  symbol_tablet::symbolst::iterator previous_symbol=
    symbol_table.symbols.find(symbol_name);

  if(previous_symbol!=symbol_table.symbols.end())
  {
    // we do!
    
    symbolt &symbol=previous_symbol->second;

    if(has_body)
    {
      if(symbol.type.id()=="incomplete_"+type.id_string())
      {
        // a previously incomplete struct/union becomes complete
        symbol.type.swap(type);
        typecheck_compound_body(symbol);
      }
      else if(symbol.type.get_bool(ID_C_is_anonymous))
      {
        // we silently ignore
      }
      else
      {
        err_location(type);
        str << "error: compound tag `" << base_name
            << "' declared previously" << std::endl;
        str << "location of previous definition: "
            << symbol.location;
        throw 0;
      }
    }
  }
  else
  {
    // produce new symbol
    symbolt symbol;

    symbol.name=symbol_name;
    symbol.base_name=base_name;
    symbol.value.make_nil();
    symbol.location=type.source_location();
    symbol.mode=ID_cpp;
    symbol.module=module;
    symbol.type.swap(type);
    symbol.is_type=true;
    symbol.is_macro=false;
    symbol.pretty_name=
      cpp_scopes.current_scope().prefix+
      id2string(symbol.base_name)+
      cpp_scopes.current_scope().suffix;
    symbol.type.set(ID_tag, cpp_scopes.current_scope().prefix+id2string(symbol.base_name));

    // move early, must be visible before doing body
    symbolt *new_symbol;
 
    if(symbol_table.move(symbol, new_symbol))
      throw "cpp_typecheckt::typecheck_compound_type: symbol_table.move() failed";

    // put into dest_scope
    cpp_idt &id=cpp_scopes.put_into_scope(*new_symbol, *dest_scope);

    id.id_class=cpp_idt::CLASS;
    id.is_scope=true;
    id.prefix=cpp_scopes.current_scope().prefix+
              id2string(new_symbol->base_name)+
              cpp_scopes.current_scope().suffix+"::";
    id.class_identifier=new_symbol->name;
    id.id_class=cpp_idt::CLASS;
    
    if(has_body)
      typecheck_compound_body(*new_symbol);
    else
    {
      typet new_type("incomplete_"+new_symbol->type.id_string());
      new_type.set(ID_tag, new_symbol->base_name);
      new_symbol->type.swap(new_type);
    }
  }

  // create type symbol
  typet symbol_type(ID_symbol);
  symbol_type.set(ID_identifier, symbol_name);
  qualifiers.write(symbol_type);
  type.swap(symbol_type);
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_compound_declarator

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_compound_declarator(
  const symbolt &symbol,
  const cpp_declarationt &declaration,
  cpp_declaratort &declarator,
  struct_typet::componentst &components,
  const irep_idt &access,
  bool is_static,
  bool is_typedef,
  bool is_mutable)
{
  bool is_cast_operator=
    declaration.type().id()=="cpp-cast-operator";

  if(is_cast_operator)
  {
    assert(declarator.name().get_sub().size()==2 &&
           declarator.name().get_sub().front().id()==ID_operator);

    typet type=static_cast<typet &>(declarator.name().get_sub()[1]);
    declarator.type().subtype()=type;

    irept name(ID_name);
    name.set(ID_identifier, "("+cpp_type2name(type)+")");
    declarator.name().get_sub().back().swap(name);
  }

  typet final_type=
    declarator.merge_type(declaration.type());

  // this triggers template elaboration
  elaborate_class_template(final_type);

  typecheck_type(final_type);
  
  cpp_namet cpp_name;
  cpp_name.swap(declarator.name());
  
  irep_idt base_name;
  
  if(cpp_name.is_nil())
  {
    // Yes, there can be members without name.
    base_name=irep_idt();
  }
  else if(cpp_name.is_simple_name())
  {
    base_name=cpp_name.get_base_name();
  }
  else
  {
    err_location(cpp_name.source_location());
    str << "declarator in compound needs to be simple name";
    throw 0;
  }

  bool is_method=!is_typedef && final_type.id()==ID_code;
  bool is_constructor=declaration.is_constructor();
  bool is_destructor=declaration.is_destructor();
  bool is_virtual=declaration.member_spec().is_virtual();
  bool is_explicit=declaration.member_spec().is_explicit();
  bool is_inline=declaration.member_spec().is_inline();

  final_type.set(ID_C_member_name, symbol.name);

  // first do some sanity checks

  if(is_virtual && !is_method)
  {
    err_location(cpp_name.source_location());
    str << "only methods can be virtual";
    throw 0;
  }

  if(is_inline && !is_method)
  {
    err_location(cpp_name.source_location());
    str << "only methods can be inlined";
    throw 0;
  }

  if(is_virtual && is_static)
  {
    err_location(cpp_name.source_location());
    str << "static methods cannot be virtual";
    throw 0;
  }

  if(is_cast_operator && is_static)
  {
    err_location(cpp_name.source_location());
    str << "cast operators cannot be static`";
    throw 0;
  }

  if(is_constructor && is_virtual)
  {
    err_location(cpp_name.source_location());
    str << "constructors cannot be virtual";
    throw 0;
  }

  if(!is_constructor && is_explicit)
  {
    err_location(cpp_name.source_location());
    str << "only constructors can be explicit";
    throw 0;
  }

  if(is_constructor &&
     base_name!=id2string(symbol.base_name))
  {
    err_location(cpp_name.source_location());
    str << "member function must return a value or void";
    throw 0;
  }

  if(is_destructor &&
     base_name!="~"+id2string(symbol.base_name))
  {
    err_location(cpp_name.source_location());
    str << "destructor with wrong name";
    throw 0;
  }

  // now do actual work

  struct_typet::componentt component;
  irep_idt identifier;
  
  // the below is a temporary hack
  //if(is_method || is_static)d
  if(id2string(cpp_scopes.current_scope().prefix).find("#anon")==
     std::string::npos ||
     is_method || is_static)
  {
    // Identifiers for methods include the scope prefix.
    // Identifiers for static members include the scope prefix.
    identifier=
      cpp_scopes.current_scope().prefix+
      id2string(base_name);
  }
  else
  {
    // otherwise, we keep them simple
    identifier=base_name;
  }
  
  component.set(ID_name, identifier);
  component.type()=final_type;
  component.set(ID_access, access);
  component.set(ID_base_name, base_name);
  component.set(ID_pretty_name, base_name);
  component.add_source_location()=cpp_name.source_location();

  if(cpp_name.is_operator())
  {
    component.set("is_operator", true);
    component.type().set("#is_operator", true);
  }

  if(is_cast_operator)
    component.set("is_cast_operator", true);

  if(declaration.member_spec().is_explicit())
    component.set("is_explicit", true);

  // either blank, const, volatile, or const volatile
  const typet &method_qualifier=
    static_cast<const typet &>(declarator.add(ID_method_qualifier));

  if(is_static)
  {
    component.set(ID_is_static, true);
    component.type().set("#is_static", true);
  }

  if(is_typedef)
    component.set("is_type", true);

  if(is_mutable)
    component.set("is_mutable", true);

  exprt &value=declarator.value();
  irept &initializers=declarator.member_initializers();

  if(is_method)
  {
    component.set(ID_is_inline, declaration.member_spec().is_inline());

    // the 'virtual' name of the function
    std::string virtual_name=
    component.get_string(ID_base_name)+
      id2string(
        function_identifier(static_cast<const typet &>(component.find(ID_type))));
        
    if(has_const(method_qualifier))
      virtual_name+="$const";

    if(has_volatile(method_qualifier))
      virtual_name+="$virtual";
      
    if(component.type().get(ID_return_type) == ID_destructor)
      virtual_name= "@dtor";
    
    // The method may be virtual implicitly.
    std::set<irep_idt> virtual_bases;

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it->get_bool("is_virtual"))
      {
        if(it->get("virtual_name")==virtual_name)
        {
          is_virtual=true;
          const code_typet& code_type = to_code_type(it->type());
          assert(code_type.parameters().size()>0);
          const typet& pointer_type = code_type.parameters()[0].type();
          assert(pointer_type.id() == ID_pointer);
          virtual_bases.insert(pointer_type.subtype().get(ID_identifier));
        }
      }
    }

    if(!is_virtual)
    {
      typecheck_member_function(
        symbol.name, component, initializers,
        method_qualifier, value);

      if(!value.is_nil() && !is_static)
      {
        err_location(cpp_name.source_location());
        str << "no initialization allowed here";
        throw 0;
      }
    }
    else // virtual
    {
      component.type().set(ID_C_is_virtual, true);
      component.type().set("#virtual_name",virtual_name);

      // Check if it is a pure virtual method
      if(is_virtual)
      {
        if(value.is_not_nil() && value.id() == ID_constant)
        {
          mp_integer i;
          to_integer(value, i);
          if(i!=0)
          {
            err_location(declarator.name().source_location());
            str << "expected 0 to mark pure virtual method, got " << i;
          }
          component.set("is_pure_virtual", true);
          value.make_nil();
        }
      }

      typecheck_member_function(
        symbol.name,
        component,
        initializers,
        method_qualifier,
        value);

      // get the virtual-table symbol type
      irep_idt vt_name = "virtual_table::"+id2string(symbol.name);

      symbol_tablet::symbolst::iterator vtit =
        symbol_table.symbols.find(vt_name);

      if(vtit == symbol_table.symbols.end())
      {
        // first time: create a virtual-table symbol type 
        symbolt vt_symb_type;
        vt_symb_type.name= vt_name;
        vt_symb_type.base_name="virtual_table::"+id2string(symbol.base_name);
        vt_symb_type.pretty_name = vt_symb_type.base_name;
        vt_symb_type.mode=ID_cpp;
        vt_symb_type.module=module;
        vt_symb_type.location=symbol.location;
        vt_symb_type.type = struct_typet();
        vt_symb_type.type.set(ID_name, vt_symb_type.name);
        vt_symb_type.is_type = true;

        bool failed = symbol_table.move(vt_symb_type);
        assert(!failed);
        vtit = symbol_table.symbols.find(vt_name);

        // add a virtual-table pointer 
        struct_typet::componentt compo;
        compo.type() = pointer_typet(symbol_typet(vt_name));
        compo.set_name(id2string(symbol.name) +"::@vtable_pointer");
        compo.set(ID_base_name, "@vtable_pointer");
        compo.set(ID_pretty_name, id2string(symbol.base_name) +"@vtable_pointer");
        compo.set("is_vtptr", true);
        compo.set(ID_access, ID_public);
        components.push_back(compo);
        put_compound_into_scope(compo);
      }
      
      assert(vtit->second.type.id()==ID_struct);

      struct_typet &virtual_table=
        to_struct_type(vtit->second.type);

      component.set("virtual_name", virtual_name);
      component.set("is_virtual", is_virtual);

      // add an entry to the virtual table
      struct_typet::componentt vt_entry;
      vt_entry.type() = pointer_typet(component.type());
      vt_entry.set_name(id2string(vtit->first)+"::"+virtual_name);
      vt_entry.set(ID_base_name, virtual_name);
      vt_entry.set(ID_pretty_name, virtual_name);
      vt_entry.set(ID_access, ID_public);
      vt_entry.add_source_location() = symbol.location;
      virtual_table.components().push_back(vt_entry);

      // take care of overloading
      while(!virtual_bases.empty())
      {
        irep_idt virtual_base = *virtual_bases.begin();

        // a new function that does 'late casting' of the 'this' parameter
        symbolt func_symb;
        func_symb.name=id2string(component.get_name()) + "::" +id2string(virtual_base);
        func_symb.base_name=component.get(ID_base_name);
        func_symb.pretty_name = component.get(ID_base_name);
        func_symb.mode=ID_cpp;
        func_symb.module=module;
        func_symb.location=component.source_location();
        func_symb.type=component.type();

        // change the type of the 'this' pointer
        code_typet& code_type = to_code_type(func_symb.type);
        code_typet::parametert& arg= code_type.parameters().front();
        arg.type().subtype().set(ID_identifier, virtual_base);

        // create symbols for the parameters
        code_typet::parameterst& args =  code_type.parameters();
        for(unsigned i=0; i<args.size(); i++)
        {
          code_typet::parametert& arg = args[i];
          irep_idt base_name = arg.get_base_name();

          if(base_name==irep_idt())
            base_name="arg"+i2string(i);

          symbolt arg_symb;
          arg_symb.name = id2string(func_symb.name) + "::"+ id2string(base_name);
          arg_symb.base_name = base_name;
          arg_symb.pretty_name = base_name;
          arg_symb.mode=ID_cpp;
          arg_symb.location=func_symb.location;
          arg_symb.type = arg.type();

          arg.set(ID_C_identifier, arg_symb.name);

          // add the parameter to the symbol table
          bool failed = symbol_table.move(arg_symb);
          assert(!failed);
        }

        // do the body of the function
        typecast_exprt late_cast(to_code_type(component.type()).parameters()[0].type());

        late_cast.op0()=
          namespacet(symbol_table).lookup(
            args[0].get(ID_C_identifier)).symbol_expr();
        
        if(code_type.return_type().id()!=ID_empty &&
           code_type.return_type().id()!=ID_destructor)
        {
          side_effect_expr_function_callt expr_call;
          expr_call.function() = symbol_exprt(component.get_name(),component.type());
          expr_call.type() = to_code_type(component.type()).return_type();
          expr_call.arguments().reserve(args.size());
          expr_call.arguments().push_back(late_cast);

          for(unsigned i=1; i < args.size(); i++)
          {
            expr_call.arguments().push_back(
              namespacet(symbol_table).lookup(args[i].get(ID_C_identifier)).symbol_expr());
          }

          code_returnt code_return;
          code_return.return_value() = expr_call;

          func_symb.value = code_return;
        }
        else
        {
          code_function_callt code_func;
          code_func.function() = symbol_exprt(component.get_name(),component.type());
          code_func.arguments().reserve(args.size());
          code_func.arguments().push_back(late_cast);

          for(unsigned i=1; i < args.size(); i++)
          {
            code_func.arguments().push_back(
              namespacet(symbol_table).lookup(
                args[i].get(ID_C_identifier)).symbol_expr());
          }

          func_symb.value = code_func;
        }

        // add this new function to the list of components
        
        struct_typet::componentt new_compo = component;
        new_compo.type() = func_symb.type;
        new_compo.set_name(func_symb.name);
        components.push_back(new_compo);

        // add the function to the symbol table
        {
          bool failed = symbol_table.move(func_symb);
          assert(!failed);
        }

        // next base
        virtual_bases.erase(virtual_bases.begin());
      }
    }
  }
  
  if(is_static && !is_method) // static non-method member
  {
    // add as global variable to symbol_table
    symbolt static_symbol;
    static_symbol.mode=symbol.mode;
    static_symbol.name=identifier;
    static_symbol.type=component.type();
    static_symbol.base_name=component.get(ID_base_name);
    static_symbol.is_lvalue=true;
    static_symbol.is_static_lifetime=true;
    static_symbol.location=cpp_name.source_location();
    static_symbol.is_extern=true;
    
    // TODO: not sure about this: should be defined separately!
    dynamic_initializations.push_back(static_symbol.name);

    symbolt *new_symbol;
    if(symbol_table.move(static_symbol, new_symbol))
    {
      err_location(cpp_name.source_location());
        str << "redeclaration of static member `" 
            << static_symbol.base_name
            << "'";
      throw 0;
    }

    if(value.is_not_nil())
    {
      if(cpp_is_pod(new_symbol->type))
      {
        new_symbol->value.swap(value);
        c_typecheck_baset::do_initializer(*new_symbol);

        // these are macros if they are PODs and come with a (constant) value
        if(new_symbol->type.get_bool(ID_C_constant))
        {
          simplify(new_symbol->value, *this);
          new_symbol->is_macro=true;
        }
      }
      else
      {
        symbol_exprt symexpr;
        symexpr.set_identifier(new_symbol->name);

        exprt::operandst ops;
        ops.push_back(value);
        codet defcode =
          cpp_constructor(source_locationt(), symexpr, ops);

        new_symbol->value.swap(defcode);
      }
    }
  }

  // array members must have fixed size
  check_fixed_size_array(component.type());

  put_compound_into_scope(component);

  components.push_back(component);
}

/*******************************************************************\

Function: cpp_typecheckt::check_fixed_size_array

Inputs:

Outputs:

Purpose: check that an array has fixed size

\*******************************************************************/

void cpp_typecheckt::check_fixed_size_array(typet &type)
{
  if(type.id()==ID_array)
  {
    array_typet &array_type=to_array_type(type);
    
    if(array_type.size().is_not_nil())
      make_constant_index(array_type.size());

    // recursive call for multi-dimensional arrays
    check_fixed_size_array(array_type.subtype());
  }
}

/*******************************************************************\

Function: cpp_typecheckt::put_compound_into_scope

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void cpp_typecheckt::put_compound_into_scope(
  const struct_union_typet::componentt &compound)
{
  const irep_idt &base_name=compound.get_base_name();
  const irep_idt &name=compound.get_name();
  
  // nothing to do if no base_name (e.g., an anonymous bitfield)
  if(base_name==irep_idt())
    return;
  
  if(compound.type().id()==ID_code)
  {
    // put the symbol into scope
    cpp_idt &id=cpp_scopes.current_scope().insert(base_name);
    id.id_class=compound.get_bool("is_type")?cpp_idt::TYPEDEF:cpp_idt::SYMBOL;
    id.identifier=name;
    id.class_identifier=cpp_scopes.current_scope().identifier;
    id.is_member = true;
    id.is_constructor =
      compound.find(ID_type).get(ID_return_type) == ID_constructor;
    id.is_method = true;
    id.is_static_member=compound.get_bool(ID_is_static);

    // create function block-scope in the scope
    cpp_idt &id_block=
      cpp_scopes.current_scope().insert(
        irep_idt(std::string("$block:") + base_name.c_str()));

    id_block.id_class=cpp_idt::BLOCK_SCOPE;
    id_block.identifier=name;
    id_block.class_identifier=cpp_scopes.current_scope().identifier;
    id_block.is_method=true;
    id_block.is_static_member=compound.get_bool(ID_is_static);

    id_block.is_scope=true;
    id_block.prefix=compound.get_string("prefix");
    cpp_scopes.id_map[id.identifier]=&id_block;
  }
  else
  {
    // check if it's already there
    cpp_scopest::id_sett id_set;
    
    cpp_scopes.current_scope().lookup(base_name, cpp_scopet::SCOPE_ONLY, id_set);
    
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
        err_location(compound);
        str << "`" << base_name
            << "' already in compound scope";
        throw 0;
      }
    }

    // put into the scope
    cpp_idt &id=cpp_scopes.current_scope().insert(base_name);
    id.id_class=compound.get_bool(ID_is_type)?cpp_idt::TYPEDEF:cpp_idt::SYMBOL;
    id.identifier=name;
    id.class_identifier=cpp_scopes.current_scope().identifier;
    id.is_member=true;
    id.is_method=false;
    id.is_static_member=compound.get_bool(ID_is_static);
  }
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_friend_declaration

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_friend_declaration(
  symbolt &symbol,
  cpp_declarationt &declaration)
{
  // A friend of a class can be a function/method,
  // or a struct/class/union type.

  if(declaration.is_template())
  {
    return; // TODO
    err_location(declaration.type());
    str << "friend template not supported";
    throw 0;
  }
  
  // we distinguish these whether there is a declarator
  if(declaration.declarators().empty())
  {
    typet &ftype=declaration.type();

    // must be struct or union
    if(ftype.id()!=ID_struct && ftype.id()!=ID_union)
    {
      err_location(declaration.type());
      str << "unexpected friend";
      throw 0;
    }
       
    if(ftype.find(ID_body).is_not_nil())
    {
      err_location(declaration.type());
      str << "friend declaration must not have compound body";
      throw 0;
    }

    // typecheck ftype
    
    // TODO
//    typecheck_type(ftype);
//    assert(ftype.id()==ID_symbol);
//    symbol.type.add("#friends").move_to_sub(ftype);

    return;
  }

  // It should be a friend function.
  // Do the declarators.
  
  Forall_cpp_declarators(sub_it, declaration)
  {
    bool has_value = sub_it->value().is_not_nil();

    if(!has_value)
    {
      // If no value is found, then we jump to the
      // global scope, and we convert the declarator
      // as if it were declared there
      cpp_save_scopet saved_scope(cpp_scopes);
      cpp_scopes.go_to_global_scope();
      cpp_declarator_convertert cpp_declarator_converter(*this);
      const symbolt &conv_symb = cpp_declarator_converter.convert(
          declaration.type(), declaration.storage_spec(),
          declaration.member_spec(), *sub_it);
      exprt symb_expr = cpp_symbol_expr(conv_symb);
      symbol.type.add("#friends").move_to_sub(symb_expr);
    }
    else
    {
      cpp_declarator_convertert cpp_declarator_converter(*this);
      cpp_declarator_converter.is_friend = true;

      declaration.member_spec().set_inline(true);

      const symbolt &conv_symb = cpp_declarator_converter.convert(
        declaration.type(), declaration.storage_spec(),
        declaration.member_spec(), *sub_it);

      exprt symb_expr = cpp_symbol_expr(conv_symb);

      symbol.type.add("#friends").move_to_sub(symb_expr);
    }
  }
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_compound_body

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_compound_body(symbolt &symbol)
{
  cpp_save_scopet saved_scope(cpp_scopes);

  // enter scope of compound
  cpp_scopes.set_scope(symbol.name);

  assert(symbol.type.id()==ID_struct ||
         symbol.type.id()==ID_union);

  struct_union_typet &type=
    to_struct_union_type(symbol.type);

  // pull the base types in
  if(!type.find(ID_bases).get_sub().empty())
  {
    if(type.id()==ID_union)
    {
      err_location(symbol.location);
      throw "union types must not have bases";
    }
    
    typecheck_compound_bases(to_struct_type(type));
  }

  exprt &body=static_cast<exprt &>(type.add(ID_body));
  struct_union_typet::componentst &components=type.components();

  symbol.type.set(ID_name, symbol.name);

  // default access
  irep_idt access=
    type.get_bool(ID_C_class)?ID_private:ID_public;

  bool found_ctor=false;
  bool found_dtor=false;

  // we first do everything _but_ the constructors

  Forall_operands(it, body)
  {
    if(it->id()==ID_cpp_declaration)
    {
      cpp_declarationt &declaration=
        to_cpp_declaration(*it);

      if(declaration.member_spec().is_friend())
      {
        typecheck_friend_declaration(symbol, declaration);
        continue; // done
      }

      if(declaration.is_template())
      {
        // remember access mode
        declaration.set(ID_C_access, access);
        convert_template_declaration(declaration);
        continue;
      }

      if(declaration.type().id()==irep_idt()) // empty?
        continue;

      bool is_typedef=declaration.is_typedef();

      // is it tag-only?
      if(declaration.type().id()==ID_struct ||
         declaration.type().id()==ID_union ||
         declaration.type().id()==ID_c_enum)
        if(declaration.declarators().empty())
          declaration.type().set(ID_C_tag_only_declaration, true);

      declaration.name_anon_struct_union();
      typecheck_type(declaration.type());

      bool is_static=declaration.storage_spec().is_static();
      bool is_mutable=declaration.storage_spec().is_mutable();

      if(declaration.storage_spec().is_extern() ||
         declaration.storage_spec().is_auto() ||
         declaration.storage_spec().is_register())
      {
        err_location(declaration.storage_spec());
        str << "invalid storage class specified for field";
        throw 0;
      }

      typet final_type=follow(declaration.type());

      // anonymous member?
      if(declaration.declarators().empty() &&
         final_type.get_bool(ID_C_is_anonymous))
      {
        // we only allow this on struct/union types
        if(final_type.id()!=ID_union &&
           final_type.id()!=ID_struct)
        {
          err_location(declaration.type());
          throw "member declaration does not declare anything";
        }

        convert_anon_struct_union_member(
          declaration, access, components);

        continue;
      }

      // declarators
      Forall_cpp_declarators(d_it, declaration)
      {
        cpp_declaratort &declarator=*d_it;

        // Skip the constructors until all the data members
        // are discovered
        if(declaration.is_destructor())
          found_dtor=true;

        if(declaration.is_constructor())
        {
          found_ctor=true;
          continue;
        }

        typecheck_compound_declarator(
          symbol,
          declaration, declarator, components,
          access, is_static, is_typedef, is_mutable);
      }
    }
    else if(it->id()=="cpp-public")
      access=ID_public;
    else if(it->id()=="cpp-private")
      access=ID_private;
    else if(it->id()=="cpp-protected")
      access=ID_protected;
    else
    {
    }
  }

  // Add the default dtor, if needed
  // (we have to do the destructor before building the virtual tables,
  //  as the destructor may be virtual!)

  if((found_ctor || !cpp_is_pod(symbol.type)) && !found_dtor)
  {
    // build declaration
    cpp_declarationt dtor;
    default_dtor(symbol, dtor);

    typecheck_compound_declarator(
      symbol,
      dtor, dtor.declarators()[0], components,
      ID_public, false, false, false);
  }

  // setup virtual tables before doing the constructors
  if(symbol.type.id()==ID_struct)
    do_virtual_table(symbol);

  if(!found_ctor && !cpp_is_pod(symbol.type))
  {
    // it's public!
    exprt cpp_public("cpp-public");
    body.move_to_operands(cpp_public);

    // build declaration
    cpp_declarationt ctor;
    default_ctor(symbol.type.source_location(), symbol.base_name, ctor);
    body.move_to_operands(ctor);
  }

  // Reset the access type
  access=
    type.get_bool(ID_C_class)?ID_private:ID_public;

  // All the data members are now known.
  // We now deal with the constructors that we are given.
  Forall_operands(it, body)
  {
    if(it->id()==ID_cpp_declaration)
    {
      cpp_declarationt &declaration=
        to_cpp_declaration(*it);

      if(!declaration.is_constructor())
        continue;
      
      Forall_cpp_declarators(d_it, declaration)
      {
        cpp_declaratort &declarator=*d_it;

        #if 0
        irep_idt ctor_base_name=
          declarator.name().get_base_name();
        #endif
        
        if(declarator.value().is_not_nil()) // body?
        {
          if(declarator.find(ID_member_initializers).is_nil())
            declarator.set(ID_member_initializers, ID_member_initializers);

          check_member_initializers(
            type.add(ID_bases),
            type.components(),
            declarator.member_initializers()
            );

          full_member_initialization(
            type,
            declarator.member_initializers()
            );
        }

        // Finally, we typecheck the constructor with the
        // full member-initialization list
        bool is_static=declaration.storage_spec().is_static();    // Shall be false
        bool is_mutable=declaration.storage_spec().is_mutable();  // Shall be false
        bool is_typedef=declaration.is_typedef();                 // Shall be false
        
        typecheck_compound_declarator(
          symbol,
          declaration, declarator, components,
          access, is_static, is_typedef, is_mutable);
      }
    }
    else if(it->id()=="cpp-public")
      access=ID_public;
    else if(it->id()=="cpp-private")
      access=ID_private;
    else if(it->id()=="cpp-protected")
      access=ID_protected;
    else
    {
    }
  }

  if(!cpp_is_pod(symbol.type))
  {
    // Add the default copy constructor
    struct_typet::componentt component;

    if(!find_cpctor(symbol))
    {      
      // build declaration
      cpp_declarationt cpctor;
      default_cpctor(symbol, cpctor);
      assert(cpctor.declarators().size()==1);

      exprt value("cpp_not_typechecked");
      value.copy_to_operands(cpctor.declarators()[0].value());
      cpctor.declarators()[0].value() = value;

      typecheck_compound_declarator(
        symbol,
        cpctor, cpctor.declarators()[0], components,
        ID_public, false, false, false);      
    }

    // Add the default assignment operator
    if(!find_assignop(symbol))
    {
      // build declaration
      cpp_declarationt assignop;
      default_assignop(symbol, assignop);
      assert(assignop.declarators().size()==1);

      // The value will be typechecked only if the operator
      // is actually used
      cpp_declaratort declarator;
      assignop.declarators().push_back(declarator);
      assignop.declarators()[0].value() = exprt("cpp_not_typechecked");

      typecheck_compound_declarator(
        symbol,
        assignop, assignop.declarators()[0], components,
        ID_public, false, false, false);
    }
  }

  // clean up!
  symbol.type.remove(ID_body);
}

/*******************************************************************\

Function: cpp_typecheckt::move_member_initializers

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void cpp_typecheckt::move_member_initializers(
  irept &initializers,
  const typet &type,
  exprt &value)
{
  bool is_constructor=
    type.find(ID_return_type).id()==ID_constructor;

  // see if we have initializers
  if(!initializers.get_sub().empty())
  {
    if(!is_constructor)
    {
      err_location(initializers);
      str << "only constructors are allowed to "
             "have member initializers";
      throw 0;
    }

    if(value.is_nil())
    {
      err_location(initializers);
      str << "only constructors with body are allowed to "
             "have member initializers";
      throw 0;
    }

    to_code(value).make_block();

    exprt::operandst::iterator o_it=value.operands().begin();
    forall_irep(it, initializers.get_sub())
    {
      o_it=value.operands().insert(o_it, static_cast<const exprt &>(*it));
      o_it++;
    }
  }
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_member_function

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_member_function(
  const irep_idt &compound_identifier,
  struct_typet::componentt &component,
  irept &initializers,
  const typet &method_qualifier,
  exprt &value)
{
  symbolt symbol;

  typet &type=component.type();

  if(component.get_bool(ID_is_static))
  {
    if(method_qualifier.id()!=irep_idt())
    {
      err_location(component);
      throw "method is static -- no qualifiers allowed";
    }
  }
  else
  {
    adjust_method_type(
      compound_identifier,
      type,
      method_qualifier);
  }

  if(value.id()=="cpp_not_typechecked")
    move_member_initializers(initializers, type, value.op0());
  else
    move_member_initializers(initializers, type, value);

  irep_idt f_id=
    function_identifier(component.type());

  const irep_idt identifier=
    cpp_scopes.current_scope().prefix+
    id2string(component.get_base_name())+
    id2string(f_id);

  component.set_name(identifier);
  component.set("prefix", id2string(identifier)+"::");

  if(value.is_not_nil())
    type.set(ID_C_inlined, true);

  symbol.name=identifier;
  symbol.base_name=component.get_base_name();
  symbol.value.swap(value);
  symbol.mode=ID_cpp;
  symbol.module=module;
  symbol.type=type;
  symbol.is_type=false;
  symbol.is_macro=false;
  symbol.location=component.source_location();

  // move early, it must be visible before doing any value
  symbolt *new_symbol;

  if(symbol_table.move(symbol, new_symbol))
  {
    err_location(symbol.location);
    str << "failed to insert new method symbol: "
        << symbol.name << "\n";

    str << "name of previous symbol: "
        << new_symbol->name << "\n";
    str << "location of previous symbol: "
        << new_symbol->location;

    throw 0;
  }
  
  // Is this in a class template?
  // If so, we defer typechecking until used.
  if(cpp_scopes.current_scope().get_parent().is_template_scope())
  {
  }
  else // remember for later typechecking of body
    add_function_body(new_symbol);
}

/*******************************************************************\

Function: cpp_typecheckt::adjust_method_type

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void cpp_typecheckt::adjust_method_type(
  const irep_idt &compound_symbol,
  typet &type,
  const typet &method_qualifier)
{
  irept &parameters=type.add(ID_parameters);

  parameters.get_sub().insert(
    parameters.get_sub().begin(), irept(ID_parameter));

  exprt &parameter=static_cast<exprt &>(parameters.get_sub().front());
  parameter.type()=typet(ID_pointer);

  parameter.type().subtype()=typet(ID_symbol);
  parameter.type().subtype().set(ID_identifier, compound_symbol);

  parameter.set(ID_C_identifier, ID_this);
  parameter.set(ID_C_base_name, ID_this);

  if(has_const(method_qualifier))
    parameter.type().subtype().set(ID_C_constant, true);
  
  if(has_volatile(method_qualifier))
    parameter.type().subtype().set(ID_C_volatile, true);
}

/*******************************************************************\

Function: cpp_typecheckt::add_anonymous_members_to_scope

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void cpp_typecheckt::add_anonymous_members_to_scope(
  const symbolt &struct_union_symbol)
{
  const struct_union_typet &struct_union_type=
    to_struct_union_type(struct_union_symbol.type);

  const struct_union_typet::componentst &struct_union_components=
    struct_union_type.components();

  // do scoping -- the members of the struct/union
  // should be visible in the containing struct/union,
  // and that recursively!

  for(struct_union_typet::componentst::const_iterator
      it=struct_union_components.begin();
      it!=struct_union_components.end();
      it++)
  {
    if(it->type().id()==ID_code)
    {
      err_location(struct_union_symbol.type.source_location());
      str << "anonymous struct/union member `"
          << struct_union_symbol.base_name
          << "' shall not have function members";
      throw 0;
    }

    if(it->get_anonymous())
    {
      const symbolt &symbol=lookup(it->type().get(ID_identifier));
      // recrusive call
      add_anonymous_members_to_scope(symbol);
    }
    else
    {
      const irep_idt &base_name=it->get_base_name();

      if(cpp_scopes.current_scope().contains(base_name))
      {
        err_location(*it);
        str << "`" << base_name << "' already in scope";
        throw 0;
      }
      
      cpp_idt &id=cpp_scopes.current_scope().insert(base_name);
      id.id_class=cpp_idt::SYMBOL;
      id.identifier=it->get(ID_name);
      id.class_identifier=struct_union_symbol.name;
      id.is_member=true;
    }
  }
}

/*******************************************************************\

Function: cpp_typecheckt::convert_anon_struct_union_member

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void cpp_typecheckt::convert_anon_struct_union_member(
  const cpp_declarationt &declaration,
  const irep_idt &access,
  struct_typet::componentst &components)
{
  symbolt &struct_union_symbol=
    symbol_table.symbols[follow(declaration.type()).get(ID_name)];

  if(declaration.storage_spec().is_static() ||
     declaration.storage_spec().is_mutable())
  {
    err_location(struct_union_symbol.type.source_location());
    throw "storage class is not allowed here";
  }

  if(!cpp_is_pod(struct_union_symbol.type))
  {
    err_location(struct_union_symbol.type.source_location());
    str << "anonymous struct/union member is not POD";
    throw 0;
  }

  // produce an anonymous member
  irep_idt base_name="#anon_member"+i2string(components.size());

  irep_idt identifier=
    cpp_scopes.current_scope().prefix+
    base_name.c_str();

  typet symbol_type(ID_symbol);
  symbol_type.set(ID_identifier, struct_union_symbol.name);

  struct_typet::componentt component;
  component.set(ID_name, identifier);
  component.type()=symbol_type;
  component.set_access(access);
  component.set_base_name(base_name);
  component.set_pretty_name(base_name);
  component.set_anonymous(true);
  component.add_source_location()=declaration.source_location();

  components.push_back(component);
  
  add_anonymous_members_to_scope(struct_union_symbol);
    
  put_compound_into_scope(component);

  struct_union_symbol.type.set("#unnamed_object", base_name);
}

/*******************************************************************\

Function: cpp_typecheckt::get_component

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool cpp_typecheckt::get_component(
  const source_locationt &source_location,
  const exprt &object,
  const irep_idt &component_name,
  exprt &member)
{
  const typet &followed_type=follow(object.type());

  assert(followed_type.id()==ID_struct ||
         followed_type.id()==ID_union);

  struct_union_typet final_type=
    to_struct_union_type(followed_type);

  const struct_union_typet::componentst &components=
    final_type.components();

  for(struct_union_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    const struct_union_typet::componentt &component = *it;

    exprt tmp(ID_member, component.type());
    tmp.set(ID_component_name, component.get_name());
    tmp.add_source_location()=source_location;
    tmp.copy_to_operands(object);

    if(component.get_name()==component_name)
    {
      member.swap(tmp);

      bool not_ok=check_component_access(component, final_type);
      if(not_ok)
      {
        if(disable_access_control)
        {
          member.set("#not_accessible", true);
          member.set(ID_C_access, component.get(ID_access));
        }
        else
        {
          #if 0
          err_location(source_location);
          str << "error: member `" << component_name
              << "' is not accessible (" << component.get(ID_access) << ")";
          str << std::endl
              << "struct name: " << final_type.get(ID_name);
          throw 0;
          #endif
        }
      }

      if(object.get_bool(ID_C_lvalue))
        member.set(ID_C_lvalue, true);

      if(object.type().get_bool(ID_C_constant) &&
         !component.get_bool("is_mutable"))
        member.type().set(ID_C_constant, true);

      member.add_source_location() = source_location;

      return true; // component found
    }
    else if(
      follow(component.type()).find("#unnamed_object").is_not_nil())
    {
      // could be anonymous union or struct
      
      const typet &component_type=follow(component.type());
      
      if(component_type.id()==ID_union ||
         component_type.id()==ID_struct)
      {
        // recursive call!
        if(get_component(source_location, tmp, component_name, member))
        {
          if(check_component_access(component, final_type))
          {
            #if 0
            err_location(source_location);
            str << "error: member `" << component_name
                << "' is not accessible";
            throw 0;
            #endif
          }

          if(object.get_bool(ID_C_lvalue))
            member.set(ID_C_lvalue, true);

          if(object.get_bool(ID_C_constant) &&
             !component.get_bool("is_mutable"))
            member.type().set(ID_C_constant, true);

          member.add_source_location() = source_location;
          return true; // component found
        }
      }
    }
  }

  return false; // component not found
}

/*******************************************************************\

Function: cpp_typecheckt::check_component_access

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool cpp_typecheckt::check_component_access(
  const struct_union_typet::componentt &component,
  const struct_union_typet &struct_union_type)
{
  const irep_idt &access=component.get(ID_access);

  if(access=="noaccess")
    return true; // not ok

  if(access == ID_public)
    return false; // ok

  assert(access == ID_private ||
         access == ID_protected);

  const irep_idt &struct_identifier=
    struct_union_type.get(ID_name);

  cpp_scopet *pscope = &(cpp_scopes.current_scope());
  while(!(pscope->is_root_scope()))
  {
    if(pscope->is_class())
    {
      if(pscope->identifier == struct_identifier)
        return false; // ok

      const struct_typet &scope_struct=
        to_struct_type(lookup(pscope->identifier).type);

      if(subtype_typecast(
        to_struct_type(struct_union_type), scope_struct))
        return false; // ok

      else break;
    }
    pscope = &(pscope->get_parent());
  }

  // check friendship
  const irept::subt &friends=
    struct_union_type.find("#friends").get_sub();
  
  forall_irep(f_it, friends)
  {
    const irept &friend_symb = *f_it;

    const cpp_scopet &friend_scope =
      cpp_scopes.get_scope(friend_symb.get(ID_identifier));

    cpp_scopet *pscope = &(cpp_scopes.current_scope());

    while(!(pscope->is_root_scope()))
    {
      if(friend_scope.identifier == pscope->identifier)
        return false; // ok

      if(pscope->is_class())
        break;

      pscope = &(pscope->get_parent());
    }
  }

  return true; //not ok
}

/*******************************************************************\

Function: cpp_typecheckt::get_bases

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void cpp_typecheckt::get_bases(
  const struct_typet &type,
  std::set<irep_idt> &set_bases) const
{
  const irept::subt &bases=type.find(ID_bases).get_sub();

  forall_irep(it, bases)
  {
    assert(it->id()==ID_base);
    assert(it->get(ID_type) == ID_symbol);

    const struct_typet &base=
      to_struct_type(lookup(it->find(ID_type).get(ID_identifier)).type);

    set_bases.insert(base.get(ID_name));
    get_bases(base,set_bases);
  }
}

/*******************************************************************\

Function: cpp_typecheckt::get_virtual_bases

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void cpp_typecheckt::get_virtual_bases(
  const struct_typet& type,
  std::list<irep_idt> &vbases) const
{
  if(std::find(vbases.begin(), vbases.end(), type.get(ID_name)) != vbases.end())
    return;

  const irept::subt &bases=type.find(ID_bases).get_sub();

  forall_irep(it, bases)
  {
    assert(it->id()==ID_base);
    assert(it->get(ID_type) == ID_symbol);

    const struct_typet &base=
      to_struct_type(lookup(it->find(ID_type).get(ID_identifier)).type);

    if(it->get_bool(ID_virtual))
      vbases.push_back(base.get(ID_name));

    get_virtual_bases(base,vbases);
  }
}

/*******************************************************************\

Function: cpp_typecheckt::subtype_typecast

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool cpp_typecheckt::subtype_typecast(
  const struct_typet &from,
  const struct_typet &to) const
{
  if(from.get(ID_name)==to.get(ID_name))
    return true;

  std::set<irep_idt> bases;

  get_bases(from, bases);

  return bases.find(to.get(ID_name)) != bases.end();
}

/*******************************************************************\

Function: cpp_typecheckt::make_ptr_subtypecast

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void cpp_typecheckt::make_ptr_typecast(
  exprt &expr,
  const typet & dest_type)
{
  typet src_type = expr.type();

  assert(src_type.id()==  ID_pointer);
  assert(dest_type.id()== ID_pointer);

  struct_typet src_struct =
    to_struct_type(static_cast<const typet&>(follow(src_type.subtype())));

  struct_typet dest_struct =
    to_struct_type(static_cast<const typet&>(follow(dest_type.subtype())));

  assert(subtype_typecast(src_struct, dest_struct) ||
         subtype_typecast(dest_struct, src_struct));

  expr.make_typecast(dest_type);
}

