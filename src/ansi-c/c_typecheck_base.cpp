/*******************************************************************\

Module: ANSI-C Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/prefix.h>
#include <util/config.h>
#include <util/std_types.h>
#include <util/i2string.h>

#include "c_typecheck_base.h"
#include "expr2c.h"
#include "type2name.h"
#include "c_storage_spec.h"

/*******************************************************************\

Function: c_typecheck_baset::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string c_typecheck_baset::to_string(const exprt &expr)
{ 
  return expr2c(expr, *this);
}

/*******************************************************************\

Function: c_typecheck_baset::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string c_typecheck_baset::to_string(const typet &type)
{ 
  return type2c(type, *this);
}

/*******************************************************************\

Function: c_typecheck_baset::move_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::move_symbol(symbolt &symbol, symbolt *&new_symbol)
{
  symbol.mode=mode;
  symbol.module=module;

  if(symbol_table.move(symbol, new_symbol))
  {
    err_location(symbol.location);
    throw "failed to move symbol `"+id2string(symbol.name)+
          "' into symbol table";
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_symbol(symbolt &symbol)
{
  current_symbol_id=symbol.name;

  bool is_function=symbol.type.id()==ID_code;

  const typet &final_type=follow(symbol.type);
  
  // set a few flags
  symbol.is_lvalue=!symbol.is_type && !symbol.is_macro;
  
  irep_idt root_name=symbol.base_name;
  irep_idt new_name=symbol.name;

  if(symbol.is_file_local)
  {
    // file-local stuff -- stays as is
    // collisions are resolved during linking
  }
  else if(symbol.is_extern && !is_function)
  {
    // variables marked as "extern" go into the global namespace
    // and have static lifetime
    new_name=root_name;
    symbol.is_static_lifetime=true;
  }
  else if(!is_function && symbol.value.id()==ID_code)
  {
    err_location(symbol.value);
    throw "only functions can have a function body";
  }
  
  // set the pretty name
  if(symbol.is_type &&
     (final_type.id()==ID_struct ||
      final_type.id()==ID_incomplete_struct))
  {
    symbol.pretty_name="struct "+id2string(symbol.base_name);
  }
  else if(symbol.is_type &&
          (final_type.id()==ID_union ||
           final_type.id()==ID_incomplete_union))
  {
    symbol.pretty_name="union "+id2string(symbol.base_name);
  }
  else if(symbol.is_type &&
          (final_type.id()==ID_c_enum ||
           final_type.id()==ID_incomplete_c_enum))
  {
    symbol.pretty_name="enum "+id2string(symbol.base_name);
  }
  else
  {
    symbol.pretty_name=new_name;
  }
  
  // see if we have it already
  symbol_tablet::symbolst::iterator old_it=symbol_table.symbols.find(symbol.name);
  
  if(old_it==symbol_table.symbols.end())
  {
    // just put into symbol_table
    symbolt *new_symbol;
    move_symbol(symbol, new_symbol);
    
    typecheck_new_symbol(*new_symbol);
  }    
  else
  {
    if(old_it->second.is_type!=symbol.is_type)
    {
      err_location(symbol.location);
      str << "redeclaration of `" << symbol.display_name()
          << "' as a different kind of symbol";
      throw 0;
    }

    if(symbol.is_type)
      typecheck_redefinition_type(old_it->second, symbol);
    else
      typecheck_redefinition_non_type(old_it->second, symbol);
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_new_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_new_symbol(symbolt &symbol)
{
  if(symbol.is_parameter)
    adjust_function_parameter(symbol.type);

  // check initializer, if needed

  if(symbol.type.id()==ID_code)
  {
    if(symbol.value.is_not_nil())
      typecheck_function_body(symbol);
    else
    {
      // we don't need the identifiers
      code_typet &code_type=to_code_type(symbol.type);
      for(code_typet::parameterst::iterator
          it=code_type.parameters().begin();
          it!=code_type.parameters().end();
          it++)
        it->set_identifier(irep_idt());
    }
  }
  else
  {
    if(symbol.type.id()==ID_array &&
       to_array_type(symbol.type).size().is_nil() &&
       !symbol.is_type)
    {
      // Insert a new type symbol for the array.
      // We do this because we want a convenient way
      // of adjusting the size of the type later on.

      type_symbolt new_symbol(symbol.type);
      new_symbol.name=id2string(symbol.name)+"$type";
      new_symbol.base_name=id2string(symbol.base_name)+"$type"; 
      new_symbol.location=symbol.location;
      new_symbol.mode=symbol.mode;
      new_symbol.module=symbol.module;
    
      symbol.type=symbol_typet(new_symbol.name);
    
      symbolt *new_sp;
      symbol_table.move(new_symbol, new_sp);
    }

    // check the initializer
    do_initializer(symbol);
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_redefinition_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_redefinition_type(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  const typet &final_old=follow(old_symbol.type);
  const typet &final_new=follow(new_symbol.type);

  // see if we had s.th. incomplete before
  if(final_old.id()==ID_incomplete_struct ||
     final_old.id()==ID_incomplete_union ||
     final_old.id()==ID_incomplete_c_enum)
  {
    // new one complete?
    if("incomplete_"+final_new.id_string()==final_old.id_string())
    {
      // overwrite location
      old_symbol.location=new_symbol.location;
      
      // move body
      old_symbol.type.swap(new_symbol.type);
    }
    else if(new_symbol.type.id()==old_symbol.type.id())
      return;
    else
    {
      err_location(new_symbol.location);
      str << "error: conflicting definition of type symbol `"
          << new_symbol.display_name()
          << "'";
      throw 0;
    }
  }
  else
  {
    // see if new one is just a tag
    if(final_new.id()==ID_incomplete_struct ||
       final_new.id()==ID_incomplete_union ||
       final_new.id()==ID_incomplete_c_enum)
    {
      if("incomplete_"+final_old.id_string()==final_new.id_string())
      {
        // just ignore silently  
      }
      else
      {
        // arg! new tag type
        err_location(new_symbol.location);
        str << "error: conflicting definition of tag symbol `"
            << new_symbol.display_name()
            << "'";
        throw 0;
      }
    }
    else if(config.ansi_c.os==configt::ansi_ct::OS_WIN &&
            final_new.id()==ID_c_enum && final_old.id()==ID_c_enum)              
    {        
      // under Windows, ignore this silently;
      // MSC doesn't think this is a problem, but GCC complains.
    }
    else if(config.ansi_c.os==configt::ansi_ct::OS_WIN &&
            final_new.id()==ID_pointer && final_old.id()==ID_pointer &&
            follow(final_new.subtype()).id()==ID_c_enum &&
            follow(final_old.subtype()).id()==ID_c_enum)
    {
      // under Windows, ignore this silently;
      // MSC doesn't think this is a problem, but GCC complains.
    }
    else
    {
      // see if it changed
      if(follow(new_symbol.type)!=follow(old_symbol.type))
      {
        err_location(new_symbol.location);
        str << "error: type symbol `" << new_symbol.display_name()
            << "' defined twice:" << "\n";
        str << "Original: " << to_string(old_symbol.type) << "\n";
        str << "     New: " << to_string(new_symbol.type);
        throw 0;
      }
    }
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_redefinition_non_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_redefinition_non_type(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  const typet &final_old=follow(old_symbol.type);
  const typet &initial_new=follow(new_symbol.type);

  if(final_old.id()==ID_array &&
     to_array_type(final_old).size().is_not_nil() &&
     initial_new.id()==ID_array &&
     to_array_type(initial_new).size().is_nil() &&
     final_old.subtype()==initial_new.subtype())
  {
    // this is ok, just use old type
    new_symbol.type=old_symbol.type;
  }

  // do initializer, this may change the type
  if(follow(new_symbol.type).id()!=ID_code)
    do_initializer(new_symbol);
  
  const typet &final_new=follow(new_symbol.type);
  
  // K&R stuff?
  if(old_symbol.type.id()==ID_KnR)
  {
    // check the type
    if(final_new.id()==ID_code)
    {
      err_location(new_symbol.location);
      throw "function type not allowed for K&R function parameter";
    }
    
    // fix up old symbol -- we now got the type
    old_symbol.type=new_symbol.type;
    return;
  }
  
  if(final_new.id()==ID_code)
  {
    bool inlined=
       (new_symbol.type.get_bool(ID_C_inlined) ||
        old_symbol.type.get_bool(ID_C_inlined));
        
    if(final_old.id()!=ID_code)
    {
      err_location(new_symbol.location);
      str << "error: function symbol `" << new_symbol.display_name()
          << "' redefined with a different type:" << "\n";
      str << "Original: " << to_string(old_symbol.type) << "\n";
      str << "     New: " << to_string(new_symbol.type);
      throw 0;
    }

    code_typet &old_ct=to_code_type(old_symbol.type);
    code_typet &new_ct=to_code_type(new_symbol.type);
    
    if(old_ct.has_ellipsis() && !new_ct.has_ellipsis())
      old_ct=new_ct;
    else if(!old_ct.has_ellipsis() && new_ct.has_ellipsis())
      new_ct=old_ct;

    if(inlined)
    {
      old_symbol.type.set(ID_C_inlined, true);
      new_symbol.type.set(ID_C_inlined, true);
    }

    // do body
    
    if(new_symbol.value.is_not_nil())
    {  
      if(old_symbol.value.is_not_nil())
      {
        // gcc allows re-definition if the first
        // definition is marked as "extern inline"
        
        if(old_symbol.type.get_bool(ID_C_inlined) &&
           (config.ansi_c.mode==configt::ansi_ct::MODE_GCC_C ||
            config.ansi_c.mode==configt::ansi_ct::MODE_ARM_C_CPP))
        {
          // overwrite "extern inline" properties
          old_symbol.is_extern=new_symbol.is_extern;
          old_symbol.is_file_local=new_symbol.is_file_local;

          // remove parameter declarations to avoid conflicts
          const code_typet::parameterst &old_p=old_ct.parameters();
          for(code_typet::parameterst::const_iterator
              p_it=old_p.begin();
              p_it!=old_p.end();
              p_it++)
          {
            const irep_idt &identifier=p_it->get_identifier();

            symbol_tablet::symbolst::iterator p_s_it=
              symbol_table.symbols.find(identifier);
            if(p_s_it!=symbol_table.symbols.end())
              symbol_table.symbols.erase(p_s_it);
          }
        }
        else
        {
          err_location(new_symbol.location);
          str << "function body `" << new_symbol.display_name()
              << "' defined twice";
          error();
          throw 0;
        }
      }
      else if(inlined)
      {
        // preserve "extern inline" properties
        old_symbol.is_extern=new_symbol.is_extern;
        old_symbol.is_file_local=new_symbol.is_file_local;
      }

      typecheck_function_body(new_symbol);
    
      // overwrite location
      old_symbol.location=new_symbol.location;
    
      // move body
      old_symbol.value.swap(new_symbol.value);

      // overwrite type (because of parameter names)
      old_symbol.type=new_symbol.type;
    }

    return;
  }

  if(final_old!=final_new)
  {
    if(final_old.id()==ID_array &&
            to_array_type(final_old).size().is_nil() &&
            final_new.id()==ID_array &&
            to_array_type(final_new).size().is_not_nil() &&
            final_old.subtype()==final_new.subtype())
    {
      // this is also ok
      if(old_symbol.type.id()==ID_symbol)
      {
        // fix the symbol, not just the type
        const irep_idt identifier=
          to_symbol_type(old_symbol.type).get_identifier();

        symbol_tablet::symbolst::iterator s_it=symbol_table.symbols.find(identifier);
  
        if(s_it==symbol_table.symbols.end())
        {
          err_location(old_symbol.location);
          str << "typecheck_redefinition_non_type: "
                 "failed to find symbol `" << identifier << "'";
          throw 0;
        }
                  
        symbolt &symbol=s_it->second;
          
        symbol.type=final_new;          
      }
      else
        old_symbol.type=new_symbol.type;
    }
    else if((final_old.id()==ID_incomplete_c_enum ||
             final_old.id()==ID_c_enum) &&
            (final_new.id()==ID_incomplete_c_enum ||
             final_new.id()==ID_c_enum))
    {
      // this is ok for now
    }
    else if(final_old.id()==ID_pointer &&
            follow(final_old).subtype().id()==ID_code &&
            to_code_type(follow(final_old).subtype()).has_ellipsis() &&
            final_new.id()==ID_pointer &&
            follow(final_new).subtype().id()==ID_code)
    {
      // to allow 
      // int (*f) ();
      // int (*f) (int)=0;
      old_symbol.type=new_symbol.type;
    }
    else if(final_old.id()==ID_pointer &&
            follow(final_old).subtype().id()==ID_code &&
            final_new.id()==ID_pointer &&
            follow(final_new).subtype().id()==ID_code &&
            to_code_type(follow(final_new).subtype()).has_ellipsis())
    {
      // to allow 
      // int (*f) (int)=0;
      // int (*f) ();
    }
    else
    {
      err_location(new_symbol.location);
      str << "error: symbol `" << new_symbol.display_name()
          << "' redefined with a different type:" << "\n";
      str << "Original: " << to_string(old_symbol.type) << "\n";
      str << "     New: " << to_string(new_symbol.type);
      throw 0;
    }
  }
  else // finals are equal
  {
  }

  // do value
  if(new_symbol.value.is_not_nil())
  {
    // see if we already have one
    if(old_symbol.value.is_not_nil())
    {
      if(new_symbol.value.get_bool(ID_C_zero_initializer))
      {
        // do nothing
      }
      else if(old_symbol.value.get_bool(ID_C_zero_initializer))
      {
        old_symbol.value=new_symbol.value;
        old_symbol.type=new_symbol.type;
      }
      else
      {
        if(new_symbol.is_macro &&
           (final_new.id()==ID_incomplete_c_enum ||
            final_new.id()==ID_c_enum) &&
            old_symbol.value.is_constant() &&
            new_symbol.value.is_constant() &&
            old_symbol.value.get(ID_value)==new_symbol.value.get(ID_value))
        {
          // ignore
        }
        else
        {
          err_location(new_symbol.value);
          str << "symbol `" << new_symbol.display_name()
              << "' already has an initial value";
          warning();
        }
      }
    }
    else
    {
      old_symbol.value=new_symbol.value;
      old_symbol.type=new_symbol.type;
    }
  }
  
  // take care of some flags
  if(old_symbol.is_extern && !new_symbol.is_extern)
    old_symbol.location=new_symbol.location;

  old_symbol.is_extern=old_symbol.is_extern && new_symbol.is_extern;
  
  // We should likely check is_volatile and
  // is_thread_local for consistency. GCC complains if these
  // mismatch.
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_function_body

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_function_body(symbolt &symbol)
{
  code_typet &code_type=to_code_type(symbol.type);
  
  assert(symbol.value.is_not_nil());
  
  // reset labels
  labels_used.clear();
  labels_defined.clear();

  // fix type
  symbol.value.type()=code_type;
    
  // set return type
  return_type=code_type.return_type();
  
  unsigned anon_counter=0;
  
  // Add the parameter declarations into the symbol table.
  code_typet::parameterst &parameters=code_type.parameters();
  for(code_typet::parameterst::iterator
      p_it=parameters.begin();
      p_it!=parameters.end();
      p_it++)
  {
    // may be anonymous
    if(p_it->get_base_name()==irep_idt())
    {
      irep_idt base_name="#anon"+i2string(anon_counter++);
      p_it->set_base_name(base_name);
    }
    
    // produce identifier
    irep_idt base_name=p_it->get_base_name();
    irep_idt identifier=id2string(symbol.name)+"::"+id2string(base_name);

    p_it->set_identifier(identifier);

    parameter_symbolt p_symbol;
    
    p_symbol.type=p_it->type();
    p_symbol.name=identifier;
    p_symbol.base_name=base_name;
    p_symbol.location=p_it->source_location();

    symbolt *new_p_symbol;
    move_symbol(p_symbol, new_p_symbol);
  }

  // typecheck the body code  
  typecheck_code(to_code(symbol.value));

  // special case for main()  
  if(symbol.name==ID_main)
    add_argc_argv(symbol);

  // check the labels
  for(std::map<irep_idt, source_locationt>::const_iterator
      it=labels_used.begin(); it!=labels_used.end(); it++)
  {
    if(labels_defined.find(it->first)==labels_defined.end())
    {
      err_location(it->second);
      str << "branching label `" << it->first
          << "' is not defined in function";
      throw 0;
    }
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_declaration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_declaration(
  ansi_c_declarationt &declaration)
{
  if(declaration.get_is_static_assert())
  {
    assert(declaration.operands().size()==2);
    typecheck_expr(declaration.op0());
    typecheck_expr(declaration.op1());
  }
  else
  {
    // get storage spec
    c_storage_spect c_storage_spec(declaration.type());
  
    declaration.set_is_inline(c_storage_spec.is_inline);
    declaration.set_is_static(c_storage_spec.is_static);
    declaration.set_is_extern(c_storage_spec.is_extern);
    declaration.set_is_thread_local(c_storage_spec.is_thread_local);
    declaration.set_is_register(c_storage_spec.is_register);
    declaration.set_is_typedef(c_storage_spec.is_typedef);

    // first typecheck the type of the declaration
    typecheck_type(declaration.type());
    
    // mark as 'already typechecked'
    make_already_typechecked(declaration.type());

    // Now do declarators, if any.
    for(ansi_c_declarationt::declaratorst::iterator
        d_it=declaration.declarators().begin();
        d_it!=declaration.declarators().end();
        d_it++)
    {
      symbolt symbol;
      declaration.to_symbol(*d_it, symbol);

      // now check other half of type
      typecheck_type(symbol.type);

      typecheck_symbol(symbol);
    }
  }
}

