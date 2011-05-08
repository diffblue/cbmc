/*******************************************************************\

Module: ANSI-C Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_types.h>
#include <prefix.h>
#include <config.h>

#include "c_typecheck_base.h"
#include "expr2c.h"
#include "type2name.h"
#include "std_types.h"

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

Function: c_typecheck_baset::replace_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::replace_symbol(irept &symbol)
{
  id_replace_mapt::const_iterator it=
    id_replace_map.find(symbol.get(ID_identifier));
  
  if(it!=id_replace_map.end())
    symbol.set(ID_identifier, it->second);
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

  if(context.move(symbol, new_symbol))
  {
    err_location(symbol.location);
    throw "failed to move symbol `"+id2string(symbol.name)+
          "' into context";
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
  // first of all, we typecheck the type
  typecheck_type(symbol.type);

  bool is_function=symbol.type.id()==ID_code;

  const typet &final_type=follow(symbol.type);
  
  // set a few flags
  symbol.lvalue=!symbol.is_type && !symbol.is_macro;
  
  std::string prefix="c::";
  std::string root_name=prefix+id2string(symbol.base_name);
  std::string new_name=id2string(symbol.name);

  // do anon-tags first
  if(symbol.is_type &&
     has_prefix(id2string(symbol.name), prefix+"tag-#anon"))
  {    
    // we rename them to make collisions unproblematic
    std::string typestr = type2name(symbol.type);
    new_name = prefix+"tag-#anon#" + typestr;
    
    id_replace_map[symbol.name]=new_name;    

    contextt::symbolst::const_iterator it=context.symbols.find(new_name);
    if(it!=context.symbols.end())
      return; // bail out, we have an appropriate symbol already.

    irep_idt newtag=std::string("#anon#")+typestr;
    symbol.type.set(ID_tag, newtag);
  }
  else if(symbol.file_local)
  {
    // file-local stuff -- we rename to prevent collisions with
    // non-file local symbols with the same name
    // collisions are resolved during linking
    assert(has_prefix(new_name, prefix));
    new_name=prefix+"$file::"+std::string(new_name, prefix.size(), std::string::npos);
  }
  else if(symbol.is_extern && !is_function)
  {
    // variables mared as "extern" go into the global namespace
    // and have static lifetime
    new_name=root_name;
    symbol.static_lifetime=true;
  }
  else if(is_function && !symbol.is_actual)
  {
    // functions always go into the global namespace
    // (code doesn't have lifetime),
    // unless it's a function argument
    new_name=root_name;
    symbol.static_lifetime=false;
  }
  else if(!is_function && symbol.value.id()==ID_code)
  {
    err_location(symbol.value);
    throw "only functions can have a function body";
  }

  if(symbol.name!=new_name)
  {
    id_replace_map[symbol.name]=new_name;
    symbol.name=new_name;
  }

  // and now that we have the proper name
  // we clean the type of any side-effects
  // (needs to be done before next symbol)
  clean_type(symbol, symbol.type);
  
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
    // just strip the c::
    symbol.pretty_name=
      std::string(new_name, prefix.size(), std::string::npos);
      
    // strip the $file::
    if(has_prefix(id2string(symbol.pretty_name), "$file::"))
      symbol.pretty_name=std::string(id2string(symbol.pretty_name), 7, std::string::npos);
  }
  
  // see if we have it already
  contextt::symbolst::iterator old_it=context.symbols.find(symbol.name);
  
  if(old_it==context.symbols.end())
  {
    // just put into context
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
  if(symbol.is_actual)
    adjust_function_argument(symbol.type);

  // check initializer, if needed

  if(symbol.type.id()==ID_code)
  {
    if(symbol.value.is_not_nil())
      typecheck_function_body(symbol);
    else
    {
      // we don't need the identifiers
      code_typet &code_type=to_code_type(symbol.type);
      for(code_typet::argumentst::iterator
          it=code_type.arguments().begin();
          it!=code_type.arguments().end();
          it++)
        it->set_identifier(irep_idt());
    }
  }
  else
  {
    if(symbol.type.id()==ID_incomplete_array ||
       symbol.type.id()==ID_array)
    {
      // Insert a new type symbol for the array.
      // We do this because we want a convenient way
      // of making the type complete later on

      symbolt new_symbol;
      new_symbol.name=id2string(symbol.name)+"$type";
      new_symbol.base_name=id2string(symbol.base_name)+"$type"; 
      new_symbol.location=symbol.location;
      new_symbol.mode=symbol.mode;
      new_symbol.module=symbol.module;
      new_symbol.type=symbol.type;
      new_symbol.is_type=true;
      new_symbol.is_macro=false;
    
      symbol.type=symbol_typet(new_symbol.name);
    
      symbolt *new_sp;
      context.move(new_symbol, new_sp);
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
            << "' defined twice:" << std::endl;
        str << "Original: " << to_string(old_symbol.type) << std::endl;
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
  // do initializer, this may change the type
  if(follow(new_symbol.type).id()!=ID_code)
    do_initializer(new_symbol);
  
  const typet &final_old=follow(old_symbol.type);
  const typet &final_new=follow(new_symbol.type);
  
  // K&R stuff?
  if(old_symbol.type.id()==ID_KnR)
  {
    // check the type
    if(final_new.id()==ID_code)
    {
      err_location(new_symbol.location);
      throw "function type not allowed for K&R function argument";
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
          << "' defined twice with different types:" << std::endl;
      str << "Original: " << to_string(old_symbol.type) << std::endl;
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
        err_location(new_symbol.location);
        str << "function `" << new_symbol.display_name()
            << "' defined twice";
        error();
        throw 0;
      }

      typecheck_function_body(new_symbol);
    
      // overwrite location
      old_symbol.location=new_symbol.location;
    
      // move body
      old_symbol.value.swap(new_symbol.value);

      // overwrite type (because of argument names)
      old_symbol.type=new_symbol.type;
    }

    return;
  }

  if(final_old!=final_new)
  {
    if(final_old.id()==ID_array &&
       final_new.id()==ID_incomplete_array &&
       final_old.subtype()==final_new.subtype())
    {
      // this is ok, just use old type
      new_symbol.type=old_symbol.type;
    }
    else if(final_old.id()==ID_incomplete_array &&
            final_new.id()==ID_array &&
            final_old.subtype()==final_new.subtype())
    {
      // this is also ok
      if(old_symbol.type.id()==ID_symbol)
      {
        // fix the symbol, not just the type
        const irep_idt identifier=
          old_symbol.type.get(ID_identifier);

        contextt::symbolst::iterator s_it=context.symbols.find(identifier);
  
        if(s_it==context.symbols.end())
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
    else
    {
      err_location(new_symbol.location);
      str << "error: symbol `" << new_symbol.display_name()
          << "' defined twice with different types:" << std::endl;
      str << "Original: " << to_string(old_symbol.type) << std::endl;
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
  
  // adjust the function identifiers
  for(code_typet::argumentst::iterator
      a_it=code_type.arguments().begin();
      a_it!=code_type.arguments().end();
      a_it++)
  {
    irep_idt identifier=a_it->get_identifier();
    if(identifier!=irep_idt())
    {
      id_replace_mapt::const_iterator
        m_it=id_replace_map.find(identifier);

      if(m_it!=id_replace_map.end())
        a_it->set_identifier(m_it->second);      
    }
  }
    
  assert(symbol.value.is_not_nil());

  // fix type
  symbol.value.type()=code_type;
    
  // set return type
  return_type=code_type.return_type();
  
  typecheck_code(to_code(symbol.value));
  
  if(symbol.name=="c::main")
    add_argc_argv(symbol);
}
