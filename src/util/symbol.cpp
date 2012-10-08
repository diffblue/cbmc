/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>

#include "symbol.h"
#include "location.h"
#include "std_expr.h"

/*******************************************************************\

Function: symbolt::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
   
void symbolt::show(std::ostream &out) const
{
  out << "  " << name << std::endl;
  out << "    type:  " << type.pretty(4) << std::endl
      << "    value: " << value.pretty(4) << std::endl;

  out << "  flags:";
  if(is_lvalue)          out << " lvalue";
  if(is_static_lifetime) out << " static_lifetime";
  if(is_thread_local)    out << " thread_local";
  if(is_file_local)      out << " file_local";
  if(is_type)            out << " type";
  if(is_extern)          out << " extern";
  if(is_input)           out << " input";
  if(is_output)          out << " output";
  if(is_macro)           out << " macro";
  if(is_argument)        out << " argument";
  if(is_property)        out << " property";
  if(is_state_var)       out << " state_var";
  if(mode!="")           out << " mode=" << mode;
  if(base_name!="")      out << " base_name=" << base_name;
  if(module!="")         out << " module=" << module;
  if(pretty_name!="")    out << " pretty_name=" << pretty_name;
  out << std::endl;
  out << "  location: " << location << std::endl;

  out << "  hierarchy:";

  for(std::list<irep_idt>::const_iterator it=hierarchy.begin();
      it!=hierarchy.end();
      it++)
    out << " " << *it;

  out << std::endl;  
  out << std::endl;  
}

/*******************************************************************\

Function: operator<<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator<<(std::ostream &out,
                         const symbolt &symbol)
{
  symbol.show(out);
  return out;
}                        

/*******************************************************************\

Function: symbolt::to_irep

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symbolt::to_irep(irept &dest) const
{
  dest.clear();
  dest.add(ID_type)=type;
  dest.add(ID_value)=value;
  dest.add(ID_location)=location;
  dest.set(ID_name, name);
  dest.set(ID_module, module);
  dest.set(ID_base_name, base_name);
  dest.set(ID_mode, mode);
  dest.set(ID_pretty_name, pretty_name);

  if(is_type) dest.set("is_type", true);
  if(is_macro) dest.set("is_macro", true);
  if(is_exported) dest.set("is_exported", true);
  if(is_input) dest.set("is_input", true);
  if(is_output) dest.set("is_output", true);
  if(is_state_var) dest.set("is_statevar", true);
  if(is_argument) dest.set("is_argument", true);
  if(is_property) dest.set("is_property", true);
  if(is_lvalue) dest.set("is_lvalue", true);
  if(is_static_lifetime) dest.set("is_static_lifetime", true);
  if(is_thread_local) dest.set("is_thread_local", true);
  if(is_file_local) dest.set("is_file_local", true);
  if(is_extern) dest.set("is_extern", true);
  if(is_volatile) dest.set("is_volatile", true);       
}

/*******************************************************************\

Function: symbolt::from_irep

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symbolt::from_irep(const irept &src)
{
  type=static_cast<const typet &>(src.find(ID_type));
  value=static_cast<const exprt &>(src.find(ID_value));
  location=static_cast<const locationt &>(src.find(ID_location));

  name=src.get(ID_name);
  module=src.get(ID_module);
  base_name=src.get(ID_base_name);
  mode=src.get(ID_mode);
  pretty_name=src.get(ID_pretty_name);

  is_type=src.get_bool("is_type");
  is_macro=src.get_bool("is_macro");
  is_exported=src.get_bool("is_exported");
  is_input=src.get_bool("is_input");
  is_output=src.get_bool("is_output");
  is_state_var=src.get_bool("is_state_var");
  is_argument=src.get_bool("is_argument");
  is_property=src.get_bool("property");
  is_lvalue=src.get_bool("lvalue");
  is_static_lifetime=src.get_bool("static_lifetime");
  is_thread_local=src.get_bool("thread_local");
  is_file_local=src.get_bool("file_local");
  is_extern=src.get_bool("is_extern");
  is_volatile=src.get_bool("is_volatile");
}

/*******************************************************************\

Function: symbolt::swap

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symbolt::swap(symbolt &b)
{
  #define SYM_SWAP1(x) x.swap(b.x)
  
  SYM_SWAP1(type);
  SYM_SWAP1(value);
  SYM_SWAP1(name);
  SYM_SWAP1(pretty_name);
  SYM_SWAP1(module);
  SYM_SWAP1(base_name);
  SYM_SWAP1(mode);
  SYM_SWAP1(location);

  #define SYM_SWAP2(x) std::swap(x, b.x)
  
  SYM_SWAP2(is_type);
  SYM_SWAP2(is_macro);
  SYM_SWAP2(is_exported);
  SYM_SWAP2(is_input);
  SYM_SWAP2(is_output);
  SYM_SWAP2(is_state_var);
  SYM_SWAP2(is_argument);
  SYM_SWAP2(is_lvalue);
  SYM_SWAP2(is_static_lifetime);
  SYM_SWAP2(is_thread_local);
  SYM_SWAP2(is_file_local);
  SYM_SWAP2(is_extern);
  SYM_SWAP2(is_volatile);
}

/*******************************************************************\

Function: is_global

  Inputs: symbol

 Outputs: boolean

 Purpose: decides whether the symbol is a global variable

\*******************************************************************/

bool is_global(const symbolt &symbol)
{
  return symbol.is_static_lifetime && !symbol.is_thread_local;
}

/*******************************************************************\

Function: is_thread_local

  Inputs: symbol

 Outputs: boolean

 Purpose: decides whether the symbol is a thread local variable

\*******************************************************************/

bool is_thread_local(const symbolt &symbol)
{
  return symbol.is_static_lifetime && symbol.is_thread_local;
}

/*******************************************************************\

Function: is_procedure_local

  Inputs: symbol

 Outputs: boolean

 Purpose: decides whether the symbol is a procedure local variable

\*******************************************************************/

bool is_procedure_local(const symbolt &symbol)
{
  return !symbol.is_static_lifetime;
}

/*******************************************************************\

Function: symbolt::symbol_expr

  Inputs: symbol

 Outputs: boolean

 Purpose: decides whether the symbol is a procedure local variable

\*******************************************************************/

symbol_exprt symbolt::symbol_expr() const
{
  symbol_exprt tmp(type);
  tmp.set_identifier(name);
  return tmp;
}

