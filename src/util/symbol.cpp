/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "symbol.h"
#include "source_location.h"
#include "std_expr.h"

/*******************************************************************\

Function: symbolt::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
   
void symbolt::show(std::ostream &out) const
{
  out << "  " << name << '\n';
  out << "    type:  " << type.pretty(4) << '\n'
      << "    value: " << value.pretty(4) << '\n';

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
  if(is_parameter)       out << " parameter";
  if(is_auxiliary)       out << " auxiliary";
  if(is_property)        out << " property";
  if(is_state_var)       out << " state_var";
  if(is_exported)        out << " exported";
  if(is_volatile)        out << " volatile";
  if(mode!="")           out << " mode=" << mode;
  if(base_name!="")      out << " base_name=" << base_name;
  if(module!="")         out << " module=" << module;
  if(pretty_name!="")    out << " pretty_name=" << pretty_name;
  out << '\n';
  out << "  location: " << location << '\n';

  out << '\n';  
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
  if(is_parameter) dest.set("is_parameter", true);
  if(is_auxiliary) dest.set("is_auxiliary", true);
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
  location=static_cast<const source_locationt &>(src.find(ID_location));

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
  is_parameter=src.get_bool("is_parameter");
  is_auxiliary=src.get_bool("is_auxiliary");
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
  SYM_SWAP2(is_property);
  SYM_SWAP2(is_parameter);
  SYM_SWAP2(is_auxiliary);
  SYM_SWAP2(is_lvalue);
  SYM_SWAP2(is_static_lifetime);
  SYM_SWAP2(is_thread_local);
  SYM_SWAP2(is_file_local);
  SYM_SWAP2(is_extern);
  SYM_SWAP2(is_volatile);
}

/*******************************************************************\

Function: symbolt::symbol_expr

  Inputs: symbol

 Outputs: symbol_exprt

 Purpose: produces a symbol_exprt for a symbol

\*******************************************************************/

symbol_exprt symbolt::symbol_expr() const
{
  return symbol_exprt(name, type);
}

