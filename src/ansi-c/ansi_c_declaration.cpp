/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/config.h>

#include "ansi_c_declaration.h"

/*******************************************************************\

Function: ansi_c_declarationt::ansi_c_declarationt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ansi_c_declarationt::ansi_c_declarationt():exprt(ID_declaration)
{
}
  
/*******************************************************************\

Function: ansi_c_declarationt::to_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_declarationt::to_symbol(symbolt &symbol) const
{
  symbol.clear();    
  symbol.value=value();
  symbol.type=type();
  symbol.name="c::"+id2string(get_name());
  symbol.base_name=get_base_name();
  symbol.is_type=get_is_type();
  if(symbol.is_type)
    symbol.location=symbol.type.location();
  else
    symbol.location=location();
  symbol.is_extern=get_is_extern();
  symbol.is_macro=get_is_macro();
  symbol.is_parameter=get_is_parameter();

  bool is_code=symbol.type.id()==ID_code;

  symbol.is_static_lifetime=
    !symbol.is_macro &&
    !symbol.is_type &&
    (get_is_global() || get_is_static()) &&
    !is_code;
    
  symbol.is_thread_local=
    (!get_is_global() && !is_code &&
     !get_is_static() && !symbol.is_type &&
     !symbol.is_macro) ||
    (get_is_global() && !is_code && get_is_thread_local());
     
  symbol.is_file_local=
    get_is_static() || symbol.is_macro || 
    (!get_is_global() && !get_is_extern() && !is_code);
  
  if(get_is_inline())
    symbol.type.set(ID_C_inlined, true);

  // GCC extern inline cleanup, to enable remove_internal_symbols
  // do its full job
  // https://gcc.gnu.org/ml/gcc/2006-11/msg00006.html
  if(is_code && get_is_inline())
  {
    // __attribute__((__gnu_inline__))
    if(get_is_static() && get_is_extern())
      symbol.is_extern=false;
    // C99 and above
    else if(config.ansi_c.for_has_scope ||
            (config.ansi_c.mode!=configt::ansi_ct::MODE_GCC_C &&
             config.ansi_c.mode!=configt::ansi_ct::MODE_ARM_C_CPP))
      symbol.is_file_local=symbol.is_file_local || !get_is_extern();
    // traditional GCC
    else
      symbol.is_file_local=symbol.is_file_local || get_is_extern();
  }
}
