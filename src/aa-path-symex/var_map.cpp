/*******************************************************************\

Module: Variable Numbering

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/symbol.h>
#include <util/std_expr.h>
#include <util/i2string.h>
#include <util/prefix.h>

#include "var_map.h"

// #define DEBUG

/*******************************************************************\

Function: var_mapt::var_infot::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void var_mapt::var_infot::output(std::ostream &out) const
{
  out << "full_identifier: " << full_identifier << "\n";
  out << "symbol: " << symbol << "\n";
  out << "suffix: " << suffix << "\n";

  out << "kind: ";

  switch(kind)
  {
  case PROCEDURE_LOCAL: out << "PROCEDURE_LOCAL"; break;
  case THREAD_LOCAL: out << "THREAD_LOCAL"; break;
  case SHARED: out << "SHARED"; break;
  }
  
  out << "\n";
  
  out << "number: " << number << "\n";
  
  out << "type: " << type << "\n";
  
  out << "\n";
}

/*******************************************************************\

Function: var_mapt::init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void var_mapt::init(var_infot &var_info)
{
  if(has_prefix(id2string(var_info.symbol), "symex_dynamic::"))
  {
    var_info.kind=var_infot::SHARED;
  }
  else
  {
    try
    {
      const symbolt &symbol=ns.lookup(var_info.symbol);

      if(symbol.is_static_lifetime)
      {
        if(symbol.is_thread_local)
          var_info.kind=var_infot::THREAD_LOCAL;
        else
          var_info.kind=var_infot::SHARED;
      }
      else
        var_info.kind=var_infot::PROCEDURE_LOCAL;
    }
    
    catch(std::string s)
    {
      throw "var_mapt::init identifier \"" +
            id2string(var_info.full_identifier)+
            "\" lookup in ns failed";
    }
  }

  if(var_info.is_shared())
    var_info.number=shared_count++;
  else
    var_info.number=local_count++;
}

/*******************************************************************\

Function: var_mapt::var_infot::ssa_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt var_mapt::var_infot::ssa_identifier() const
{
  return id2string(full_identifier)+
         "#"+i2string(ssa_counter);
}
