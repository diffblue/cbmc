/*******************************************************************\

Module: Variable Numbering

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include <util/symbol.h>
#include <util/std_expr.h>
#include <util/i2string.h>
#include <util/prefix.h>

#include "var_map.h"

// #define DEBUG

/*******************************************************************\

Function: var_mapt::var_infot::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

var_mapt::var_infot & var_mapt::operator()(
  const irep_idt &symbol,
  const irep_idt &suffix,
  const typet &type)
{
  assert(symbol!=irep_idt());

  std::string full_identifier=
    id2string(symbol)+id2string(suffix);

  std::pair<id_mapt::iterator, bool> result;

  result=id_map.insert(std::pair<irep_idt, var_infot>(
    full_identifier, var_infot()));

  if(result.second) // inserted?
  {
    result.first->second.full_identifier=full_identifier;
    result.first->second.symbol=symbol;
    result.first->second.suffix=suffix;
    result.first->second.type=type;
    init(result.first->second);
  }
  
  return result.first->second;
}

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

/*******************************************************************\

Function: var_mapt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void var_mapt::output(std::ostream &out) const
{
  for(id_mapt::const_iterator
      it=id_map.begin();
      it!=id_map.end();
      it++)
  {
    out << it->first << ":\n";
    it->second.output(out);
  }
}
