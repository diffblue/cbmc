/*******************************************************************\

Module: Variable Numbering

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/symbol.h>
#include <util/std_expr.h>
#include <util/i2string.h>

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
  out << "identifier: " << identifier << "\n";
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

Function: var_mapt::is_symex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool has_prefix(const irep_idt &identifier, const std::string& prefix)
{   
	return as_string(identifier).find(prefix)!=std::string::npos;
}
  

bool var_mapt::is_symex(const exprt &src)
{
	if(src.id()==ID_symbol) {
		return has_prefix(to_symbol_expr(src).get_identifier(),"symex::");
	}
	return false;        
}

bool var_mapt::is_nondet(const exprt &src)
{
	if(src.id()==ID_symbol) {
		return has_prefix(to_symbol_expr(src).get_identifier(), "symex::nondet");
	}
	return false;        
}

/*******************************************************************\

Function: var_mapt::init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void var_mapt::init(var_infot &var_info)
{
  if(has_prefix(id2string(var_info.symbol), "symex::dynamic_object"))
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
      throw "var_mapt::init identifier \"" + id2string(var_info.identifier)+
            "\" lookup in ns failed";
    }
  }

  if(var_info.is_shared())
    var_info.number=shared_count++;
  else
    var_info.number=local_count++;
}

/*******************************************************************\

Function: var_mapt::expr_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

var_mapt::var_infot *var_mapt::expr_rec(
  const exprt &src,
  const std::string &suffix,
  const typet &type)
{
  if(src.id()==ID_symbol)
  {
    // Is this a function?
    if(src.type().id()==ID_code)
      return NULL;
      
    if(src.get_bool(ID_C_SSA_symbol))
      return NULL; // SSA already
  
    irep_idt identifier=to_symbol_expr(src).get_identifier();

    var_infot &var_info=operator()(identifier, suffix, type);

    #ifdef DEBUG
    std::cout << "expr_rec " << identifier << " var_info "
              << var_info.identifier << std::endl;
    #endif

    return &var_info;
  }
  else if(src.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(src);
    return expr_rec(
      member_expr.struct_op(),
      "."+id2string(member_expr.get_component_name())+suffix,
      type);
  }
  else if(src.id()==ID_index)
  {
    return NULL;
  }
  else
    return NULL;
}

/*******************************************************************\

Function: var_mapt::var_infot::ssa_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt var_mapt::var_infot::ssa_identifier() const
{
  return id2string(identifier)+
         "#"+i2string(ssa_counter);
}
