/*******************************************************************\

Module: Field-insensitive, location-sensitive bitvector analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "custom_bitvector_analysis.h"

/*******************************************************************\

Function: custom_bitvector_domaint::assign_lhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::assign_lhs(
  const exprt &lhs, const exprt &rhs)
{
  
}

/*******************************************************************\

Function: custom_bitvector_domaint::set_bit

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::set_bit(
  const exprt &lhs, unsigned bit_nr, bool value)
{
  if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();

    bit_vectort bv=bits[identifier];
    
    bv|=(1l<<bit_nr);
    if(!value) bv^=(1l<<bit_nr); // clears it
  }
  else if(lhs.id()==ID_member)
  {
    set_bit(to_member_expr(lhs).struct_op(), bit_nr, value);
  }
  else if(lhs.id()==ID_index)
  {
    if(value) // need to be monotone
      set_bit(to_index_expr(lhs).array(), bit_nr, value);
  }
}

/*******************************************************************\

Function: custom_bitvector_domaint::assign_lhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned custom_bitvector_domaint::get_bit_nr(
  ai_baset &ai,
  const exprt &string_expr)
{
  if(string_expr.id()==ID_typecast)
    return get_bit_nr(ai, to_typecast_expr(string_expr).op());
  else if(string_expr.id()==ID_address_of)
    return get_bit_nr(ai, to_address_of_expr(string_expr).object());
  else if(string_expr.id()==ID_index)
    return get_bit_nr(ai, to_index_expr(string_expr).array());
  else if(string_expr.id()==ID_string_constant)
  {
    irep_idt value=string_expr.get(ID_value); 
    return static_cast<custom_bitvector_analysist &>(ai).bits(value);
  }  
  else
    return static_cast<custom_bitvector_analysist &>(ai).bits("(unknown)");
}

/*******************************************************************\

Function: custom_bitvector_domaint::transform

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  const goto_programt::instructiont &instruction=*from;

  switch(instruction.type)
  {
  case ASSIGN:
    {
      const code_assignt &code_assign=to_code_assign(instruction.code);
      assign_lhs(code_assign.lhs(), code_assign.rhs());
    }
    break;

  case DECL:
    {
      const code_declt &code_decl=to_code_decl(instruction.code);
      assign_lhs(code_decl.symbol(), nil_exprt());
    }
    break;

  case DEAD:
    {
      const code_deadt &code_dead=to_code_dead(instruction.code);
      assign_lhs(code_dead.symbol(), nil_exprt());
    }
    break;

  case FUNCTION_CALL:
    {
      const code_function_callt &code_function_call=to_code_function_call(instruction.code);
      const exprt &function=code_function_call.function();
      
      if(function.id()==ID_symbol)
      {
        const irep_idt &identifier=to_symbol_expr(function).get_identifier();
        if(identifier=="__CPROVER_set_flag" ||
           identifier=="__CPROVER_clear_flag")
        {
          if(code_function_call.arguments().size()==2)
          {
            set_bit(code_function_call.arguments()[0],
                    get_bit_nr(ai, code_function_call.arguments()[1]),
                    identifier=="__CPROVER_set_flag");
          }
        }
      }
    }
    break;

  default:;
  }
}

/*******************************************************************\

Function: custom_bitvector_domaint::output

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  for(bitst::const_iterator it=bits.begin();
      it!=bits.end();
      it++)
  {
    out << it->first << ": ";
    bit_vectort b=it->second;

    for(unsigned i=0; b!=0; i++, b<<=1)
      if(b&1)
        out << ' '
            << static_cast<const custom_bitvector_analysist &>(ai).bits[i];

    out << '\n';
  }
}

/*******************************************************************\

Function: custom_bitvector_domaint::merge

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool custom_bitvector_domaint::merge(
  const custom_bitvector_domaint &b,
  locationt from,
  locationt to)
{
  bool changed=false;
  for(bitst::const_iterator b_it=b.bits.begin();
      b_it!=b.bits.end();
      b_it++)
  {
    bit_vectort &a=bits[b_it->first];
    bit_vectort old=a;
    a|=b_it->second;
    if(a!=old) changed=true;
  }
  
  return changed;
}
