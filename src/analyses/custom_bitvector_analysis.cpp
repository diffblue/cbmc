/*******************************************************************\

Module: Field-insensitive, location-sensitive bitvector analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/simplify_expr.h>

#include "custom_bitvector_analysis.h"

#include <iostream>

/*******************************************************************\

Function: custom_bitvector_domaint::set_bit

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::set_bit(
  const exprt &lhs,
  unsigned bit_nr,
  modet mode)
{
  if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();
    
    vectorst &vectors=bits[identifier];

    if(mode==SET_MUST)
    {    
      vectors.must|=(1l<<bit_nr);
    }
    else if(mode==CLEAR_MUST)
    {
      vectors.must|=(1l<<bit_nr);
      vectors.must^=(1l<<bit_nr);
    }
  }
}

/*******************************************************************\

Function: custom_bitvector_domaint::assign_lhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::assign_lhs(
  const exprt &lhs,
  const vectorst &vectors)
{
  if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();
    bits[identifier]=vectors;
  }
}

/*******************************************************************\

Function: custom_bitvector_domaint::get_rhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::get_rhs(
  const exprt &lhs,
  vectorst &vectors)
{
  if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();
    vectors=bits[identifier];
  }
}

/*******************************************************************\

Function: custom_bitvector_analysist::get_bit_nr

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned custom_bitvector_analysist::get_bit_nr(
  const exprt &string_expr)
{
  if(string_expr.id()==ID_typecast)
    return get_bit_nr(to_typecast_expr(string_expr).op());
  else if(string_expr.id()==ID_address_of)
    return get_bit_nr(to_address_of_expr(string_expr).object());
  else if(string_expr.id()==ID_index)
    return get_bit_nr(to_index_expr(string_expr).array());
  else if(string_expr.id()==ID_string_constant)
  {
    irep_idt value=string_expr.get(ID_value); 
    return bits(value);
  }  
  else
    return bits("(unknown)");
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
  // upcast of ai
  custom_bitvector_analysist &cba=
    static_cast<custom_bitvector_analysist &>(ai);

  const goto_programt::instructiont &instruction=*from;

  switch(instruction.type)
  {
  case ASSIGN:
    {
      const code_assignt &code_assign=to_code_assign(instruction.code);
      
      // may alias other stuff
      std::set<exprt> lhs_set=
        cba.local_may_alias_factory(from).get(from, code_assign.lhs());
        
      lhs_set.insert(code_assign.lhs());

      for(std::set<exprt>::const_iterator
          l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
      {
        vectorst rhs_vectors;
        get_rhs(code_assign.rhs(), rhs_vectors);
        assign_lhs(*l_it, rhs_vectors);
      }
    }
    break;

  case DECL:
    {
      const code_declt &code_decl=to_code_decl(instruction.code);
      assign_lhs(code_decl.symbol(), vectorst());
    }
    break;

  case DEAD:
    {
      const code_deadt &code_dead=to_code_dead(instruction.code);
      assign_lhs(code_dead.symbol(), vectorst());
    }
    break;

  case FUNCTION_CALL:
    {
      const code_function_callt &code_function_call=to_code_function_call(instruction.code);
      const exprt &function=code_function_call.function();
      
      if(function.id()==ID_symbol)
      {
        const irep_idt &identifier=to_symbol_expr(function).get_identifier();
        if(identifier=="__CPROVER_set_must" ||
           identifier=="__CPROVER_clear_must")
        {
          if(code_function_call.arguments().size()==2)
          {
            unsigned bit_nr=
              cba.get_bit_nr(code_function_call.arguments()[1]);
              
            modet mode=(identifier=="__CPROVER_set_must")?SET_MUST:CLEAR_MUST;
            
            exprt lhs=code_function_call.arguments()[0];
            
            // may alias other stuff
            std::set<exprt> lhs_set=
              cba.local_may_alias_factory(from).get(from, lhs);

            for(std::set<exprt>::const_iterator
                l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
            {
              set_bit(*l_it, bit_nr, mode);
            }
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
  const custom_bitvector_analysist &cba=
    static_cast<const custom_bitvector_analysist &>(ai);

  for(bitst::const_iterator it=bits.begin();
      it!=bits.end();
      it++)
  {
    {
      out << it->first << " MAY: ";
      bit_vectort b=it->second.may;

      for(unsigned i=0; b!=0; i++, b>>=1)
        if(b&1)
        {
          assert(i<cba.bits.size());
          out << ' '
              << cba.bits[i];
        }

      out << '\n';
    }

    {
      out << it->first << " MUST: ";
      bit_vectort b=it->second.must;

      for(unsigned i=0; b!=0; i++, b>>=1)
        if(b&1)
        {
          assert(i<cba.bits.size());
          out << ' '
              << cba.bits[i];
        }

      out << '\n';
    }
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
    bitst::iterator a_it=bits.find(b_it->first);
    if(a_it!=bits.end())
    {
      if(a_it->second.merge(b_it->second))
        changed=true;
    }
    else
    {
      bits[b_it->first]=b_it->second;
      changed=true;
    }
  }
  
  // erase all blank ones
  for(bitst::const_iterator a_it=bits.begin();
      a_it!=bits.end();
      )
  {
    if(a_it->second.is_blank())
      a_it=bits.erase(a_it);
    else
      a_it++;
  }
  
  return changed;
}

/*******************************************************************\

Function: custom_bitvector_analysist::instrument

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_analysist::instrument(goto_functionst &)
{
}

/*******************************************************************\

Function: custom_bitvector_analysist::has_get_must

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool custom_bitvector_analysist::has_get_must(const exprt &src)
{
  if(src.id()=="get_must")
    return true;
  
  forall_operands(it, src)
    if(has_get_must(*it)) return true;

  return false;
}

/*******************************************************************\

Function: custom_bitvector_analysist::eval

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

exprt custom_bitvector_analysist::eval(
  const exprt &src,
  locationt loc)
{
  if(src.id()=="get_must")
  {
    if(src.operands().size()==2)
    {
      unsigned bit_nr=get_bit_nr(src.op1());

      exprt object=src.op0();
      
      custom_bitvector_domaint::vectorst v;
      operator[](loc).get_rhs(object, v);

      bool value=v.must&(1l<<bit_nr);
      
      if(value)
        return true_exprt();
      else
        return false_exprt();
    }
    else
      return src;
  }
  else
  {
    exprt tmp=src;
    Forall_operands(it, tmp)
      *it=eval(*it, loc);
  
    return tmp;
  }
}

/*******************************************************************\

Function: custom_bitvector_analysist::check

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_analysist::check(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out)
{
  forall_goto_functions(f_it, goto_functions)
  {
    if(!f_it->second.body.has_assertion()) continue;
    out << "******** Function " << f_it->first << '\n';
    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(!i_it->is_assert()) continue;
      if(!has_get_must(i_it->guard)) continue;
      out << i_it->source_location;
      if(!i_it->source_location.get_comment().empty())
        out << ", " << i_it->source_location.get_comment();
      out << ": ";
      exprt result=eval(i_it->guard, i_it);
      exprt result2=simplify_expr(result, ns);
      out << from_expr(ns, f_it->first, result2);
      out << '\n';
    }
    out << '\n';
  }
}
