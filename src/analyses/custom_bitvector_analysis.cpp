/*******************************************************************\

Module: Field-insensitive, location-sensitive bitvector analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/xml_expr.h>
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
  const irep_idt &identifier,
  unsigned bit_nr,
  modet mode)
{
  switch(mode)
  {
  case SET_MUST:
    {
      bit_vectort &bit_vector=must_bits[identifier];
      bit_vector|=(1l<<bit_nr);
    }
    break;
  
  case CLEAR_MUST:
    {
      bit_vectort &bit_vector=must_bits[identifier];
      bit_vector|=(1l<<bit_nr);
      bit_vector^=(1l<<bit_nr);
      if(bit_vector==0) must_bits.erase(identifier);
    }
    break;
  
  case SET_MAY:
    {
      bit_vectort &bit_vector=may_bits[identifier];
      bit_vector|=(1l<<bit_nr);
    }
    break;
  
  case CLEAR_MAY:
    {
      bit_vectort &bit_vector=may_bits[identifier];
      bit_vector|=(1l<<bit_nr);
      bit_vector^=(1l<<bit_nr);
      if(bit_vector==0) may_bits.erase(identifier);
    }
    break;
  }
}

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
    set_bit(identifier, bit_nr, mode);
  }
  else if(lhs.id()==ID_address_of)
  {
    const exprt &op=to_address_of_expr(lhs).object();
    if(op.id()==ID_symbol)
    {
      irep_idt identifier="&"+id2string(to_symbol_expr(op).get_identifier());
      set_bit(identifier, bit_nr, mode);
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

    // we erase blank ones to avoid noise

    if(vectors.must_bits==0)
      must_bits.erase(identifier);
    else
      must_bits[identifier]=vectors.must_bits;
    
    if(vectors.may_bits==0)
      may_bits.erase(identifier);
    else
      may_bits[identifier]=vectors.may_bits;
  }
}

/*******************************************************************\

Function: custom_bitvector_domaint::get_rhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

custom_bitvector_domaint::vectorst
  custom_bitvector_domaint::get_rhs(const irep_idt &identifier)
{
  vectorst vectors;

  bitst::const_iterator may_it=may_bits.find(identifier);
  if(may_it!=may_bits.end()) vectors.may_bits=may_it->second;
  
  bitst::const_iterator must_it=must_bits.find(identifier);
  if(must_it!=must_bits.end()) vectors.must_bits=must_it->second;
  
  return vectors;
}

/*******************************************************************\

Function: custom_bitvector_domaint::get_rhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

custom_bitvector_domaint::vectorst
  custom_bitvector_domaint::get_rhs(const exprt &rhs)
{
  if(rhs.id()==ID_symbol)
  {
    const irep_idt identifier=to_symbol_expr(rhs).get_identifier();
    return get_rhs(identifier);
  }
  else if(rhs.id()==ID_typecast)
  {
    return get_rhs(to_typecast_expr(rhs).op());
  }
  else if(rhs.id()==ID_if)
  {
    // need to merge both
    vectorst v_true=get_rhs(to_if_expr(rhs).true_case());
    vectorst v_false=get_rhs(to_if_expr(rhs).false_case());
    return merge(v_true, v_false);
  }
  else if(rhs.id()==ID_address_of)
  {
    const exprt &op=to_address_of_expr(rhs).object();
    if(op.id()==ID_symbol)
    {
      const irep_idt identifier="&"+id2string(to_symbol_expr(op).get_identifier());
      return get_rhs(identifier);
    }
  }
  
  return vectorst();
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
        vectorst rhs_vectors=get_rhs(code_assign.rhs());
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
           identifier=="__CPROVER_clear_must" ||
           identifier=="__CPROVER_set_may" ||
           identifier=="__CPROVER_clear_may")
        {
          if(code_function_call.arguments().size()==2)
          {
            unsigned bit_nr=
              cba.get_bit_nr(code_function_call.arguments()[1]);
              
            modet mode;
            
            if(identifier=="__CPROVER_set_must")
              mode=SET_MUST;
            else if(identifier=="__CPROVER_clear_must")
              mode=CLEAR_MUST;
            else if(identifier=="__CPROVER_set_may")
              mode=SET_MAY;
            else if(identifier=="__CPROVER_clear_may")
              mode=CLEAR_MAY;
            else
              assert(false);
            
            exprt lhs=code_function_call.arguments()[0];
            
            if(lhs.is_constant() &&
               to_constant_expr(lhs).get_value()==ID_NULL) // NULL means all
            {
              if(mode==CLEAR_MAY)
                for(bitst::const_iterator b_it=may_bits.begin();
                    b_it!=may_bits.end();
                    b_it++)
                  set_bit(b_it->first, bit_nr, mode);
              else if(mode==CLEAR_MUST)
                for(bitst::const_iterator b_it=must_bits.begin();
                    b_it!=must_bits.end();
                    b_it++)
                  set_bit(b_it->first, bit_nr, mode);
            }
            else
            {
              // may alias other stuff
              std::set<exprt> lhs_set=
                cba.local_may_alias_factory(from).get(from, lhs);

              lhs_set.insert(lhs);
               
              for(std::set<exprt>::const_iterator
                  l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
              {
                set_bit(*l_it, bit_nr, mode);
              }
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
  if(is_bottom)
    out << "BOTTOM\n";

  const custom_bitvector_analysist &cba=
    static_cast<const custom_bitvector_analysist &>(ai);
    
  for(bitst::const_iterator it=may_bits.begin();
      it!=may_bits.end();
      it++)
  {
    out << it->first << " MAY: ";
    bit_vectort b=it->second;
    
    for(unsigned i=0; b!=0; i++, b>>=1)
      if(b&1)
      {
        assert(i<cba.bits.size());
        out << ' '
            << cba.bits[i];
      }

    out << '\n';
  }

  for(bitst::const_iterator it=must_bits.begin();
      it!=must_bits.end();
      it++)
  {
    out << it->first << " MUST:";
    bit_vectort b=it->second;

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
  if(b.is_bottom)
    return false; // no change

  if(is_bottom)
  {
    *this=b;
    return true; // change
  }

  bool changed=false;

  // first do MAY
  for(bitst::const_iterator b_it=b.may_bits.begin();
      b_it!=b.may_bits.end();
      b_it++)
  {
    bit_vectort &a_bits=may_bits[b_it->first];
    bit_vectort old=a_bits;
    a_bits|=b_it->second;
    if(old!=a_bits) changed=true;
  }

  // now do MUST
  for(bitst::iterator a_it=must_bits.begin();
      a_it!=must_bits.end();
      a_it++)
  {
    bitst::const_iterator b_it=
      b.must_bits.find(a_it->first);

    if(b_it==b.must_bits.end())
    {
      a_it->second=0;
      changed=true;
    }
    else
    {
      bit_vectort old=a_it->second;
      a_it->second&=b_it->second;
      if(old!=a_it->second) changed=true;
    }
  }
  
  // erase blank ones
  for(bitst::iterator a_it=may_bits.begin();
      a_it!=may_bits.end();
      )
  {
    if(a_it->second==0)
      a_it=may_bits.erase(a_it);
    else
      a_it++;
  }
  
  // erase blank ones
  for(bitst::iterator a_it=must_bits.begin();
      a_it!=must_bits.end();
      )
  {
    if(a_it->second==0)
      a_it=must_bits.erase(a_it);
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

Function: custom_bitvector_analysist::has_get_must_or_may

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool custom_bitvector_analysist::has_get_must_or_may(const exprt &src)
{
  if(src.id()=="get_must" ||
     src.id()=="get_may")
    return true;
  
  forall_operands(it, src)
    if(has_get_must_or_may(*it)) return true;

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
  if(src.id()=="get_must" || src.id()=="get_may")
  {
    if(src.operands().size()==2)
    {
      unsigned bit_nr=get_bit_nr(src.op1());

      exprt object=src.op0();
      
      if(object.is_constant() &&
         to_constant_expr(object).get_value()==ID_NULL) // NULL means all
      {
        const custom_bitvector_domaint &d=operator[](loc);

        if(src.id()=="get_may")
        {
          for(custom_bitvector_domaint::bitst::const_iterator
              b_it=d.may_bits.begin();
              b_it!=d.may_bits.end();
              b_it++)
          {
            if(b_it->second&(1l<<bit_nr)) return true_exprt();
          }
          
          return false_exprt();
        }
        else
          return src;
      }
      else
      {
        custom_bitvector_domaint::vectorst v=
          operator[](loc).get_rhs(object);

        bool value=false;

        if(src.id()=="get_must")
          value=v.must_bits&(1l<<bit_nr);
        else if(src.id()=="get_may")
          value=v.may_bits&(1l<<bit_nr);

        if(value)
          return true_exprt();
        else
          return false_exprt();
      }
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
  bool use_xml,
  std::ostream &out)
{
  unsigned pass=0, fail=0, unknown=0;

  forall_goto_functions(f_it, goto_functions)
  {
    if(!f_it->second.body.has_assertion()) continue;
    
    if(f_it->first=="__actual_thread_spawn")
      continue;

    if(!use_xml)
      out << "******** Function " << f_it->first << '\n';

    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(!i_it->is_assert()) continue;
      if(!has_get_must_or_may(i_it->guard)) continue;

      if(operator[](i_it).is_bottom) continue;

      exprt result=eval(i_it->guard, i_it);
      exprt result2=simplify_expr(result, ns);

      if(use_xml)
      {
        out << "<result status=\"";
        if(result2.is_true())
          out << "SUCCESS";
        else if(result2.is_false())
          out << "FAILURE";
        else 
          out << "UNKNOWN";
        out << "\">\n";
        out << xml(i_it->source_location);
        out << "<description>"
            << i_it->source_location.get_comment()
            << "</description>\n";
        out << "</result>\n\n";
      }
      else
      {
        out << i_it->source_location;
        if(!i_it->source_location.get_comment().empty())
          out << ", " << i_it->source_location.get_comment();
        out << ": ";
        out << from_expr(ns, f_it->first, result2);
        out << '\n';
      }

      if(result2.is_true())
        pass++;
      else if(result2.is_false())
        fail++;
      else
        unknown++;
    }

    if(!use_xml)
      out << '\n';
  }
  
  if(!use_xml)
    out << "SUMMARY: " << pass << " pass, " << fail << " fail, "
        << unknown << " unknown\n";
}
