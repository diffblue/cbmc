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
    set_bit(must_bits[identifier], bit_nr);
    break;
  
  case CLEAR_MUST:
    clear_bit(must_bits[identifier], bit_nr);
    break;
  
  case SET_MAY:
    set_bit(may_bits[identifier], bit_nr);
    break;
  
  case CLEAR_MAY:
    clear_bit(may_bits[identifier], bit_nr);
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
  irep_idt id=object2id(lhs);
  if(!id.empty()) set_bit(id, bit_nr, mode);
}

/*******************************************************************\

Function: custom_bitvector_domaint::object2id

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

irep_idt custom_bitvector_domaint::object2id(const exprt &src)
{
  if(src.id()==ID_symbol)
  {
    return to_symbol_expr(src).get_identifier();
  }
  else if(src.id()==ID_dereference)
  {
    const exprt &op=to_dereference_expr(src).pointer();
    
    if(op.id()==ID_address_of)
    {
      return object2id(to_address_of_expr(op).object());
    }
    else if(op.id()==ID_typecast)
    {
      return object2id(dereference_exprt(to_typecast_expr(op).op()));
    }
    else
    {
      irep_idt op_id=object2id(op);
      if(op_id.empty())
        return irep_idt();
      else
        return '*'+id2string(op_id);
    }
  }
  else if(src.id()==ID_typecast)
    return object2id(to_typecast_expr(src).op());
  else
    return irep_idt();
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
  irep_idt id=object2id(lhs);
  if(!id.empty()) assign_lhs(id, vectors);
}

/*******************************************************************\

Function: custom_bitvector_domaint::assign_lhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::assign_lhs(
  const irep_idt &identifier,
  const vectorst &vectors)
{
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

/*******************************************************************\

Function: custom_bitvector_domaint::get_rhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

custom_bitvector_domaint::vectorst
  custom_bitvector_domaint::get_rhs(const irep_idt &identifier) const
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
  custom_bitvector_domaint::get_rhs(const exprt &rhs) const
{
  if(rhs.id()==ID_symbol ||
     rhs.id()==ID_dereference)
  {
    const irep_idt identifier=object2id(rhs);
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

Function: custom_bitvector_domaint::aliases

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

std::set<exprt> custom_bitvector_analysist::aliases(
  const exprt &src,
  locationt loc)
{
  if(src.id()==ID_symbol)
  {
    std::set<exprt> result;
    result.insert(src);
    return result;
  }
  else if(src.id()==ID_dereference)
  {
    exprt pointer=to_dereference_expr(src).pointer();
  
    std::set<exprt> pointer_set=
      local_may_alias_factory(loc).get(loc, pointer);

    std::set<exprt> result;

    for(std::set<exprt>::const_iterator
        p_it=pointer_set.begin();
        p_it!=pointer_set.end();
        p_it++)
    {
      result.insert(dereference_exprt(*p_it));
    }
    
    result.insert(src);
    
    return result;
  }
  else if(src.id()==ID_typecast)
  {
    return aliases(to_typecast_expr(src).op(), loc);
  }
  else
    return std::set<exprt>();
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
      std::set<exprt> lhs_set=cba.aliases(code_assign.lhs(), from);
        
      vectorst rhs_vectors=get_rhs(code_assign.rhs());
      
      for(std::set<exprt>::const_iterator
          l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
      {
        assign_lhs(*l_it, rhs_vectors);
      }
      
      // is it a pointer?
      if(code_assign.lhs().type().id()==ID_pointer)
      {
        dereference_exprt lhs_deref(code_assign.lhs());
        dereference_exprt rhs_deref(code_assign.rhs());
        vectorst rhs_vectors=get_rhs(rhs_deref);
        assign_lhs(lhs_deref, rhs_vectors);
      }
    }
    break;

  case DECL:
    {
      const code_declt &code_decl=to_code_decl(instruction.code);
      assign_lhs(code_decl.symbol(), vectorst());

      // is it a pointer?
      if(code_decl.symbol().type().id()==ID_pointer)
        assign_lhs(dereference_exprt(code_decl.symbol()), vectorst());
    }
    break;

  case DEAD:
    {
      const code_deadt &code_dead=to_code_dead(instruction.code);
      assign_lhs(code_dead.symbol(), vectorst());

      // is it a pointer?
      if(code_dead.symbol().type().id()==ID_pointer)
        assign_lhs(dereference_exprt(code_dead.symbol()), vectorst());
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
              {
                for(bitst::iterator b_it=may_bits.begin();
                    b_it!=may_bits.end();
                    b_it++)
                  clear_bit(b_it->second, bit_nr);

                // erase blank ones
                erase_blank_vectors(may_bits);
              }
              else if(mode==CLEAR_MUST)
              {
                for(bitst::iterator b_it=must_bits.begin();
                    b_it!=must_bits.end();
                    b_it++)
                  clear_bit(b_it->second, bit_nr);

                // erase blank ones
                erase_blank_vectors(must_bits);
              }
            }
            else
            {
              dereference_exprt deref(lhs);
              
              // may alias other stuff
              std::set<exprt> lhs_set=cba.aliases(deref, from);
              
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
    
  case GOTO:
    if(has_get_must_or_may(instruction.guard))
    {
      exprt guard=instruction.guard;
    
      if(to!=from->get_target()) guard.make_not();

      exprt result=eval(guard, cba);
      exprt result2=simplify_expr(result, ns);

      if(result2.is_false())
        make_bottom();
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
  erase_blank_vectors(may_bits);
  erase_blank_vectors(must_bits);

  return changed;
}

/*******************************************************************\

Function: custom_bitvector_domaint::erase_blank_vectors

  Inputs:

 Outputs:

 Purpose: erase blank bitvectors

\*******************************************************************/

void custom_bitvector_domaint::erase_blank_vectors(bitst &bits)
{
  for(bitst::iterator a_it=bits.begin();
      a_it!=bits.end();
      )
  {
    if(a_it->second==0)
      a_it=bits.erase(a_it);
    else
      a_it++;
  }
}

/*******************************************************************\

Function: custom_bitvector_domaint::has_get_must_or_may

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool custom_bitvector_domaint::has_get_must_or_may(const exprt &src)
{
  if(src.id()=="get_must" ||
     src.id()=="get_may")
    return true;
  
  forall_operands(it, src)
    if(has_get_must_or_may(*it)) return true;

  return false;
}

/*******************************************************************\

Function: custom_bitvector_domaint::eval

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

exprt custom_bitvector_domaint::eval(
  const exprt &src,
  custom_bitvector_analysist &custom_bitvector_analysis) const
{
  if(src.id()=="get_must" || src.id()=="get_may")
  {
    if(src.operands().size()==2)
    {
      unsigned bit_nr=
        custom_bitvector_analysis.get_bit_nr(src.op1());

      exprt pointer=src.op0();
      
      if(pointer.is_constant() &&
         to_constant_expr(pointer).get_value()==ID_NULL) // NULL means all
      {
        if(src.id()=="get_may")
        {
          for(custom_bitvector_domaint::bitst::const_iterator
              b_it=may_bits.begin();
              b_it!=may_bits.end();
              b_it++)
          {
            if(get_bit(b_it->second, bit_nr)) return true_exprt();
          }
          
          return false_exprt();
        }
        else if(src.id()=="get_must")
        {
          return false_exprt();
        }
        else
          return src;
      }
      else
      {
        custom_bitvector_domaint::vectorst v=
          get_rhs(dereference_exprt(pointer));

        bool value=false;

        if(src.id()=="get_must")
          value=get_bit(v.must_bits, bit_nr);
        else if(src.id()=="get_may")
          value=get_bit(v.may_bits, bit_nr);

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
      *it=eval(*it, custom_bitvector_analysis);
  
    return tmp;
  }
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
      if(!custom_bitvector_domaint::has_get_must_or_may(i_it->guard))
        continue;

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
