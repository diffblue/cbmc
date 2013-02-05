/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <cassert>

#include <std_expr.h>
#include <prefix.h>

#include "goto_symex_state.h"

/*******************************************************************\

Function: goto_symex_statet::goto_symex_statet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_symex_statet::goto_symex_statet():
  depth(0),
  atomic_section_count(0)
{
  threads.resize(1);
  new_frame();
}

/*******************************************************************\

Function: goto_symex_statet::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::initialize(const goto_functionst &goto_functions)
{
  goto_functionst::function_mapt::const_iterator it=
    goto_functions.function_map.find(ID_main);

  if(it==goto_functions.function_map.end())
    throw "main symbol not found; please set an entry point";

  const goto_programt &body=it->second.body;

  source=symex_targett::sourcet(body);
  top().end_of_function=--body.instructions.end();
  top().calling_location.pc=top().end_of_function;
}

/*******************************************************************\

Function: goto_symex_statet::level0t::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt goto_symex_statet::level0t::operator()(
  const irep_idt &identifier,
  const namespacet &ns,
  unsigned thread_nr)
{
  // already renamed?
  if(original_identifiers.find(identifier)!=original_identifiers.end())
    return identifier;

  // guards are not L0-renamed
  if(identifier=="goto_symex::\\guard")
  {
    original_identifiers[identifier]=identifier;
    return identifier;
  }

  const symbolt *s;
  if(ns.lookup(identifier, s))
  {
    std::cerr << "level0: failed to find " << identifier << std::endl;
    abort();
  }
  
  // don't rename shared variables or functions
  if(s->type.id()==ID_code ||
     s->is_shared())
  {
    original_identifiers[identifier]=identifier;
    return identifier;
  }

  // rename!    
  irep_idt new_identifier=name(identifier, thread_nr);
  
  // remember that
  original_identifiers[new_identifier]=identifier;

  return new_identifier;
}

/*******************************************************************\

Function: goto_symex_statet::renaming_levelt::current_count

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned goto_symex_statet::renaming_levelt::current_count(
  const irep_idt &identifier) const
{
  current_namest::const_iterator it=current_names.find(identifier);
  return it==current_names.end()?0:it->second;
}

/*******************************************************************\

Function: goto_symex_statet::constant_propagation

  Inputs:

 Outputs:

 Purpose: This function determines what expressions are to
          be propagated as "constants"

\*******************************************************************/

bool goto_symex_statet::constant_propagation(const exprt &expr) const
{
  if(expr.is_constant())
    return true;
  
  if(expr.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr=to_address_of_expr(expr);

    return constant_propagation_reference(address_of_expr.object());
  }
  else if(expr.id()==ID_typecast)
  {
    const typecast_exprt &typecast_expr=to_typecast_expr(expr);

    return constant_propagation(typecast_expr.op());
  }
  else if(expr.id()==ID_plus)
  {
    forall_operands(it, expr)
      if(!constant_propagation(*it))
        return false;

    return true;
  }
  else if(expr.id()==ID_mult)
  {
    // propagate stuff with sizeof in it
    forall_operands(it, expr)
      if(it->find(ID_C_c_sizeof_type).is_not_nil())
        return true;

    return true;
  }
  else if(expr.id()==ID_array)
  {
    forall_operands(it, expr)
      if(!constant_propagation(*it))
        return false;
        
    return true;
  }
  else if(expr.id()==ID_array_of)
  {
    return constant_propagation(expr.op0());
  }
  else if(expr.id()==ID_with)
  {
    // this is bad
    /*
    forall_operands(it, expr)
      if(!constant_propagation(expr.op0()))
        return false;

    return true;
    */
    return false;
  }
  else if(expr.id()==ID_struct)
  {
    forall_operands(it, expr)
      if(!constant_propagation(*it))
        return false;

    return true;
  }

  return false;
}

/*******************************************************************\

Function: goto_symex_statet::constant_propagation_reference

  Inputs:

 Outputs:

 Purpose: this function determines which reference-typed
          expressions are constant

\*******************************************************************/

bool goto_symex_statet::constant_propagation_reference(const exprt &expr) const
{
  if(expr.id()==ID_symbol)
    return true;
  else if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);

    return constant_propagation_reference(index_expr.array()) &&
           constant_propagation(index_expr.index());
  }
  else if(expr.id()==ID_member)
  {
    if(expr.operands().size()!=1)
      throw "member expects one operand";

    return constant_propagation_reference(expr.op0());
  }
  else if(expr.id()==ID_string_constant)
    return true;

  return false;
}

/*******************************************************************\

Function: goto_symex_statet::assignment

  Inputs:

 Outputs:

 Purpose: write to a variable

\*******************************************************************/

void goto_symex_statet::assignment(
  symbol_exprt &lhs, // L0/L1
  const exprt &rhs,  // L2
  const namespacet &ns,
  bool record_value)
{
  assert(lhs.id()==ID_symbol);

  // the type might need renaming
  rename(lhs.type(), ns);

  irep_idt identifier=lhs.get_identifier();
    
  // identifier should be l0 or l1, make sure it's l1
  irep_idt l1_identifier=level1(identifier);

  #if 0  
  assert(l1_identifier != get_original_name(l1_identifier)
      || l1_identifier=="goto_symex::\\guard"
      || is_global(ns.lookup(l1_identifier))
      || has_prefix(l1_identifier.as_string(), "symex::invalid_object")
      || has_prefix(l1_identifier.as_string(), "symex_dynamic::dynamic_object"));
  #endif

  // do the l2 renaming 
  irep_idt new_l2_name=level2.increase_counter(l1_identifier);
  lhs.set_identifier(new_l2_name);

  // in case we happen to be multi-threaded, record the memory access
  {
    irep_idt orig_identifier=get_original_name(l1_identifier);
    if(orig_identifier!="goto_symex::\\guard" &&
       ns.lookup(orig_identifier).is_shared())
    {
    }
  }

  // for value propagation -- the RHS is L2
  
  if(record_value && constant_propagation(rhs))
    propagation.values[l1_identifier]=rhs;
  else
    propagation.remove(l1_identifier);
      
  {
    // update value sets
    value_sett::expr_sett rhs_value_set;
    exprt l1_rhs(rhs);
    level2.get_original_name(l1_rhs);

    symbol_exprt l1_lhs(l1_identifier, lhs.type());
    level2.get_original_name(l1_lhs.type());

    value_set.assign(l1_lhs, l1_rhs, ns);  
  }
  
  #if 0
  std::cout << "Assigning " << identifier << std::endl;
  value_set.output(ns, std::cout);
  std::cout << "**********************" << std::endl;
  #endif
}

/*******************************************************************\

Function: goto_symex_statet::propagationt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::propagationt::operator()(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    valuest::const_iterator it=
      values.find(to_symbol_expr(expr).get_identifier());
    if(it!=values.end())
      expr=it->second;
  }
  else if(expr.id()==ID_address_of)
  {
    // ignore
  }
  else
  {
    // do this recursively
    Forall_operands(it, expr)
      operator()(*it);
  }
}

/*******************************************************************\

Function: goto_symex_statet::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt goto_symex_statet::rename(
  const irep_idt &identifier,
  const namespacet &ns,
  levelt level)
{
  switch(level)
  {
  case L0:
    return level0(identifier, ns, source.thread_nr);
    
  case L1:
    {
      if(level2.is_renamed(identifier)) return identifier;
      if(level1.is_renamed(identifier)) return identifier;
      irep_idt l0_identifier=level0(identifier, ns, source.thread_nr);
      return level1(l0_identifier);
    }
  
  case L2:
    {
      if(level2.is_renamed(identifier)) return identifier;
      irep_idt l0_identifier=level0(identifier, ns, source.thread_nr);
      irep_idt l1_identifier=level1(l0_identifier);
      return level2(l1_identifier); // L2
    }
    
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: goto_symex_statet::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::rename(
  exprt &expr,
  const namespacet &ns,
  levelt level)
{
  // rename all the symbols with their last known value
  
  rename(expr.type(), ns, level);

  if(expr.id()==ID_symbol)
  {
    const irep_idt identifier=to_symbol_expr(expr).get_identifier();

    if(level==L0 || level==L1)
    {
      const irep_idt new_name=rename(identifier, ns, level);
      to_symbol_expr(expr).set_identifier(new_name);
    }  
    else if(level==L2)
    {
      if(!level2.is_renamed(identifier))
      {
        if(l2_thread_encoding(expr, ns))
        {
          // done
        }
        else
        {
          irep_idt l1_identifier=rename(identifier, ns, L1);

          // We also consider propagation if we go up to L2.
          // L1 identifiers are used for propagation!
          propagationt::valuest::const_iterator p_it=
            propagation.values.find(l1_identifier);

          if(p_it!=propagation.values.end())
            expr=p_it->second; // already L2
          else
          {
            const irep_idt new_name=level2(l1_identifier); // L2
            to_symbol_expr(expr).set_identifier(new_name);
          }
        }
      }
    }
    
  }
  else if(expr.id()==ID_address_of)
  {
    assert(expr.operands().size()==1);
    rename_address(expr.op0(), ns, level);
  }
  else
  {
    // do this recursively
    Forall_operands(it, expr)
      rename(*it, ns, level);
  }
}

/*******************************************************************\

Function: goto_symex_statet::l2_thread_encoding

  Inputs:

 Outputs:

 Purpose: thread encoding

\*******************************************************************/

bool goto_symex_statet::l2_thread_encoding(
  exprt &expr,
  const namespacet &ns)
{
  #if 0
  // do we have threads at all?
  if(threads.size()<=1) return false;

  irep_idt original_identifier=get_original_name(identifier);
  if(ns.lookup(original_identifier).is_shared() &&
     threads.size()>1)
  {
    // take a fresh l2 name
    const irep_idt new_name=level2.increase_counter(l1_identifier);
    to_symbol_expr(expr).set_identifier(new_name);
    return true;
  }
  #else
  return false;
  #endif
}

/*******************************************************************\

Function: goto_symex_statet::rename_address

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::rename_address(
  exprt &expr,
  const namespacet &ns,
  levelt level)
{
  // only do L1!
  rename(expr.type(), ns, L1);

  if(expr.id()==ID_symbol)
  {
    // only do L1!
    irep_idt identifier=to_symbol_expr(expr).get_identifier();
    identifier=rename(identifier, ns, L1);
    to_symbol_expr(expr).set_identifier(identifier);
  }
  else
  {
    if(expr.id()==ID_index)
    {
      assert(expr.operands().size()==2);
      rename_address(expr.op0(), ns, level);

      // the index is not an address
      rename(expr.op1(), ns, level);
    }
    else if(expr.id()==ID_if)
    {
      // the condition is not an address
      if_exprt &if_expr=to_if_expr(expr);
      rename(if_expr.cond(), ns, level);
      rename_address(if_expr.true_case(), ns, level);
      rename_address(if_expr.false_case(), ns, level);
    }
    else if(expr.id()==ID_member)
    {
      rename_address(to_member_expr(expr).struct_op(), ns, level);
    }
    else
    {
      // do this recursively; we assume here
      // that all the operands are addresses
      Forall_operands(it, expr)
        rename_address(*it, ns, level);
    }
  }
}

/*******************************************************************\

Function: goto_symex_statet::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::rename(
  typet &type,
  const namespacet &ns,
  levelt level)
{
  // rename all the symbols with their last known value
  // to the given level

  if(type.id()==ID_array)
  {
    rename(type.subtype(), ns, level);
    rename(to_array_type(type).size(), ns, level);
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union ||
          type.id()==ID_class)
  {
    // TODO
  }
  else if(type.id()==ID_pointer)
  {
    // rename(type.subtype(), ns);
    // don't do this, or it might get cyclic
  }
  else if(type.id()==ID_symbol)
  {
    const symbolt &symbol=
      ns.lookup(to_symbol_type(type).get_identifier());
    type=symbol.type;
    rename(type, ns, level);
  }
}

/*******************************************************************\

Function: goto_symex_statet::renaming_levelt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::renaming_levelt::print(std::ostream &out) const
{
  for(current_namest::const_iterator
      it=current_names.begin();
      it!=current_names.end();
      it++)
    out << it->first << " --> "
        << name(it->first, it->second) << std::endl;
}

/*******************************************************************\

Function: goto_symex_statet::get_original_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::get_original_name(exprt &expr) const
{
  get_original_name(expr.type());

  Forall_operands(it, expr)
    get_original_name(*it);

  if(expr.id()==ID_symbol)
  {
    level2.get_original_name(expr);
    level1.get_original_name(expr);
    level0.get_original_name(expr);
  }
}

/*******************************************************************\

Function: goto_symex_statet::renaming_levelt::get_original_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::renaming_levelt::get_original_name(exprt &expr) const
{
  get_original_name(expr.type());

  Forall_operands(it, expr)
    get_original_name(*it);

  if(expr.id()==ID_symbol)
  {
    original_identifierst::const_iterator it=
      original_identifiers.find(expr.get(ID_identifier));
    if(it==original_identifiers.end()) return;
    assert(it->second!="");
    expr.set(ID_identifier, it->second);
  }
}

/*******************************************************************\

Function: goto_symex_statet::renaming_levelt::get_original_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const irep_idt &goto_symex_statet::renaming_levelt::get_original_name(
  const irep_idt &identifier) const
{
  original_identifierst::const_iterator it=
    original_identifiers.find(identifier);
  if(it==original_identifiers.end()) return identifier;
  return it->second;
}

 /*******************************************************************\
 
Function: goto_symex_statet::get_original_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::get_original_name(typet &type) const
{
  // rename all the symbols with their last known value

  if(type.id()==ID_array)
  {
    get_original_name(type.subtype());
    get_original_name(to_array_type(type).size());
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union ||
          type.id()==ID_class)
  {
    // TODO
  }
  else if(type.id()==ID_pointer)
  {
    get_original_name(type.subtype());
  }
}

/*******************************************************************\

Function: goto_symex_statet::renaming_levelt::get_original_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::renaming_levelt::get_original_name(typet &type) const
{
  // rename all the symbols back to their original name

  if(type.id()==ID_array)
  {
    get_original_name(type.subtype());
    get_original_name(to_array_type(type).size());
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union ||
          type.id()==ID_class)
  {
    // TODO
  }
  else if(type.id()==ID_pointer)
  {
    get_original_name(type.subtype());
  }
}

/*******************************************************************\

Function: goto_symex_statet::get_original_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const irep_idt &goto_symex_statet::get_original_name(
  const irep_idt &identifier) const
{
  return level0.get_original_name(
         level1.get_original_name(
         level2.get_original_name(identifier)));
}

/*******************************************************************\

Function: goto_symex_statet::switch_to_thread

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::switch_to_thread(unsigned t)
{
  assert(source.thread_nr<threads.size());
  assert(t<threads.size());
  
  // save PC
  threads[source.thread_nr].pc=source.pc;

  // get new PC
  source.thread_nr=t;
  source.pc=threads[t].pc;
  
  guard=threads[t].guard;
}
