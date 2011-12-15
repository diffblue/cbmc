/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <i2string.h>
#include <std_expr.h>

#include "goto_symex_state.h"

/*******************************************************************\

Function: goto_symex_statet::goto_symex_statet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_symex_statet::goto_symex_statet()
{
  depth=0;
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

  source.is_set=true;
  source.pc=body.instructions.begin();
  top().end_of_function=--body.instructions.end();
  top().calling_location=top().end_of_function;
}

/*******************************************************************\

Function: goto_symex_statet::name_frame

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string goto_symex_statet::level1t::name(
  const irep_idt &identifier,
  unsigned frame) const
{
  return id2string(identifier)+"@"+i2string(frame);
}

/*******************************************************************\

Function: goto_symex_statet::name_count

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string goto_symex_statet::level2t::name(
  const irep_idt &identifier,
  unsigned count) const
{
  return id2string(identifier)+"#"+i2string(count);
}

/*******************************************************************\

Function: goto_symex_statet::current_number

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned goto_symex_statet::level2t::current_number(
  const irep_idt &identifier) const
{
  current_namest::const_iterator it=current_names.find(identifier);
  if(it==current_names.end()) return 0;
  return it->second.count;
}

/*******************************************************************\

Function: goto_symex_statet::level1t::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string goto_symex_statet::level1t::operator()(
  const irep_idt &identifier) const
{
  current_namest::const_iterator it=
    current_names.find(identifier);

  if(it==current_names.end())
    return id2string(identifier);

  return name(identifier, it->second);
}

/*******************************************************************\

Function: goto_symex_statet::level2t::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string goto_symex_statet::level2t::operator()(
  const irep_idt &identifier) const
{
  current_namest::const_iterator it=
    current_names.find(identifier);

  if(it==current_names.end())
    return name(identifier, 0);

  return name(identifier, it->second.count);
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
  symbol_exprt &lhs,
  const exprt &rhs,
  const namespacet &ns,
  bool record_value)
{
  assert(lhs.id()==ID_symbol);

  // the type might need renaming
  rename(lhs.type(), ns);

  const irep_idt &identifier=lhs.get_identifier();
    
  // identifier should be l0 or l1, make sure it's l1
  
  const std::string l1_identifier=top().level1(identifier);

  // do the l2 renaming 
  level2t::valuet &entry=level2.current_names[l1_identifier];

  entry.count++;
    
  level2.rename(l1_identifier, entry.count);
  
  lhs.set_identifier(level2.name(l1_identifier, entry.count));
  
  if(record_value)
  {
    // for constant propagation
    
    if(constant_propagation(rhs))
      entry.constant=rhs;
    else
      entry.constant.make_nil();
  }
  else
    entry.constant.make_nil();
      
  {
    // update value sets
    value_sett::expr_sett rhs_value_set;
    exprt l1_rhs(rhs);
    level2.get_original_name(l1_rhs);

    symbol_exprt l1_lhs(l1_identifier, lhs.type());

    value_set.assign(l1_lhs, l1_rhs, ns);  
  }
  
  #if 0
  std::cout << "Assigning " << identifier << std::endl;
  value_set.output(ns, std::cout);
  std::cout << "**********************" << std::endl;
  #endif
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
  
  rename(expr.type(), ns);

  if(expr.id()==ID_symbol)
  {
    if(level==L1)
    {
      top().level1.rename(expr);
    }
    else if(level==L2)
    {
      top().level1.rename(expr);
      level2.rename(expr);
    }
  }
  else if(expr.id()==ID_address_of)
  {
    assert(expr.operands().size()==1);
    rename_address(expr.op0(), ns);
  }
  else
  {
    // do this recursively
    Forall_operands(it, expr)
      rename(*it, ns, level);
  }
}

/*******************************************************************\

Function: goto_symex_statet::rename_address

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::rename_address(
  exprt &expr,
  const namespacet &ns)
{
  // rename all the symbols with their last known value

  rename(expr.type(), ns);

  if(expr.id()==ID_symbol)
  {
    // only do L1!
    top().level1.rename(expr);
  }
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size()==2);
    rename_address(expr.op0(), ns);
    
    // the index is not an address
    rename(expr.op1(), ns);
  }
  else if(expr.id()==ID_if)
  {
    // the condition is not an address
    if_exprt &if_expr=to_if_expr(expr);
    rename(if_expr.cond(), ns);
    rename_address(if_expr.true_case(), ns);
    rename_address(if_expr.false_case(), ns);
  }
  else if(expr.id()==ID_member)
  {
    rename_address(to_member_expr(expr).struct_op(), ns);
  }
  else
  {
    // do this recursively; we assume here
    // that all the operands are addresses
    Forall_operands(it, expr)
      rename_address(*it, ns);
  }
}

/*******************************************************************\

Function: goto_symex_statet::level1t::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::level1t::rename(exprt &expr)
{
  // rename all the symbols with their last known value
  
  rename(expr.type());

  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);

    // first see if it's already an l1 name
    
    if(original_identifiers.find(identifier)!=
       original_identifiers.end())
      return;
    
    const current_namest::const_iterator it=
      current_names.find(identifier);
    
    if(it!=current_names.end())
      expr.set(ID_identifier, name(identifier, it->second));
  }
  else if(expr.id()==ID_address_of)
  {
    assert(expr.operands().size()==1);
    rename(expr.op0());
  }
  else
  {
    // do this recursively
    Forall_operands(it, expr)
      rename(*it);
  }
}
/*******************************************************************\

Function: goto_symex_statet::level2t::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::level2t::rename(exprt &expr)
{
  // rename all the symbols with their last known value
  
  rename(expr.type());

  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);
    
    // first see if it's already an l2 name

    if(original_identifiers.find(identifier)!=
       original_identifiers.end())
      return;
    
    const current_namest::const_iterator it=
      current_names.find(identifier);
    
    if(it!=current_names.end())
    {
      if(it->second.constant.is_not_nil())
        expr=it->second.constant;
      else
        expr.set(ID_identifier, name(identifier, it->second.count));
    }
    else
    {
      std::string new_identifier=name(identifier, 0);
      original_identifiers[new_identifier]=identifier;
      expr.set(ID_identifier, new_identifier);
    }
  }
  else if(expr.id()==ID_address_of)
  {
    // do nothing
  }
  else
  {
    // do this recursively
    Forall_operands(it, expr)
      rename(*it);
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
  const namespacet &ns)
{
  // rename all the symbols with their last known value

  if(type.id()==ID_array)
  {
    rename(type.subtype(), ns);
    rename(static_cast<exprt &>(type.add(ID_size)), ns);
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
    const symbolt &symbol=ns.lookup(type.get(ID_identifier));
    type=symbol.type;
    rename(type, ns);
  }
}

/*******************************************************************\

Function: goto_symex_statet::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::renaming_levelt::rename(typet &type)
{
  // rename all the symbols with their last known value

  if(type.id()==ID_array)
  {
    rename(type.subtype());
    rename((exprt &)type.add(ID_size));
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union ||
          type.id()==ID_class)
  {
    // TODO
  }
  else if(type.id()==ID_pointer)
  {
    rename(type.subtype());
  }
}

/*******************************************************************\

Function: goto_symex_statet::get_original_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::get_original_name(exprt &expr) const
{
  Forall_operands(it, expr)
    get_original_name(*it);

  if(expr.id()==ID_symbol)
  {
    level2.get_original_name(expr);
    top().level1.get_original_name(expr);
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
    get_original_name((exprt &)type.add(ID_size));
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
  // rename all the symbols with their last known value

  if(type.id()==ID_array)
  {
    get_original_name(type.subtype());
    get_original_name((exprt &)type.add(ID_size));
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

Function: goto_symex_statet::get_original_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const irep_idt &goto_symex_statet::get_original_name(
  const irep_idt &identifier) const
{
  return top().level1.get_original_name(
         level2.get_original_name(identifier));
}

/*******************************************************************\

Function: goto_symex_statet::level1t::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::level1t::print(std::ostream &out) const
{
  for(current_namest::const_iterator
      it=current_names.begin();
      it!=current_names.end();
      it++)
    out << it->first << " --> "
        << name(it->first, it->second) << std::endl;
}

/*******************************************************************\

Function: goto_symex_statet::level2t::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symex_statet::level2t::print(std::ostream &out) const
{
  for(current_namest::const_iterator
      it=current_names.begin();
      it!=current_names.end();
      it++)
    out << it->first << " --> "
        << name(it->first, it->second.count) << std::endl;
}

