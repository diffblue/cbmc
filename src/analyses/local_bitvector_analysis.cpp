/*******************************************************************\

Module: Field-insensitive, location-sensitive may-alias analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iterator>
#include <algorithm>

#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/expr_util.h>

#include <ansi-c/c_types.h>
#include <langapi/language_util.h>

#include "local_bitvector_analysis.h"

/*******************************************************************\

Function: local_bitvector_analysist::flagst::print

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void local_bitvector_analysist::flagst::print(std::ostream &out) const
{
  if(is_unknown()) out << "+unknown";
  if(is_uninitialized()) out << "+uninitialized";
  if(is_uses_offset()) out << "+uses_offset";
  if(is_dynamic_local()) out << "+dynamic_local";
  if(is_dynamic_heap()) out << "+dynamic_heap";
  if(is_null()) out << "+null";
  if(is_static_lifetime()) out << "+static_lifetime";
  if(is_integer_address()) out << "+integer_address";
}

/*******************************************************************\

Function: local_bitvector_analysist::loc_infot::merge

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool local_bitvector_analysist::loc_infot::merge(const loc_infot &src)
{
  bool result=false;
  
  std::size_t max_index=
    std::max(src.points_to.size(), points_to.size());

  for(std::size_t i=0; i<max_index; i++)
  {
    if(points_to[i].merge(src.points_to[i]))
      result=true;
  }
  
  return result;
}

/*******************************************************************\

Function: local_bitvector_analysist::is_tracked

  Inputs:

 Outputs: return 'true' iff we track the object with given
          identifier

 Purpose:

\*******************************************************************/

bool local_bitvector_analysist::is_tracked(const irep_idt &identifier)
{
  localst::locals_mapt::const_iterator it=locals.locals_map.find(identifier);
  if(it==locals.locals_map.end()) return false;
  if(it->second.id()!=ID_pointer) return false;
  if(dirty(identifier)) return false;
  return true;
}

/*******************************************************************\

Function: local_bitvector_analysist::assign_lhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void local_bitvector_analysist::assign_lhs(
  const exprt &lhs,
  const exprt &rhs,
  const loc_infot &loc_info_src,
  loc_infot &loc_info_dest)
{
  if(lhs.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(lhs).get_identifier();

    if(is_tracked(identifier))
    {
      unsigned dest_pointer=pointers.number(identifier);
      flagst rhs_flags=get_rec(rhs, loc_info_src);
      loc_info_dest.points_to[dest_pointer]=rhs_flags;
    }
  }
  else if(lhs.id()==ID_dereference)
  {
  }
  else if(lhs.id()==ID_index)
  {
    assign_lhs(to_index_expr(lhs).array(), rhs, loc_info_src, loc_info_dest);
  }
  else if(lhs.id()==ID_member)
  {
    assign_lhs(to_member_expr(lhs).struct_op(), rhs, loc_info_src, loc_info_dest);
  }
  else if(lhs.id()==ID_typecast)
  {
    assign_lhs(to_typecast_expr(lhs).op(), rhs, loc_info_src, loc_info_dest);
  }
  else if(lhs.id()==ID_if)
  {
    assign_lhs(to_if_expr(lhs).true_case(), rhs, loc_info_src, loc_info_dest);
    assign_lhs(to_if_expr(lhs).false_case(), rhs, loc_info_src, loc_info_dest);
  }
}
 
/*******************************************************************\

Function: local_bitvector_analysist::get

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

local_bitvector_analysist::flagst local_bitvector_analysist::get(
  const goto_programt::const_targett t,
  const exprt &rhs)
{
  local_cfgt::loc_mapt::const_iterator loc_it=cfg.loc_map.find(t);
  
  assert(loc_it!=cfg.loc_map.end());
  
  const loc_infot &loc_info_src=loc_infos[loc_it->second];

  return get_rec(rhs, loc_info_src);
}

/*******************************************************************\

Function: local_bitvector_analysist::get_rec

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

local_bitvector_analysist::flagst local_bitvector_analysist::get_rec(
  const exprt &rhs,
  const loc_infot &loc_info_src)
{
  if(rhs.id()==ID_constant)
  {
    if(rhs.is_zero())
      return flagst::mk_null();
    else
      return flagst::mk_integer_address();
  }
  else if(rhs.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(rhs).get_identifier();
    if(is_tracked(identifier))
    {
      unsigned src_pointer=pointers.number(identifier);
      return loc_info_src.points_to[src_pointer];
    }
    else
      return flagst::mk_unknown();
  }
  else if(rhs.id()==ID_address_of)
  {
    const exprt &object=to_address_of_expr(rhs).object();
    
    if(object.id()==ID_symbol)
    {
      if(locals.is_local(to_symbol_expr(object).get_identifier()))
        return flagst::mk_dynamic_local();
      else
        return flagst::mk_static_lifetime();
    }
    else if(object.id()==ID_index)
    {
      const index_exprt &index_expr=to_index_expr(object);
      if(index_expr.array().id()==ID_symbol)
      {
        if(locals.is_local(
          to_symbol_expr(index_expr.array()).get_identifier()))
          return flagst::mk_dynamic_local() | flagst::mk_uses_offset();
        else
          return flagst::mk_static_lifetime() | flagst::mk_uses_offset();
      }
      else
        return flagst::mk_unknown();
    }
    else
      return flagst::mk_unknown();
  }
  else if(rhs.id()==ID_typecast)
  {
    return get_rec(to_typecast_expr(rhs).op(), loc_info_src);
  }
  else if(rhs.id()==ID_uninitialized)
  {
    return flagst::mk_uninitialized();
  }
  else if(rhs.id()==ID_plus)
  {
    if(rhs.operands().size()>=3)
    {
      return get_rec(make_binary(rhs), loc_info_src);
    }
    else if(rhs.operands().size()==2)
    {
      // one must be pointer, one an integer
      if(rhs.op0().type().id()==ID_pointer)
      {
        return get_rec(rhs.op0(), loc_info_src) |
               flagst::mk_uses_offset();
      }
      else if(rhs.op1().type().id()==ID_pointer)
      {
        return get_rec(rhs.op1(), loc_info_src) |
               flagst::mk_uses_offset();
      }
      else
        return flagst::mk_unknown();
    }
    else
      return flagst::mk_unknown();
  }
  else if(rhs.id()==ID_minus)
  {
    if(rhs.op0().type().id()==ID_pointer)
    {
      return get_rec(rhs.op0(), loc_info_src) |
             flagst::mk_uses_offset();
    }
    else
      return flagst::mk_unknown();
  }
  else if(rhs.id()==ID_member)
  {
    return flagst::mk_unknown();
  }
  else if(rhs.id()==ID_index)
  {
    return flagst::mk_unknown();
  }
  else if(rhs.id()==ID_dereference)
  {
    return flagst::mk_unknown();
  }
  else if(rhs.id()==ID_side_effect)
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(rhs);
    const irep_idt &statement=side_effect_expr.get_statement();

    if(statement==ID_malloc)
      return flagst::mk_dynamic_heap();
    else
      return flagst::mk_unknown();
  }
  else
    return flagst::mk_unknown();
}
 
/*******************************************************************\

Function: local_bitvector_analysist::build

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void local_bitvector_analysist::build(const goto_functiont &goto_function)
{
  if(cfg.nodes.empty()) return;

  work_queuet work_queue;
  work_queue.push(0);  
  
  loc_infos.resize(cfg.nodes.size());
  
  // Gather the objects we track, and
  // feed in sufficiently bad defaults for their value
  // in the entry location.
  for(localst::locals_mapt::const_iterator
      it=locals.locals_map.begin();
      it!=locals.locals_map.end();
      it++)
    if(is_tracked(it->first))
      loc_infos[0].points_to[pointers.number(it->first)]=flagst::mk_unknown();

  while(!work_queue.empty())
  {
    unsigned loc_nr=work_queue.top();
    const local_cfgt::nodet &node=cfg.nodes[loc_nr];
    const goto_programt::instructiont &instruction=*node.t;
    work_queue.pop();
    
    const loc_infot &loc_info_src=loc_infos[loc_nr];
    loc_infot loc_info_dest=loc_infos[loc_nr];
    
    switch(instruction.type)
    {
    case ASSIGN:
      {
        const code_assignt &code_assign=to_code_assign(instruction.code);
        assign_lhs(code_assign.lhs(), code_assign.rhs(), loc_info_src, loc_info_dest);
      }
      break;

    case DECL:
      {
        const code_declt &code_decl=to_code_decl(instruction.code);
        assign_lhs(code_decl.symbol(), exprt(ID_uninitialized), loc_info_src, loc_info_dest);
      }
      break;

    case DEAD:
      {
        const code_deadt &code_dead=to_code_dead(instruction.code);
        assign_lhs(code_dead.symbol(), exprt(ID_uninitialized), loc_info_src, loc_info_dest);
      }
      break;

    case FUNCTION_CALL:
      {
        const code_function_callt &code_function_call=to_code_function_call(instruction.code);
        if(code_function_call.lhs().is_not_nil())
          assign_lhs(code_function_call.lhs(), nil_exprt(), loc_info_src, loc_info_dest);
      }
      break;

    default:;
    }

    for(local_cfgt::successorst::const_iterator
        it=node.successors.begin();
        it!=node.successors.end();
        it++)
    {
      if(loc_infos[*it].merge(loc_info_dest))
        work_queue.push(*it);
    }
  }
}

/*******************************************************************\

Function: local_bitvector_analysist::output

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void local_bitvector_analysist::output(
  std::ostream &out,
  const goto_functiont &goto_function,
  const namespacet &ns) const
{
  unsigned l=0;

  forall_goto_program_instructions(i_it, goto_function.body)
  {
    out << "**** " << i_it->source_location << "\n";

    const loc_infot &loc_info=loc_infos[l];

    for(points_tot::const_iterator
        p_it=loc_info.points_to.begin();
        p_it!=loc_info.points_to.end();
        p_it++)
    {
      out << "  " << pointers[p_it-loc_info.points_to.begin()]
          << ": "
          << *p_it
          << "\n";
    }

    out << "\n";
    goto_function.body.output_instruction(ns, "", out, i_it);
    out << "\n";
    
    l++;
  }
}

