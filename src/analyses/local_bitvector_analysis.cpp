/*******************************************************************\

Module: Field-insensitive, location-sensitive may-alias analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Field-insensitive, location-sensitive may-alias analysis

#include "local_bitvector_analysis.h"

#include <algorithm>

#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

void local_bitvector_analysist::flagst::print(std::ostream &out) const
{
  if(is_unknown())
    out << "+unknown";
  if(is_uninitialized())
    out << "+uninitialized";
  if(is_uses_offset())
    out << "+uses_offset";
  if(is_dynamic_local())
    out << "+dynamic_local";
  if(is_dynamic_heap())
    out << "+dynamic_heap";
  if(is_null())
    out << "+null";
  if(is_static_lifetime())
    out << "+static_lifetime";
  if(is_integer_address())
    out << "+integer_address";
}

bool local_bitvector_analysist::merge(points_tot &a, points_tot &b)
{
  bool result=false;

  std::size_t max_index=
    std::max(a.size(), b.size());

  for(std::size_t i=0; i<max_index; i++)
  {
    if(a[i].merge(b[i]))
      result=true;
  }

  return result;
}

/// \return return 'true' iff we track the object with given identifier
bool local_bitvector_analysist::is_tracked(const irep_idt &identifier)
{
  localst::locals_sett::const_iterator it = locals.locals.find(identifier);
  return it != locals.locals.end() && ns.lookup(*it).type.id() == ID_pointer &&
         !dirty(identifier);
}

void local_bitvector_analysist::assign_lhs(
  const exprt &lhs,
  const exprt &rhs,
  points_tot &loc_info_src,
  points_tot &loc_info_dest)
{
  if(lhs.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(lhs).get_identifier();

    if(is_tracked(identifier))
    {
      unsigned dest_pointer=pointers.number(identifier);
      flagst rhs_flags=get_rec(rhs, loc_info_src);
      loc_info_dest[dest_pointer]=rhs_flags;
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
    assign_lhs(
      to_member_expr(lhs).struct_op(), rhs, loc_info_src, loc_info_dest);
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

local_bitvector_analysist::flagst local_bitvector_analysist::get(
  const goto_programt::const_targett t,
  const exprt &rhs)
{
  local_cfgt::loc_mapt::const_iterator loc_it=cfg.loc_map.find(t);

  assert(loc_it!=cfg.loc_map.end());

  return get_rec(rhs, loc_infos[loc_it->second]);
}

local_bitvector_analysist::flagst local_bitvector_analysist::get_rec(
  const exprt &rhs,
  points_tot &loc_info_src)
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
      return loc_info_src[src_pointer];
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
    const auto &plus_expr = to_plus_expr(rhs);

    if(plus_expr.operands().size() >= 3)
    {
      DATA_INVARIANT(
        plus_expr.op0().type().id() == ID_pointer,
        "pointer in pointer-typed sum must be op0");
      return get_rec(plus_expr.op0(), loc_info_src) | flagst::mk_uses_offset();
    }
    else if(plus_expr.operands().size() == 2)
    {
      // one must be pointer, one an integer
      if(plus_expr.op0().type().id() == ID_pointer)
      {
        return get_rec(plus_expr.op0(), loc_info_src) |
               flagst::mk_uses_offset();
      }
      else if(plus_expr.op1().type().id() == ID_pointer)
      {
        return get_rec(plus_expr.op1(), loc_info_src) |
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
    const auto &op0 = to_minus_expr(rhs).op0();

    if(op0.type().id() == ID_pointer)
    {
      return get_rec(op0, loc_info_src) | flagst::mk_uses_offset();
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

    if(statement==ID_allocate)
      return flagst::mk_dynamic_heap();
    else
      return flagst::mk_unknown();
  }
  else
    return flagst::mk_unknown();
}

void local_bitvector_analysist::build()
{
  if(cfg.nodes.empty())
    return;

  std::set<unsigned> work_queue;
  work_queue.insert(0);

  loc_infos.resize(cfg.nodes.size());

  // Gather the objects we track, and
  // feed in sufficiently bad defaults for their value
  // in the entry location.
  for(const auto &local : locals.locals)
  {
    if(is_tracked(local))
      loc_infos[0][pointers.number(local)] = flagst::mk_unknown();
  }

  while(!work_queue.empty())
  {
    unsigned loc_nr = *work_queue.begin();
    const local_cfgt::nodet &node=cfg.nodes[loc_nr];
    const goto_programt::instructiont &instruction=*node.t;
    work_queue.erase(work_queue.begin());

    auto &loc_info_src=loc_infos[loc_nr];
    auto loc_info_dest=loc_infos[loc_nr];

    switch(instruction.type())
    {
    case ASSIGN:
      assign_lhs(
        instruction.assign_lhs(),
        instruction.assign_rhs(),
        loc_info_src,
        loc_info_dest);
      break;

    case DECL:
      assign_lhs(
        instruction.decl_symbol(),
        exprt(ID_uninitialized),
        loc_info_src,
        loc_info_dest);
      break;

    case DEAD:
      assign_lhs(
        instruction.dead_symbol(),
        exprt(ID_uninitialized),
        loc_info_src,
        loc_info_dest);
      break;

    case FUNCTION_CALL:
    {
      const auto &lhs = instruction.call_lhs();
      if(lhs.is_not_nil())
        assign_lhs(lhs, nil_exprt(), loc_info_src, loc_info_dest);
      break;
    }

    case CATCH:
    case THROW:
#if 0
      DATA_INVARIANT(false, "Exceptions must be removed before analysis");
      break;
#endif
    case SET_RETURN_VALUE:
#if 0
      DATA_INVARIANT(false, "SET_RETURN_VALUE must be removed before analysis");
      break;
#endif
    case ATOMIC_BEGIN: // Ignoring is a valid over-approximation
    case ATOMIC_END:   // Ignoring is a valid over-approximation
    case LOCATION:     // No action required
    case START_THREAD: // Require a concurrent analysis at higher level
    case END_THREAD:   // Require a concurrent analysis at higher level
    case SKIP:         // No action required
    case ASSERT:       // No action required
    case ASSUME:       // Ignoring is a valid over-approximation
    case GOTO:         // Ignoring the guard is a valid over-approximation
    case END_FUNCTION: // No action required
      break;
    case OTHER:
#if 0
      DATA_INVARIANT(
        false, "Unclear what is a safe over-approximation of OTHER");
#endif
      break;
    case INCOMPLETE_GOTO:
    case NO_INSTRUCTION_TYPE:
      DATA_INVARIANT(false, "Only complete instructions can be analyzed");
      break;
    }

    for(const auto &succ : node.successors)
    {
      assert(succ<loc_infos.size());
      if(merge(loc_infos[succ], (loc_info_dest)))
        work_queue.insert(succ);
    }
  }
}

void local_bitvector_analysist::output(
  std::ostream &out,
  const goto_functiont &goto_function,
  const namespacet &ns) const
{
  unsigned l=0;

  for(const auto &instruction : goto_function.body.instructions)
  {
    out << "**** " << instruction.source_location() << "\n";

    const auto &loc_info=loc_infos[l];

    for(points_tot::const_iterator
        p_it=loc_info.begin();
        p_it!=loc_info.end();
        p_it++)
    {
      out << "  " << pointers[p_it-loc_info.begin()]
          << ": "
          << *p_it
          << "\n";
    }

    out << "\n";
    goto_function.body.output_instruction(ns, irep_idt(), out, instruction);
    out << "\n";

    l++;
  }
}
