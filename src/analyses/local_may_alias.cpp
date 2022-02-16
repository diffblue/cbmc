/*******************************************************************\

Module: Field-insensitive, location-sensitive may-alias analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Field-insensitive, location-sensitive may-alias analysis

#include "local_may_alias.h"

#include <iterator>
#include <algorithm>

#include <util/arith_tools.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>

#include <util/c_types.h>
#include <langapi/language_util.h>

/// \return return 'true' iff changed
bool local_may_aliast::loc_infot::merge(const loc_infot &src)
{
  bool changed=false;

  // do union; this should be amortized linear
  for(std::size_t i=0; i<src.aliases.size(); i++)
  {
    std::size_t root=src.aliases.find(i);

    if(!aliases.same_set(i, root))
    {
      aliases.make_union(i, root);
      changed=true;
    }
  }

  return changed;
}

void local_may_aliast::assign_lhs(
  const exprt &lhs,
  const exprt &rhs,
  const loc_infot &loc_info_src,
  loc_infot &loc_info_dest)
{
  if(lhs.id()==ID_symbol)
  {
    if(lhs.type().id()==ID_pointer)
    {
      unsigned dest_pointer=objects.number(lhs);

      // isolate the lhs pointer
      loc_info_dest.aliases.isolate(dest_pointer);

      object_sett rhs_set;
      get_rec(rhs_set, rhs, loc_info_src);

      // make these all aliases
      for(object_sett::const_iterator
          p_it=rhs_set.begin();
          p_it!=rhs_set.end();
          p_it++)
      {
        loc_info_dest.aliases.make_union(dest_pointer, *p_it);
      }
    }
  }
  else if(lhs.id()==ID_dereference)
  {
    // this might invalidate all pointers that are
    // a) local and dirty
    // b) global
    if(lhs.type().id()==ID_pointer)
    {
      for(std::size_t i=0; i<objects.size(); i++)
      {
        if(objects[i].id()==ID_symbol)
        {
          const irep_idt &identifier=
            to_symbol_expr(objects[i]).get_identifier();

          if(dirty(identifier) || !locals.is_local(identifier))
          {
            loc_info_dest.aliases.isolate(i);
            loc_info_dest.aliases.make_union(i, unknown_object);
          }
        }
      }
    }
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

std::set<exprt> local_may_aliast::get(
  const goto_programt::const_targett t,
  const exprt &rhs) const
{
  local_cfgt::loc_mapt::const_iterator loc_it=cfg.loc_map.find(t);

  assert(loc_it!=cfg.loc_map.end());

  const loc_infot &loc_info_src=loc_infos[loc_it->second];

  object_sett result_tmp;
  get_rec(result_tmp, rhs, loc_info_src);

  std::set<exprt> result;

  for(object_sett::const_iterator
      it=result_tmp.begin();
      it!=result_tmp.end();
      it++)
  {
    result.insert(objects[*it]);
  }

  return result;
}

bool local_may_aliast::aliases(
  const goto_programt::const_targett t,
  const exprt &src1, const exprt &src2) const
{
  local_cfgt::loc_mapt::const_iterator loc_it=cfg.loc_map.find(t);

  assert(loc_it!=cfg.loc_map.end());

  const loc_infot &loc_info_src=loc_infos[loc_it->second];

  object_sett tmp1, tmp2;
  get_rec(tmp1, src1, loc_info_src);
  get_rec(tmp2, src2, loc_info_src);

  if(tmp1.find(unknown_object)!=tmp1.end() ||
     tmp2.find(unknown_object)!=tmp2.end())
    return true;

  std::list<unsigned> result;

  std::set_intersection(
    tmp1.begin(), tmp1.end(),
    tmp2.begin(), tmp2.end(),
    std::back_inserter(result));

  return !result.empty();
}

void local_may_aliast::get_rec(
  object_sett &dest,
  const exprt &rhs,
  const loc_infot &loc_info_src) const
{
  if(rhs.id()==ID_constant)
  {
    if(rhs.is_zero())
      dest.insert(objects.number(exprt(ID_null_object)));
    else
      dest.insert(objects.number(exprt(ID_integer_address_object)));
  }
  else if(rhs.id()==ID_symbol)
  {
    if(rhs.type().id()==ID_pointer)
    {
      unsigned src_pointer=objects.number(rhs);

      dest.insert(src_pointer);

      for(std::size_t i=0; i<loc_info_src.aliases.size(); i++)
        if(loc_info_src.aliases.same_set(src_pointer, i))
          dest.insert(i);
    }
    else
      dest.insert(unknown_object);
  }
  else if(rhs.id()==ID_if)
  {
    get_rec(dest, to_if_expr(rhs).false_case(), loc_info_src);
    get_rec(dest, to_if_expr(rhs).true_case(), loc_info_src);
  }
  else if(rhs.id()==ID_address_of)
  {
    const exprt &object=to_address_of_expr(rhs).object();

    if(object.id()==ID_symbol)
    {
      unsigned object_nr=objects.number(rhs);
      dest.insert(object_nr);

      for(std::size_t i=0; i<loc_info_src.aliases.size(); i++)
        if(loc_info_src.aliases.same_set(object_nr, i))
          dest.insert(i);
    }
    else if(object.id()==ID_index)
    {
      const index_exprt &index_expr=to_index_expr(object);
      if(index_expr.array().id()==ID_symbol)
      {
        index_exprt tmp1=index_expr;
        tmp1.index() = from_integer(0, c_index_type());
        address_of_exprt tmp2(tmp1);
        unsigned object_nr=objects.number(tmp2);
        dest.insert(object_nr);

        for(std::size_t i=0; i<loc_info_src.aliases.size(); i++)
          if(loc_info_src.aliases.same_set(object_nr, i))
            dest.insert(i);
      }
      else if(index_expr.array().id()==ID_string_constant)
      {
        index_exprt tmp1=index_expr;
        tmp1.index() = from_integer(0, c_index_type());
        address_of_exprt tmp2(tmp1);
        unsigned object_nr=objects.number(tmp2);
        dest.insert(object_nr);

        for(std::size_t i=0; i<loc_info_src.aliases.size(); i++)
          if(loc_info_src.aliases.same_set(object_nr, i))
            dest.insert(i);
      }
      else
        dest.insert(unknown_object);
    }
    else
      dest.insert(unknown_object);
  }
  else if(rhs.id()==ID_typecast)
  {
    get_rec(dest, to_typecast_expr(rhs).op(), loc_info_src);
  }
  else if(rhs.id()==ID_plus)
  {
    const auto &plus_expr = to_plus_expr(rhs);

    if(plus_expr.operands().size() >= 3)
    {
      DATA_INVARIANT(
        plus_expr.op0().type().id() == ID_pointer,
        "pointer in pointer-typed sum must be op0");
      get_rec(dest, plus_expr.op0(), loc_info_src);
    }
    else if(plus_expr.operands().size() == 2)
    {
      // one must be pointer, one an integer
      if(plus_expr.op0().type().id() == ID_pointer)
      {
        get_rec(dest, plus_expr.op0(), loc_info_src);
      }
      else if(plus_expr.op1().type().id() == ID_pointer)
      {
        get_rec(dest, plus_expr.op1(), loc_info_src);
      }
      else
        dest.insert(unknown_object);
    }
    else
      dest.insert(unknown_object);
  }
  else if(rhs.id()==ID_minus)
  {
    const auto &op0 = to_minus_expr(rhs).op0();

    if(op0.type().id() == ID_pointer)
    {
      get_rec(dest, op0, loc_info_src);
    }
    else
      dest.insert(unknown_object);
  }
  else if(rhs.id()==ID_member)
  {
    dest.insert(unknown_object);
  }
  else if(rhs.id()==ID_index)
  {
    dest.insert(unknown_object);
  }
  else if(rhs.id()==ID_dereference)
  {
    dest.insert(unknown_object);
  }
  else if(rhs.id()==ID_side_effect)
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(rhs);
    const irep_idt &statement=side_effect_expr.get_statement();

    if(statement==ID_allocate)
    {
      dest.insert(objects.number(exprt(ID_dynamic_object)));
    }
    else
      dest.insert(unknown_object);
  }
  else if(rhs.is_nil())
  {
    // this means 'empty'
  }
  else
    dest.insert(unknown_object);
}

void local_may_aliast::build(const goto_functiont &goto_function)
{
  if(cfg.nodes.empty())
    return;

  work_queuet work_queue;

  // put all nodes into work queue
  for(local_cfgt::node_nrt n=0; n<cfg.nodes.size(); n++)
    work_queue.push(n);

  unknown_object=objects.number(exprt(ID_unknown));

  loc_infos.resize(cfg.nodes.size());

  (void)goto_function; // unused parameter
#if 0
  // feed in sufficiently bad defaults
  for(code_typet::parameterst::const_iterator
      it=goto_function.type.parameters().begin();
      it!=goto_function.type.parameters().end();
      it++)
  {
    const irep_idt &identifier=it->get_identifier();
    if(is_tracked(identifier))
      loc_infos[0].points_to[objects.number(identifier)].objects.insert(
        unknown_object);
  }
#endif

#if 0
  for(localst::locals_mapt::const_iterator
      l_it=locals.locals_map.begin();
      l_it!=locals.locals_map.end();
      l_it++)
  {
    if(is_tracked(l_it->first))
      loc_infos[0].aliases.make_union(
        objects.number(l_it->second), unknown_object);
  }
#endif

  while(!work_queue.empty())
  {
    local_cfgt::node_nrt loc_nr=work_queue.top();
    const local_cfgt::nodet &node=cfg.nodes[loc_nr];
    const goto_programt::instructiont &instruction=*node.t;
    work_queue.pop();

    const loc_infot &loc_info_src=loc_infos[loc_nr];
    loc_infot loc_info_dest=loc_infos[loc_nr];

    switch(instruction.type())
    {
    case ASSIGN:
    {
      assign_lhs(
        instruction.assign_lhs(),
        instruction.assign_rhs(),
        loc_info_src,
        loc_info_dest);
      break;
    }

    case DECL:
      assign_lhs(
        instruction.decl_symbol(), nil_exprt(), loc_info_src, loc_info_dest);
      break;

    case DEAD:
      assign_lhs(
        instruction.dead_symbol(), nil_exprt(), loc_info_src, loc_info_dest);
      break;

    case FUNCTION_CALL:
    {
      const auto &lhs = instruction.call_lhs();
      if(lhs.is_not_nil())
        assign_lhs(lhs, nil_exprt(), loc_info_src, loc_info_dest);

      // this might invalidate all pointers that are
      // a) local and dirty
      // b) global
      for(std::size_t i = 0; i < objects.size(); i++)
      {
        if(objects[i].id() == ID_symbol)
        {
          const irep_idt &identifier =
            to_symbol_expr(objects[i]).get_identifier();

          if(dirty(identifier) || !locals.is_local(identifier))
          {
            loc_info_dest.aliases.isolate(i);
            loc_info_dest.aliases.make_union(i, unknown_object);
          }
        }
      }
      break;
    }

    case CATCH:
    case THROW:
      DATA_INVARIANT(false, "Exceptions must be removed before analysis");
      break;
    case SET_RETURN_VALUE:
#if 0
      DATA_INVARIANT(false, "SET_RETURN_VALUE must be removed before analysis");
#endif
      break;
    case GOTO:         // Ignoring the guard is a valid over-approximation
    case START_THREAD: // Require a concurrent analysis at higher level
    case END_THREAD:   // Require a concurrent analysis at higher level
    case ATOMIC_BEGIN: // Ignoring is a valid over-approximation
    case ATOMIC_END:   // Ignoring is a valid over-approximation
    case LOCATION:     // No action required
    case SKIP:         // No action required
    case END_FUNCTION: // No action required
    case ASSERT:       // No action required
    case ASSUME:       // Ignoring is a valid over-approximation
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

void local_may_aliast::output(
  std::ostream &out,
  const goto_functiont &goto_function,
  const namespacet &ns) const
{
  unsigned l=0;

  for(const auto &instruction : goto_function.body.instructions)
  {
    out << "**** " << instruction.source_location() << "\n";

    const loc_infot &loc_info=loc_infos[l];

    for(std::size_t i=0; i<loc_info.aliases.size(); i++)
    {
      if(loc_info.aliases.count(i)!=1 &&
         loc_info.aliases.find(i)==i) // root?
      {
        out << '{';
        for(std::size_t j=0; j<loc_info.aliases.size(); j++)
          if(loc_info.aliases.find(j)==i)
          {
            assert(j<objects.size());
            irep_idt identifier;
            if(objects[j].id() == ID_symbol)
              identifier = to_symbol_expr(objects[j]).get_identifier();
            out << ' ' << from_expr(ns, identifier, objects[j]);
          }

        out << " }";
        out << "\n";
      }
    }

    out << "\n";
    goto_function.body.output_instruction(ns, irep_idt(), out, instruction);
    out << "\n";

    l++;
  }
}
