/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: July 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include "build_goto_trace.h"

#include <cassert>

#include <util/threeval.h>
#include <util/simplify_expr.h>
#include <util/arith_tools.h>

#include <solvers/prop/prop_conv.h>
#include <solvers/prop/prop.h>

#include "partial_order_concurrency.h"

exprt build_full_lhs_rec(
  const prop_convt &prop_conv,
  const namespacet &ns,
  const exprt &src_original, // original identifiers
  const exprt &src_ssa)      // renamed identifiers
{
  if(src_ssa.id()!=src_original.id())
    return src_original;

  const irep_idt id=src_original.id();

  if(id==ID_index)
  {
    // get index value from src_ssa
    exprt index_value=prop_conv.get(to_index_expr(src_ssa).index());

    if(index_value.is_not_nil())
    {
      simplify(index_value, ns);
      index_exprt tmp=to_index_expr(src_original);
      tmp.index()=index_value;
      tmp.array()=
        build_full_lhs_rec(prop_conv, ns,
          to_index_expr(src_original).array(),
          to_index_expr(src_ssa).array());
      return tmp;
    }

    return src_original;
  }
  else if(id==ID_member)
  {
    member_exprt tmp=to_member_expr(src_original);
    tmp.struct_op()=build_full_lhs_rec(
      prop_conv, ns,
      to_member_expr(src_original).struct_op(),
      to_member_expr(src_ssa).struct_op());
  }
  else if(id==ID_if)
  {
    if_exprt tmp2=to_if_expr(src_original);

    tmp2.false_case()=build_full_lhs_rec(prop_conv, ns,
      tmp2.false_case(), to_if_expr(src_ssa).false_case());

    tmp2.true_case()=build_full_lhs_rec(prop_conv, ns,
      tmp2.true_case(), to_if_expr(src_ssa).true_case());

    exprt tmp=prop_conv.get(to_if_expr(src_ssa).cond());

    if(tmp.is_true())
      return tmp2.true_case();
    else if(tmp.is_false())
      return tmp2.false_case();
    else
      return tmp2;
  }
  else if(id==ID_typecast)
  {
    typecast_exprt tmp=to_typecast_expr(src_original);
    tmp.op()=build_full_lhs_rec(prop_conv, ns,
      to_typecast_expr(src_original).op(), to_typecast_expr(src_ssa).op());
    return tmp;
  }
  else if(id==ID_byte_extract_little_endian ||
          id==ID_byte_extract_big_endian)
  {
    exprt tmp=src_original;
    assert(tmp.operands().size()==2);
    tmp.op0()=build_full_lhs_rec(prop_conv, ns, tmp.op0(), src_ssa.op0());

    // re-write into big case-split
  }

  return src_original;
}

exprt adjust_lhs_object(
  const prop_convt &prop_conv,
  const namespacet &ns,
  const exprt &src)
{
  return nil_exprt();
}

/// set internal field for variable assignment related to dynamic_object[0-9]
/// and dynamic_[0-9]_array.
void hide_dynamic_object(
  const exprt &expr,
  goto_trace_stept &goto_trace_step,
  const namespacet &ns)
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt &id=to_ssa_expr(expr).get_original_name();
    const symbolt *symbol;
    if(!ns.lookup(id, symbol))
    {
      bool result=symbol->type.get_bool("#dynamic");
      if(result)
        goto_trace_step.hidden=true;
    }
  }
  else
  {
    forall_operands(it, expr)
      hide_dynamic_object(*it, goto_trace_step, ns);
  }
}

/// set internal for variables assignments related to dynamic_object and CPROVER
/// internal functions (e.g., __CPROVER_initialize)
void update_fields_to_hidden(
  const symex_target_equationt::SSA_stept &SSA_step,
  goto_trace_stept &goto_trace_step,
  const namespacet &ns)
{
  // hide dynamic_object in both lhs and rhs expressions
  hide_dynamic_object(SSA_step.ssa_lhs, goto_trace_step, ns);
  hide_dynamic_object(SSA_step.ssa_rhs, goto_trace_step, ns);

  // hide internal CPROVER functions (e.g., __CPROVER_initialize)
  if(SSA_step.is_function_call())
  {
    if(SSA_step.source.pc->source_location.as_string().empty())
      goto_trace_step.hidden=true;
  }

  // set internal field to input and output steps
  if(goto_trace_step.type==goto_trace_stept::typet::OUTPUT ||
      goto_trace_step.type==goto_trace_stept::typet::INPUT)
  {
    goto_trace_step.hidden=true;
  }

  // set internal field to _start function-return step
  if(SSA_step.source.pc->function==goto_functionst::entry_point())
  {
    goto_trace_step.internal=true;
  }
}

void build_goto_trace(
  const symex_target_equationt &target,
  symex_target_equationt::SSA_stepst::const_iterator end_step,
  const prop_convt &prop_conv,
  const namespacet &ns,
  goto_tracet &goto_trace)
{
  // We need to re-sort the steps according to their clock.
  // Furthermore, read-events need to occur before write
  // events with the same clock.

  typedef std::map<mp_integer, goto_tracet::stepst> time_mapt;
  time_mapt time_map;

  mp_integer current_time=0;

  const goto_trace_stept *end_ptr=nullptr;
  bool end_step_seen=false;

  for(symex_target_equationt::SSA_stepst::const_iterator
      it=target.SSA_steps.begin();
      it!=target.SSA_steps.end();
      it++)
  {
    if(it==end_step)
      end_step_seen=true;

    const symex_target_equationt::SSA_stept &SSA_step=*it;

    if(prop_conv.l_get(SSA_step.guard_literal)!=tvt(true))
      continue;

    if(it->is_constraint() ||
       it->is_spawn())
      continue;
    else if(it->is_atomic_begin())
    {
      // for atomic sections the timing can only be determined once we see
      // a shared read or write (if there is none, the time will be
      // reverted to the time before entering the atomic section); we thus
      // use a temporary negative time slot to gather all events
      current_time*=-1;
      continue;
    }
    else if(it->is_shared_read() || it->is_shared_write() ||
            it->is_atomic_end())
    {
      mp_integer time_before=current_time;

      if(it->is_shared_read() || it->is_shared_write())
      {
        // these are just used to get the time stamp
        exprt clock_value=prop_conv.get(
          symbol_exprt(partial_order_concurrencyt::rw_clock_id(it)));

        to_integer(clock_value, current_time);
      }
      else if(it->is_atomic_end() && current_time<0)
        current_time*=-1;

      assert(current_time>=0);
      // move any steps gathered in an atomic section

      if(time_before<0)
      {
        time_mapt::iterator entry=
          time_map.insert(std::make_pair(
              current_time,
              goto_tracet::stepst())).first;
        entry->second.splice(entry->second.end(), time_map[time_before]);
        time_map.erase(time_before);
      }

      continue;
    }

    // drop PHI and GUARD assignments altogether
    if(it->is_assignment() &&
       (SSA_step.assignment_type==
          symex_target_equationt::assignment_typet::PHI ||
        SSA_step.assignment_type==
          symex_target_equationt::assignment_typet::GUARD))
    {
      continue;
    }

    goto_tracet::stepst &steps=time_map[current_time];
    steps.push_back(goto_trace_stept());
    goto_trace_stept &goto_trace_step=steps.back();
    if(!end_step_seen)
      end_ptr=&goto_trace_step;

    goto_trace_step.thread_nr=SSA_step.source.thread_nr;
    goto_trace_step.pc=SSA_step.source.pc;
    goto_trace_step.comment=SSA_step.comment;
    if(SSA_step.ssa_lhs.is_not_nil())
      goto_trace_step.lhs_object=
        ssa_exprt(SSA_step.ssa_lhs.get_original_expr());
    else
      goto_trace_step.lhs_object.make_nil();
    goto_trace_step.type=SSA_step.type;
    goto_trace_step.hidden=SSA_step.hidden;
    goto_trace_step.format_string=SSA_step.format_string;
    goto_trace_step.io_id=SSA_step.io_id;
    goto_trace_step.formatted=SSA_step.formatted;
    goto_trace_step.identifier=SSA_step.identifier;

    // hide specific variables in the counterexample trace
    update_fields_to_hidden(SSA_step, goto_trace_step, ns);

    goto_trace_step.assignment_type=
      (it->is_assignment()&&
       (SSA_step.assignment_type==
          symex_targett::assignment_typet::VISIBLE_ACTUAL_PARAMETER ||
        SSA_step.assignment_type==
          symex_targett::assignment_typet::HIDDEN_ACTUAL_PARAMETER))?
      goto_trace_stept::assignment_typet::ACTUAL_PARAMETER:
      goto_trace_stept::assignment_typet::STATE;

    if(SSA_step.original_full_lhs.is_not_nil())
      goto_trace_step.full_lhs=
        build_full_lhs_rec(
          prop_conv, ns, SSA_step.original_full_lhs, SSA_step.ssa_full_lhs);

    if(SSA_step.ssa_lhs.is_not_nil())
      goto_trace_step.lhs_object_value=prop_conv.get(SSA_step.ssa_lhs);

    if(SSA_step.ssa_full_lhs.is_not_nil())
    {
      goto_trace_step.full_lhs_value=prop_conv.get(SSA_step.ssa_full_lhs);
      simplify(goto_trace_step.full_lhs_value, ns);
    }

    for(const auto &j : SSA_step.converted_io_args)
    {
      if(j.is_constant() ||
         j.id()==ID_string_constant)
        goto_trace_step.io_args.push_back(j);
      else
      {
        exprt tmp=prop_conv.get(j);
        goto_trace_step.io_args.push_back(tmp);
      }
    }

    if(SSA_step.is_assert() ||
       SSA_step.is_assume() ||
       SSA_step.is_goto())
    {
      goto_trace_step.cond_expr=SSA_step.cond_expr;

      goto_trace_step.cond_value=
        prop_conv.l_get(SSA_step.cond_literal).is_true();
    }
  }

  // Now assemble into a single goto_trace.
  // This exploits sorted-ness of the map.
  for(auto &t_it : time_map)
    goto_trace.steps.splice(goto_trace.steps.end(), t_it.second);

  // cut off the trace at the desired end
  for(goto_tracet::stepst::iterator
      s_it1=goto_trace.steps.begin();
      s_it1!=goto_trace.steps.end();
      ++s_it1)
    if(end_step_seen && end_ptr==&(*s_it1))
    {
      goto_trace.trim_after(s_it1);
      break;
    }

  // produce the step numbers
  unsigned step_nr=0;

  for(auto &s_it : goto_trace.steps)
    s_it.step_nr=++step_nr;
}

void build_goto_trace(
  const symex_target_equationt &target,
  const prop_convt &prop_conv,
  const namespacet &ns,
  goto_tracet &goto_trace)
{
  build_goto_trace(
    target, target.SSA_steps.end(), prop_conv, ns, goto_trace);

  // Now delete anything after first failed assertion
  for(goto_tracet::stepst::iterator
      s_it1=goto_trace.steps.begin();
      s_it1!=goto_trace.steps.end();
      s_it1++)
    if(s_it1->is_assert() && !s_it1->cond_value)
    {
      goto_trace.trim_after(s_it1);
      break;
    }
}
