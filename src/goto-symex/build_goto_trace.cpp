/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: July 2005

\*******************************************************************/

#include <cassert>

#include <util/threeval.h>
#include <util/simplify_expr.h>
#include <util/arith_tools.h>

#include <solvers/prop/prop_conv.h>
#include <solvers/prop/prop.h>

#include "partial_order_concurrency.h"

#include "build_goto_trace.h"

/*******************************************************************\

Function: build_full_lhs_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: adjust_lhs_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt adjust_lhs_object(
  const prop_convt &prop_conv,
  const namespacet &ns,
  const exprt &src)
{
  return nil_exprt();
}

/*******************************************************************\

Function: build_goto_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  
  for(symex_target_equationt::SSA_stepst::const_iterator
      it=target.SSA_steps.begin();
      it!=end_step;
      it++)
  {
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
       (SSA_step.assignment_type==symex_target_equationt::PHI ||
        SSA_step.assignment_type==symex_target_equationt::GUARD))
      continue;

    goto_tracet::stepst &steps=time_map[current_time];
    steps.push_back(goto_trace_stept());    
    goto_trace_stept &goto_trace_step=steps.back();
    
    goto_trace_step.thread_nr=SSA_step.source.thread_nr;
    goto_trace_step.pc=SSA_step.source.pc;
    goto_trace_step.comment=SSA_step.comment;
    goto_trace_step.lhs_object=SSA_step.original_lhs_object;
    goto_trace_step.type=SSA_step.type;
    goto_trace_step.hidden=SSA_step.hidden;
    goto_trace_step.format_string=SSA_step.format_string;
    goto_trace_step.io_id=SSA_step.io_id;
    goto_trace_step.formatted=SSA_step.formatted;
    goto_trace_step.identifier=SSA_step.identifier;

    goto_trace_step.assignment_type=
      (SSA_step.assignment_type==symex_targett::VISIBLE_ACTUAL_PARAMETER ||
       SSA_step.assignment_type==symex_targett::HIDDEN_ACTUAL_PARAMETER)?
      goto_trace_stept::ACTUAL_PARAMETER:
      goto_trace_stept::STATE;
    
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
    
    for(std::list<exprt>::const_iterator
        j=SSA_step.converted_io_args.begin();
        j!=SSA_step.converted_io_args.end();
        j++)
    {
      const exprt &arg=*j;
      if(arg.is_constant() ||
         arg.id()==ID_string_constant)
        goto_trace_step.io_args.push_back(arg);
      else
      {
        exprt tmp=prop_conv.get(arg);
        goto_trace_step.io_args.push_back(tmp);
      }
    }

    if(SSA_step.is_assert() ||
       SSA_step.is_assume())
    {
      goto_trace_step.cond_expr=SSA_step.cond_expr;

      goto_trace_step.cond_value=
        prop_conv.l_get(SSA_step.cond_literal).is_true();
    }
    else if(SSA_step.is_location() &&
            SSA_step.source.pc->is_goto())
    {
      goto_trace_step.cond_expr=SSA_step.source.pc->guard;

      const bool backwards=SSA_step.source.pc->is_backwards_goto();

      symex_target_equationt::SSA_stepst::const_iterator next=it;
      ++next;
      assert(next!=target.SSA_steps.end());

      // goto was taken if backwards and next is enabled or forward
      // and next is not active;
      // there is an ambiguity here if a forward goto is to the next
      // instruction, which we simply ignore for now
      goto_trace_step.goto_taken=
        backwards==
        (prop_conv.l_get(next->guard_literal)==tvt(true));
    }
  }
  
  // Now assemble into a single goto_trace.
  // This expoits sorted-ness of the map.
  for(time_mapt::iterator t_it=time_map.begin();
      t_it!=time_map.end(); t_it++)
  {
    goto_trace.steps.splice(goto_trace.steps.end(), t_it->second);
  }

  // produce the step numbers
  unsigned step_nr=0;
  
  for(goto_tracet::stepst::iterator
      s_it=goto_trace.steps.begin();
      s_it!=goto_trace.steps.end();
      s_it++)
    s_it->step_nr=++step_nr;
}

/*******************************************************************\

Function: build_goto_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
      s_it1++;

      for(goto_tracet::stepst::iterator
          s_it2=s_it1;
          s_it2!=goto_trace.steps.end();
          s_it2=goto_trace.steps.erase(s_it2));
        
      break;
    }
}

