/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: July 2005

\*******************************************************************/

#include <assert.h>

#include <simplify_expr.h>

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
  const exprt &src)
{
  if(src.id()==ID_index)
  {
    index_exprt tmp1=to_index_expr(src);
    exprt tmp2=prop_conv.get(tmp1.index());
    if(tmp2.is_not_nil()) tmp1.index()=tmp2;
    simplify(tmp1.index(), ns);
    tmp1.array()=build_full_lhs_rec(prop_conv, ns, tmp1.array());
    return tmp1;
  }
  else if(src.id()==ID_member)
  {
    member_exprt tmp=to_member_expr(src);
    tmp.struct_op()=build_full_lhs_rec(prop_conv, ns, tmp.struct_op());
  }
  else if(src.id()==ID_if)
  {
    exprt tmp=prop_conv.get(to_if_expr(src).cond());
    if(tmp.is_true())
      return build_full_lhs_rec(prop_conv, ns, to_if_expr(src).true_case());
    else if(tmp.is_false())
      return build_full_lhs_rec(prop_conv, ns, to_if_expr(src).false_case());
    else
    {
      if_exprt tmp2=to_if_expr(src);
      tmp2.false_case()=build_full_lhs_rec(prop_conv, ns, tmp2.false_case());
      tmp2.true_case()=build_full_lhs_rec(prop_conv, ns, tmp2.true_case());
      return tmp2;
    }
  }
  else if(src.id()==ID_typecast)
  {
    typecast_exprt tmp=to_typecast_expr(src);
    tmp.op()=build_full_lhs_rec(prop_conv, ns, tmp.op());
    return tmp;
  }
  else if(src.id()==ID_byte_extract_little_endian ||
          src.id()==ID_byte_extract_big_endian)
  {
    exprt tmp=src;
    assert(tmp.operands().size()==2);
    tmp.op0()=build_full_lhs_rec(prop_conv, ns, tmp.op0());

    // re-write into big case-split
    
  }
  
  return src;
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
  unsigned step_nr=0;
  
  for(symex_target_equationt::SSA_stepst::const_iterator
      it=target.SSA_steps.begin();
      it!=target.SSA_steps.end();
      it++)
  {
    const symex_target_equationt::SSA_stept &SSA_step=*it;
    
    if(prop_conv.prop.l_get(SSA_step.guard_literal)!=tvt(true))
      continue;

    if(it->is_assignment() &&
       SSA_step.assignment_type==symex_target_equationt::HIDDEN)
      continue;

    step_nr++;
    
    goto_trace.steps.push_back(goto_trace_stept());    
    goto_trace_stept &goto_trace_step=goto_trace.steps.back();
    
    goto_trace_step.thread_nr=SSA_step.source.thread_nr;
    goto_trace_step.pc=SSA_step.source.pc;
    goto_trace_step.comment=SSA_step.comment;
    goto_trace_step.lhs_object=SSA_step.original_lhs_object;
    goto_trace_step.type=SSA_step.type;
    goto_trace_step.step_nr=step_nr;
    goto_trace_step.format_string=SSA_step.format_string;
    goto_trace_step.io_id=SSA_step.io_id;
    goto_trace_step.formatted=SSA_step.formatted;

    if(SSA_step.original_full_lhs.is_not_nil())
      goto_trace_step.full_lhs=
        build_full_lhs_rec(prop_conv, ns, SSA_step.original_full_lhs);
    
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
        prop_conv.prop.l_get(SSA_step.cond_literal).is_true();
    }

    if(SSA_step.is_assert())
    {
      // we stop after a violated assertion
      if(!goto_trace_step.cond_value)
        break;
    }
    else if(SSA_step.is_assume())
    {
      // assumptions can't be false
      assert(goto_trace_step.cond_value);
    }
  }
}
