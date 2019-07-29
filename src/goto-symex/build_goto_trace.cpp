/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: July 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include "build_goto_trace.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/simplify_expr.h>
#include <util/threeval.h>

#include <goto-programs/goto_functions.h>

#include <solvers/decision_procedure.h>

#include "partial_order_concurrency.h"

static exprt build_full_lhs_rec(
  const decision_proceduret &decision_procedure,
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
    exprt index_value = decision_procedure.get(to_index_expr(src_ssa).index());

    if(index_value.is_not_nil())
    {
      simplify(index_value, ns);
      index_exprt tmp=to_index_expr(src_original);
      tmp.index()=index_value;
      tmp.array() = build_full_lhs_rec(
        decision_procedure,
        ns,
        to_index_expr(src_original).array(),
        to_index_expr(src_ssa).array());
      return std::move(tmp);
    }

    return src_original;
  }
  else if(id==ID_member)
  {
    member_exprt tmp=to_member_expr(src_original);
    tmp.struct_op() = build_full_lhs_rec(
      decision_procedure,
      ns,
      to_member_expr(src_original).struct_op(),
      to_member_expr(src_ssa).struct_op());
  }
  else if(id==ID_if)
  {
    if_exprt tmp2=to_if_expr(src_original);

    tmp2.false_case() = build_full_lhs_rec(
      decision_procedure,
      ns,
      tmp2.false_case(),
      to_if_expr(src_ssa).false_case());

    tmp2.true_case() = build_full_lhs_rec(
      decision_procedure,
      ns,
      tmp2.true_case(),
      to_if_expr(src_ssa).true_case());

    exprt tmp = decision_procedure.get(to_if_expr(src_ssa).cond());

    if(tmp.is_true())
      return tmp2.true_case();
    else if(tmp.is_false())
      return tmp2.false_case();
    else
      return std::move(tmp2);
  }
  else if(id==ID_typecast)
  {
    typecast_exprt tmp=to_typecast_expr(src_original);
    tmp.op() = build_full_lhs_rec(
      decision_procedure,
      ns,
      to_typecast_expr(src_original).op(),
      to_typecast_expr(src_ssa).op());
    return std::move(tmp);
  }
  else if(id==ID_byte_extract_little_endian ||
          id==ID_byte_extract_big_endian)
  {
    byte_extract_exprt tmp = to_byte_extract_expr(src_original);
    tmp.op() = build_full_lhs_rec(
      decision_procedure, ns, tmp.op(), to_byte_extract_expr(src_ssa).op());

    // re-write into big case-split
  }

  return src_original;
}

/// set internal field for variable assignment related to dynamic_object[0-9]
/// and dynamic_[0-9]_array.
static void set_internal_dynamic_object(
  const exprt &expr,
  goto_trace_stept &goto_trace_step,
  const namespacet &ns)
{
  if(expr.id()==ID_symbol)
  {
    const auto &type = expr.type();
    if(type.id() != ID_code && type.id() != ID_mathematical_function)
    {
      const irep_idt &id = to_ssa_expr(expr).get_original_name();
      const symbolt *symbol;
      if(!ns.lookup(id, symbol))
      {
        bool result = symbol->type.get_bool(ID_C_dynamic);
        if(result)
          goto_trace_step.internal = true;
      }
    }
  }
  else
  {
    forall_operands(it, expr)
      set_internal_dynamic_object(*it, goto_trace_step, ns);
  }
}

/// set internal for variables assignments related to dynamic_object and CPROVER
/// internal functions (e.g., __CPROVER_initialize)
static void update_internal_field(
  const SSA_stept &SSA_step,
  goto_trace_stept &goto_trace_step,
  const namespacet &ns)
{
  // set internal for dynamic_object in both lhs and rhs expressions
  set_internal_dynamic_object(SSA_step.ssa_lhs, goto_trace_step, ns);
  set_internal_dynamic_object(SSA_step.ssa_rhs, goto_trace_step, ns);

  // set internal field to CPROVER functions (e.g., __CPROVER_initialize)
  if(SSA_step.is_function_call())
  {
    if(SSA_step.source.pc->source_location.as_string().empty())
      goto_trace_step.internal=true;
  }

  // set internal field to input and output steps
  if(goto_trace_step.type==goto_trace_stept::typet::OUTPUT ||
      goto_trace_step.type==goto_trace_stept::typet::INPUT)
  {
    goto_trace_step.internal=true;
  }

  // set internal field to _start function-return step
  if(SSA_step.source.function_id == goto_functionst::entry_point())
  {
    // "__CPROVER_*" function calls in __CPROVER_start are already marked as
    // internal. Don't mark any other function calls (i.e. "main"), function
    // arguments or any other parts of a code_function_callt as internal.
    if(SSA_step.source.pc->code.get_statement()!=ID_function_call)
      goto_trace_step.internal=true;
  }
}

/// Replace nondet values that appear in \p type by their values as found by
/// \p solver.
static void
replace_nondet_in_type(typet &type, const decision_proceduret &solver)
{
  if(type.id() == ID_array)
  {
    array_typet &array_type = to_array_type(type);
    array_type.size() = solver.get(array_type.size());
  }
  if(type.has_subtype())
    replace_nondet_in_type(type.subtype(), solver);
}

/// Replace nondet values that appear in the type of \p expr and its
/// subexpressions type by their values as found by \p solver.
static void
replace_nondet_in_type(exprt &expr, const decision_proceduret &solver)
{
  replace_nondet_in_type(expr.type(), solver);
  for(auto &sub : expr.operands())
    replace_nondet_in_type(sub, solver);
}

void build_goto_trace(
  const symex_target_equationt &target,
  ssa_step_predicatet is_last_step_to_keep,
  const decision_proceduret &decision_procedure,
  const namespacet &ns,
  goto_tracet &goto_trace)
{
  // We need to re-sort the steps according to their clock.
  // Furthermore, read-events need to occur before write
  // events with the same clock.

  typedef symex_target_equationt::SSA_stepst::const_iterator ssa_step_iteratort;
  typedef std::map<mp_integer, std::vector<ssa_step_iteratort>> time_mapt;
  time_mapt time_map;

  mp_integer current_time=0;

  ssa_step_iteratort last_step_to_keep = target.SSA_steps.end();
  bool last_step_was_kept = false;

  // First sort the SSA steps by time, in the process dropping steps
  // we definitely don't want to retain in the final trace:

  for(ssa_step_iteratort it = target.SSA_steps.begin();
      it != target.SSA_steps.end();
      it++)
  {
    if(
      last_step_to_keep == target.SSA_steps.end() &&
      is_last_step_to_keep(it, decision_procedure))
    {
      last_step_to_keep = it;
    }

    const SSA_stept &SSA_step = *it;

    if(!decision_procedure.get(SSA_step.guard_handle).is_true())
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
        // these are just used to get the time stamp -- the clock type is
        // computed to be of the minimal necessary size, but we don't need to
        // know it to get the value so just use typeless
        exprt clock_value = decision_procedure.get(
          symbol_exprt::typeless(partial_order_concurrencyt::rw_clock_id(it)));

        const auto cv = numeric_cast<mp_integer>(clock_value);
        if(cv.has_value())
          current_time = *cv;
        else
          current_time = 0;
      }
      else if(it->is_atomic_end() && current_time<0)
        current_time*=-1;

      INVARIANT(current_time >= 0, "time keeping inconsistency");
      // move any steps gathered in an atomic section

      if(time_before<0)
      {
        time_mapt::const_iterator time_before_steps_it =
          time_map.find(time_before);

        if(time_before_steps_it != time_map.end())
        {
          std::vector<ssa_step_iteratort> &current_time_steps =
            time_map[current_time];

          current_time_steps.insert(
            current_time_steps.end(),
            time_before_steps_it->second.begin(),
            time_before_steps_it->second.end());

          time_map.erase(time_before_steps_it);
        }
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

    if(it == last_step_to_keep)
    {
      last_step_was_kept = true;
    }

    time_map[current_time].push_back(it);
  }

  INVARIANT(
    last_step_to_keep == target.SSA_steps.end() || last_step_was_kept,
    "last step in SSA trace to keep must not be filtered out as a sync "
    "instruction, not-taken branch, PHI node, or similar");

  // Now build the GOTO trace, ordered by time, then by SSA trace order.

  // produce the step numbers
  unsigned step_nr = 0;

  for(const auto &time_and_ssa_steps : time_map)
  {
    for(const auto ssa_step_it : time_and_ssa_steps.second)
    {
      const auto &SSA_step = *ssa_step_it;
      goto_trace.steps.push_back(goto_trace_stept());
      goto_trace_stept &goto_trace_step = goto_trace.steps.back();

      goto_trace_step.step_nr = ++step_nr;

      goto_trace_step.thread_nr = SSA_step.source.thread_nr;
      goto_trace_step.pc = SSA_step.source.pc;
      goto_trace_step.function_id = SSA_step.source.function_id;
      if(SSA_step.is_assert())
      {
        goto_trace_step.comment = SSA_step.comment;
        goto_trace_step.property_id = SSA_step.get_property_id();
      }
      goto_trace_step.type = SSA_step.type;
      goto_trace_step.hidden = SSA_step.hidden;
      goto_trace_step.format_string = SSA_step.format_string;
      goto_trace_step.io_id = SSA_step.io_id;
      goto_trace_step.formatted = SSA_step.formatted;
      goto_trace_step.called_function = SSA_step.called_function;
      goto_trace_step.function_arguments = SSA_step.converted_function_arguments;

      for(auto &arg : goto_trace_step.function_arguments)
        arg = decision_procedure.get(arg);

      // update internal field for specific variables in the counterexample
      update_internal_field(SSA_step, goto_trace_step, ns);

      goto_trace_step.assignment_type =
        (SSA_step.is_assignment() &&
         (SSA_step.assignment_type ==
            symex_targett::assignment_typet::VISIBLE_ACTUAL_PARAMETER ||
          SSA_step.assignment_type ==
            symex_targett::assignment_typet::HIDDEN_ACTUAL_PARAMETER))
          ? goto_trace_stept::assignment_typet::ACTUAL_PARAMETER
          : goto_trace_stept::assignment_typet::STATE;

      if(SSA_step.original_full_lhs.is_not_nil())
      {
        goto_trace_step.full_lhs = simplify_expr(
          build_full_lhs_rec(
            decision_procedure,
            ns,
            SSA_step.original_full_lhs,
            SSA_step.ssa_full_lhs),
          ns);
        replace_nondet_in_type(goto_trace_step.full_lhs, decision_procedure);
      }

      if(SSA_step.ssa_full_lhs.is_not_nil())
      {
        goto_trace_step.full_lhs_value =
          decision_procedure.get(SSA_step.ssa_full_lhs);
        simplify(goto_trace_step.full_lhs_value, ns);
        replace_nondet_in_type(
          goto_trace_step.full_lhs_value, decision_procedure);
      }

      for(const auto &j : SSA_step.converted_io_args)
      {
        if(j.is_constant() || j.id() == ID_string_constant)
        {
          goto_trace_step.io_args.push_back(j);
        }
        else
        {
          exprt tmp = decision_procedure.get(j);
          goto_trace_step.io_args.push_back(tmp);
        }
      }

      if(SSA_step.is_assert() || SSA_step.is_assume() || SSA_step.is_goto())
      {
        goto_trace_step.cond_expr = SSA_step.cond_expr;

        goto_trace_step.cond_value =
          decision_procedure.get(SSA_step.cond_handle).is_true();
      }

      if(ssa_step_it == last_step_to_keep)
        return;
    }
  }
}

void build_goto_trace(
  const symex_target_equationt &target,
  symex_target_equationt::SSA_stepst::const_iterator last_step_to_keep,
  const decision_proceduret &decision_procedure,
  const namespacet &ns,
  goto_tracet &goto_trace)
{
  const auto is_last_step_to_keep =
    [last_step_to_keep](
      symex_target_equationt::SSA_stepst::const_iterator it,
      const decision_proceduret &) { return last_step_to_keep == it; };

  return build_goto_trace(
    target, is_last_step_to_keep, decision_procedure, ns, goto_trace);
}

static bool is_failed_assertion_step(
  symex_target_equationt::SSA_stepst::const_iterator step,
  const decision_proceduret &decision_procedure)
{
  return step->is_assert() &&
         decision_procedure.get(step->cond_handle).is_false();
}

void build_goto_trace(
  const symex_target_equationt &target,
  const decision_proceduret &decision_procedure,
  const namespacet &ns,
  goto_tracet &goto_trace)
{
  build_goto_trace(
    target, is_failed_assertion_step, decision_procedure, ns, goto_trace);
}
