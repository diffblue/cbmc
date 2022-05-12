/*******************************************************************\

Module: Race Detection for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

/// \file
/// Race Detection for Threaded Goto Programs

#include "rw_set.h"

#include <util/pointer_expr.h>
#include <util/std_code.h>

#include <langapi/language_util.h>

#include <pointer-analysis/goto_program_dereference.h>

void rw_set_baset::output(std::ostream &out) const
{
  out << "READ:\n";
  for(entriest::const_iterator it=r_entries.begin();
      it!=r_entries.end();
      it++)
  {
    out << it->second.object << " if "
        << from_expr(ns, it->second.object, it->second.guard) << '\n';
  }

  out << '\n';

  out << "WRITE:\n";
  for(entriest::const_iterator it=w_entries.begin();
      it!=w_entries.end();
      it++)
  {
    out << it->second.object << " if "
        << from_expr(ns, it->second.object, it->second.guard) << '\n';
  }
}

void _rw_set_loct::compute()
{
  if(target->is_assign())
  {
    assign(target->assign_lhs(), target->assign_rhs());
  }
  else if(target->is_goto() ||
          target->is_assume() ||
          target->is_assert())
  {
    read(target->condition());
  }
  else if(target->is_function_call())
  {
    read(target->call_function());

    // do operands
    for(code_function_callt::argumentst::const_iterator it =
          target->call_arguments().begin();
        it != target->call_arguments().end();
        it++)
      read(*it);

    if(target->call_lhs().is_not_nil())
      write(target->call_lhs());
  }
}

void _rw_set_loct::assign(const exprt &lhs, const exprt &rhs)
{
  read(rhs);
  read_write_rec(lhs, false, true, "", exprt::operandst());
}

void _rw_set_loct::read_write_rec(
  const exprt &expr,
  bool r,
  bool w,
  const std::string &suffix,
  const exprt::operandst &guard_conjuncts)
{
  if(expr.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(expr);

    irep_idt object=id2string(symbol_expr.get_identifier())+suffix;

    if(r)
    {
      const auto &entry = r_entries.emplace(
        object, entryt(symbol_expr, object, conjunction(guard_conjuncts)));

      track_deref(entry.first->second, true);
    }

    if(w)
    {
      const auto &entry = w_entries.emplace(
        object, entryt(symbol_expr, object, conjunction(guard_conjuncts)));

      track_deref(entry.first->second, false);
    }
  }
  else if(expr.id()==ID_member)
  {
    const auto &member_expr = to_member_expr(expr);
    const std::string &component_name =
      id2string(member_expr.get_component_name());
    read_write_rec(
      member_expr.compound(),
      r,
      w,
      "." + component_name + suffix,
      guard_conjuncts);
  }
  else if(expr.id()==ID_index)
  {
    // we don't distinguish the array elements for now
    const auto &index_expr = to_index_expr(expr);
    read_write_rec(index_expr.array(), r, w, "[]" + suffix, guard_conjuncts);
    read(index_expr.index(), guard_conjuncts);
  }
  else if(expr.id()==ID_dereference)
  {
    set_track_deref();
    read(to_dereference_expr(expr).pointer(), guard_conjuncts);

    exprt tmp=expr;
    #ifdef LOCAL_MAY
    const std::set<exprt> aliases=local_may.get(target, expr);
    for(std::set<exprt>::const_iterator it=aliases.begin();
      it!=aliases.end();
      ++it)
    {
      #ifndef LOCAL_MAY_SOUND
      if(it->id()==ID_unknown)
      {
        /* as an under-approximation */
        // std::cout << "Sorry, LOCAL_MAY too imprecise. "
        //           << Omitting some variables.\n";
        irep_idt object=ID_unknown;

        entryt &entry=r_entries[object];
        entry.object=object;
        entry.symbol_expr=symbol_exprt(ID_unknown);
        entry.guard = conjunction(guard_conjuncts); // should 'OR'

        continue;
      }
      #endif
      read_write_rec(*it, r, w, suffix, guard_conjuncts);
    }
    #else
    dereference(function_id, target, tmp, ns, value_sets);

    read_write_rec(tmp, r, w, suffix, guard_conjuncts);
#endif

    reset_track_deref();
  }
  else if(expr.id()==ID_typecast)
  {
    read_write_rec(to_typecast_expr(expr).op(), r, w, suffix, guard_conjuncts);
  }
  else if(expr.id()==ID_address_of)
  {
    assert(expr.operands().size()==1);
  }
  else if(expr.id()==ID_if)
  {
    const auto &if_expr = to_if_expr(expr);
    read(if_expr.cond(), guard_conjuncts);

    exprt::operandst true_guard = guard_conjuncts;
    true_guard.push_back(if_expr.cond());
    read_write_rec(if_expr.true_case(), r, w, suffix, true_guard);

    exprt::operandst false_guard = guard_conjuncts;
    false_guard.push_back(not_exprt(if_expr.cond()));
    read_write_rec(if_expr.false_case(), r, w, suffix, false_guard);
  }
  else
  {
    forall_operands(it, expr)
      read_write_rec(*it, r, w, suffix, guard_conjuncts);
  }
}

void rw_set_functiont::compute_rec(const exprt &function)
{
  if(function.id()==ID_symbol)
  {
    const irep_idt &function_id = to_symbol_expr(function).get_identifier();

    goto_functionst::function_mapt::const_iterator f_it =
      goto_functions.function_map.find(function_id);

    if(f_it!=goto_functions.function_map.end())
    {
      const goto_programt &body=f_it->second.body;

#ifdef LOCAL_MAY
      local_may_aliast local_may(f_it->second);
#if 0
      for(goto_functionst::function_mapt::const_iterator
          g_it=goto_functions.function_map.begin();
          g_it!=goto_functions.function_map.end(); ++g_it)
        local_may(g_it->second);
#endif
#endif

      forall_goto_program_instructions(i_it, body)
      {
        *this += rw_set_loct(
          ns,
          value_sets,
          function_id,
          i_it
#ifdef LOCAL_MAY
          ,
          local_may
#endif
        ); // NOLINT(whitespace/parens)
      }
    }
  }
  else if(function.id()==ID_if)
  {
    compute_rec(to_if_expr(function).true_case());
    compute_rec(to_if_expr(function).false_case());
  }
}
