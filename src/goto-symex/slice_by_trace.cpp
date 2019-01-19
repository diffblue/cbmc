/*******************************************************************\

Module: Slicer for symex traces

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Slicer for symex traces

#include "slice_by_trace.h"

#include <cstring>
#include <set>
#include <fstream>
#include <iostream>

#include <util/arith_tools.h>
#include <util/exception_utils.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/guard.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string2int.h>

void symex_slice_by_tracet::slice_by_trace(
  std::string trace_files,
  symex_target_equationt &equation)
{
  std::cout << "Slicing by trace...\n";

  merge_identifier="goto_symex::\\merge";
  merge_symbol=symbol_exprt(typet(ID_bool));
  merge_symbol.set_identifier(merge_identifier);

  std::vector<exprt> trace_conditions;

  size_t length=trace_files.length();
  for(size_t idx=0; idx < length; idx++)
  {
    const std::string::size_type next=trace_files.find(",", idx);
    std::string filename=trace_files.substr(idx, next - idx);

    read_trace(filename);

    compute_ts_back(equation);

    exprt t_copy(t[0]);
    trace_conditions.push_back(t_copy);

    if(next==std::string::npos)
      break;
    idx=next;
  }

  exprt trace_condition = conjunction(trace_conditions);

  simplify(trace_condition, ns);

  std::set<exprt> implications=implied_guards(trace_condition);

  for(const auto &guard : sliced_guards)
  {
    exprt g_copy(guard);

    DATA_INVARIANT(
      g_copy.id() == ID_symbol || g_copy.id() == ID_not ||
        g_copy.id() == ID_and || g_copy.id() == ID_constant,
      "guards should only be and, symbol, constant, or `not'");

    if(g_copy.id()==ID_symbol || g_copy.id() == ID_not)
    {
      g_copy = simplify_expr(boolean_negate(g_copy), ns);
      implications.insert(g_copy);
    }
    else if(g_copy.id()==ID_and)
    {
      exprt copy_last = boolean_negate(g_copy.operands().back());
      simplify(copy_last, ns);
      implications.insert(copy_last);
    }
  }

  slice_SSA_steps(equation, implications); // Slice based on implications

  guardt t_guard;
  symex_targett::sourcet empty_source;
  equation.SSA_steps.emplace_front(
    empty_source, goto_trace_stept::typet::ASSUME);
  symex_target_equationt::SSA_stept &SSA_step=equation.SSA_steps.front();

  SSA_step.guard=t_guard.as_expr();
  SSA_step.ssa_lhs.make_nil();
  SSA_step.cond_expr.swap(trace_condition);

  assign_merges(equation); // Now add the merge variable assignments to eqn

  std::cout << "Finished slicing by trace...\n";
}

void symex_slice_by_tracet::read_trace(std::string filename)
{
  std::cout << "Reading trace from file " << filename << '\n';
  std::ifstream file(filename);
  if(file.fail())
    throw invalid_command_line_argument_exceptiont(
      "invalid file to read trace from: " + filename, "");

  // In case not the first trace read
  alphabet.clear();
  sigma.clear();
  sigma_vals.clear();
  t.clear();

  std::string read_line;
  bool done=false;
  bool begin=true;
  alphabet_parity=true;

  while(!done && !file.eof())
  {
    std::getline(file, read_line);
    if(begin && (read_line=="!"))
      alphabet_parity=false;
    else
      done=parse_alphabet(read_line);
  }

  while(!file.eof())
  {
    std::getline(file, read_line);
    parse_events(read_line);
  }

  for(size_t i=0; i < sigma.size(); i++)
  {
    exprt f_e=static_cast<const exprt &>(get_nil_irep());
    f_e=false_exprt();
    t.push_back(f_e);
  }

  exprt t_e=static_cast<const exprt &>(get_nil_irep());
  t_e=true_exprt();
  t.push_back(t_e);
}

bool symex_slice_by_tracet::parse_alphabet(std::string read_line)
{
  if((read_line==":") || (read_line == ":exact") ||
     (read_line==":suffix") || (read_line == ":exact-suffix") ||
     (read_line==":prefix"))
  {
    semantics=read_line;
    return true;
  }
  else
  {
    std::cout << "Alphabet: ";
    if(!alphabet_parity)
      std::cout << "!";
    std::cout << read_line << '\n';
    alphabet.insert(read_line);
  }
  return false;
}

void symex_slice_by_tracet::parse_events(std::string read_line)
{
  if(read_line=="")
    return;
  bool parity=strstr(read_line.c_str(), "!")==nullptr;
  bool universe=strstr(read_line.c_str(), "?")!=nullptr;
  bool has_values=strstr(read_line.c_str(), " ")!=nullptr;
  std::cout << "Trace: " << read_line << '\n';
  std::vector<irep_idt> value_v;
  if(has_values)
  {
    std::string::size_type sloc=read_line.find(" ", 0);
    std::string values=(read_line.substr(sloc, read_line.size()-1));
    size_t length=values.length();
    for(size_t idx=0; idx < length; idx++)
    {
      const std::string::size_type next=values.find(",", idx);
      std::string value=values.substr(idx, next - idx);
      value_v.push_back(value);
      if(next==std::string::npos)
        break;
      idx=next;
    }
    read_line=read_line.substr(0, sloc);
  }
  sigma_vals.push_back(value_v);
  if(universe)
    parity=false;
  if(!parity)
    read_line=read_line.substr(1, read_line.size()-1);
  std::set<irep_idt> eis;
  size_t vlength=read_line.length();
  for(size_t vidx=0; vidx < vlength; vidx++)
  {
    const std::string::size_type vnext=read_line.find(",", vidx);
    std::string event=read_line.substr(vidx, vnext - vidx);
    eis.insert(event);
    PRECONDITION(!alphabet.empty());
    INVARIANT(
      (alphabet.count(event) != 0) == alphabet_parity,
      "trace uses symbol not in alphabet: " + event);
    if(vnext==std::string::npos)
      break;
    vidx=vnext;
  }
  event_sett es=event_sett(eis, parity);
  sigma.push_back(es);
}

void symex_slice_by_tracet::compute_ts_back(
  symex_target_equationt &equation)
{
  size_t merge_count=0;

  for(symex_target_equationt::SSA_stepst::reverse_iterator
      i=equation.SSA_steps.rbegin();
      i!=equation.SSA_steps.rend();
      i++)
  {
    if(i->is_output() &&
       !i->io_args.empty() &&
       i->io_args.front().id()=="trace_event")
    {
      irep_idt event = i->io_args.front().get(ID_event);

      if(!alphabet.empty())
      {
        bool present=(alphabet.count(event)!=0);
        if(alphabet_parity!=present)
          continue;
      }

      exprt guard=i->guard;

#if 0
      std::cout << "EVENT:  " << event << '\n';
      std::cout << "GUARD:  " << format(guard) << '\n';
      for(size_t j=0; j < t.size(); j++)
      {
        std::cout << "t[" << j << "]=" << format(t[j]) <<
          '\n';
      }
#endif

      bool slice_this=(semantics!=":prefix");
      std::vector<exprt> merge;

      for(size_t j=0; j < t.size(); j++)
      {
        if((t[j].is_true()) || (t[j].is_false()))
        {
          merge.push_back(t[j]);
        }
        else
        {
          ssa_exprt merge_sym(merge_symbol);
          merge_sym.set_level_2(merge_count++);
          exprt t_copy(t[j]);
          merge_map_back.push_back(t_copy);
          std::set<exprt> empty_impls;
          merge_impl_cache_back.push_back
            (std::pair<bool, std::set<exprt> >(false, empty_impls));
          merge.push_back(merge_sym);
        }
      }

      for(size_t j=0; j < t.size(); j++)
      {
        exprt u_lhs=exprt(ID_and, typet(ID_bool));
        if((j < sigma.size()) && (matches(sigma[j], event)))
        {
          u_lhs.operands().reserve(2);
          u_lhs.copy_to_operands(guard);
          if(!sigma_vals[j].empty())
          {
            std::list<exprt> eq_conds;
            std::list<exprt>::iterator pvi=i->io_args.begin();

            for(const auto &sigma_val : sigma_vals[j])
            {
              exprt equal_cond=exprt(ID_equal, bool_typet());
              equal_cond.operands().reserve(2);
              equal_cond.copy_to_operands(*pvi);
              // Should eventually change to handle non-bv types!
              exprt constant_value = from_integer(
                unsafe_string2int(id2string(sigma_val)), (*pvi).type());
              equal_cond.move_to_operands(constant_value);
              eq_conds.push_back(equal_cond);
              pvi++;
            }

            exprt val_merge=exprt(ID_and, typet(ID_bool));
            val_merge.operands().reserve(eq_conds.size()+1);
            val_merge.copy_to_operands(merge[j+1]);

            for(const auto &eq_cond : eq_conds)
            {
              val_merge.copy_to_operands(eq_cond);
            }

            u_lhs.move_to_operands(val_merge);
          }
          else
          {
            u_lhs.copy_to_operands(merge[j+1]);
          }

          simplify(u_lhs, ns);

          if((!u_lhs.is_false()) && implies_false(u_lhs))
            u_lhs=false_exprt();
          if(!u_lhs.is_false())
            slice_this=false;
        }
        else
        {
          u_lhs=false_exprt();
        }
        exprt u_rhs=exprt(ID_and, typet(ID_bool));
        if((semantics!=":suffix") || (j != 0))
        {
          u_rhs.add_to_operands(boolean_negate(guard), merge[j]);
        }
        else
        {
          u_rhs.swap(merge[j]);
        }
        exprt u_j=exprt(ID_or, typet(ID_bool));
        u_j.operands().reserve(2);
        u_j.copy_to_operands(u_lhs);
        u_j.copy_to_operands(u_rhs);

        simplify(u_j, ns);

        t[j]=u_j;
      }

      if(semantics==":prefix")
        t[t.size()-1]=true_exprt();

      if(slice_this)
      {
        exprt guard_copy(guard);

        sliced_guards.insert(guard_copy);
      }
    }
  }
}

void symex_slice_by_tracet::slice_SSA_steps(
  symex_target_equationt &equation,
  std::set<exprt> implications)
{
  // Some statistics for our benefit.
  size_t conds_seen=0;
  size_t sliced_SSA_steps=0;
  size_t potential_SSA_steps=0;
  size_t sliced_conds=0;
  size_t trace_SSA_steps=0;
  size_t location_SSA_steps=0;
  size_t trace_loc_sliced=0;

  for(auto &SSA_step : equation.SSA_steps)
  {
    if(SSA_step.is_output())
      trace_SSA_steps++;
    if(SSA_step.is_location())
      location_SSA_steps++;
    bool sliced_SSA_step=false;
    exprt guard = SSA_step.guard;

    simplify(guard, ns);

    if(!guard.is_true())
      potential_SSA_steps++;
    // SSA_step.output(ns,std::cout);
    // std::cout << "-----------------\n";

    if((guard.id()==ID_symbol) || (guard.id() == ID_not))
    {
      guard = simplify_expr(boolean_negate(guard), ns);

      if(implications.count(guard)!=0)
      {
        SSA_step.cond_expr = true_exprt();
        SSA_step.ssa_rhs = true_exprt();
        SSA_step.guard = false_exprt();
        sliced_SSA_steps++;
        if(SSA_step.is_output() || SSA_step.is_location())
          trace_loc_sliced++;
        sliced_SSA_step=true;
      }
    }
    else if(guard.id()==ID_and)
    {
      Forall_operands(git, guard)
      {
        exprt neg_expr = boolean_negate(*git);
        simplify(neg_expr, ns);

        if(implications.count(neg_expr)!=0)
        {
          SSA_step.cond_expr = true_exprt();
          SSA_step.ssa_rhs = true_exprt();
          SSA_step.guard = false_exprt();
          sliced_SSA_steps++;
          if(SSA_step.is_output() || SSA_step.is_location())
            trace_loc_sliced++;
          sliced_SSA_step=true;
          break; // Sliced, so no need to consider the rest
        }
      }
      else if(guard.id()==ID_or)
      {
        std::cout << "Guarded by an OR.\n";
      }
    }

    if(!sliced_SSA_step && SSA_step.is_assignment())
    {
      if(SSA_step.ssa_rhs.id() == ID_if)
      {
        conds_seen++;
        exprt cond_copy(to_if_expr(SSA_step.ssa_rhs).cond());
        simplify(cond_copy, ns);

        if(implications.count(cond_copy)!=0)
        {
          sliced_conds++;
          exprt t_copy1(to_if_expr(SSA_step.ssa_rhs).true_case());
          exprt t_copy2(to_if_expr(SSA_step.ssa_rhs).true_case());
          SSA_step.ssa_rhs = t_copy1;
          SSA_step.cond_expr.op1().swap(t_copy2);
        }
        else
        {
          cond_copy = simplify_expr(boolean_negate(cond_copy), ns);
          if(implications.count(cond_copy)!=0)
          {
            sliced_conds++;
            exprt f_copy1(to_if_expr(SSA_step.ssa_rhs).false_case());
            exprt f_copy2(to_if_expr(SSA_step.ssa_rhs).false_case());
            SSA_step.ssa_rhs = f_copy1;
            SSA_step.cond_expr.op1().swap(f_copy2);
          }
        }
      }
    }
  }

  std::cout << "Trace slicing effectively removed "
            << (sliced_SSA_steps + sliced_conds) << " out of "
            << equation.SSA_steps.size() << " SSA_steps.\n";
  std::cout << "  ("
                << ((sliced_SSA_steps + sliced_conds) - trace_loc_sliced)
            << " out of "
            << (equation.SSA_steps.size()-trace_SSA_steps-location_SSA_steps)
            << " non-trace, non-location SSA_steps)\n";
}

bool symex_slice_by_tracet::matches(
  event_sett s,
  irep_idt event)
{
  bool present=s.first.count(event)!=0;
  return ((s.second && present) || (!s.second && !present));
}

void symex_slice_by_tracet::assign_merges(
  symex_target_equationt &equation)
{
  size_t merge_count=(merge_map_back.size()) - 1;
  for(std::vector<exprt>::reverse_iterator i=merge_map_back.rbegin();
      i!=merge_map_back.rend(); i++)
  {
    ssa_exprt merge_sym(merge_symbol);
    merge_sym.set_level_2(merge_count);
    merge_count--;
    guardt t_guard;
    symex_targett::sourcet empty_source;

    exprt merge_copy(*i);

    equation.SSA_steps.emplace_front(
      empty_source, goto_trace_stept::typet::ASSIGNMENT);
    symex_target_equationt::SSA_stept &SSA_step=equation.SSA_steps.front();

    SSA_step.guard=t_guard.as_expr();
    SSA_step.ssa_lhs=merge_sym;
    SSA_step.ssa_rhs.swap(merge_copy);
    SSA_step.assignment_type=symex_targett::assignment_typet::HIDDEN;

    SSA_step.cond_expr=equal_exprt(SSA_step.ssa_lhs, SSA_step.ssa_rhs);
  }
}

std::set<exprt> symex_slice_by_tracet::implied_guards(exprt e)
{
  std::set<exprt> s;

  if(e.id()==ID_symbol)
  { // Guard or merge
    const std::string &id_string =
      id2string(to_symbol_expr(e).get_identifier());

    std::string::size_type merge_loc=id_string.find("merge#");

    if(merge_loc==std::string::npos)
    {
      exprt e_copy(e);
      simplify(e_copy, ns);
      s.insert(e_copy);
      return s;
    }
    else
    {
      const std::size_t i = unsafe_string2size_t(id_string.substr(merge_loc+6));
      if(merge_impl_cache_back[i].first)
      {
        return merge_impl_cache_back[i].second;
      }
      else
      {
        merge_impl_cache_back[i].first=true;
        exprt merge_copy(merge_map_back[i]);
        merge_impl_cache_back[i].second=implied_guards(merge_copy);
        return merge_impl_cache_back[i].second;
      }
    }
  }
  else if(e.id()==ID_not)
  { // Definitely a guard
    exprt e_copy(e);
    simplify(e_copy, ns);
    s.insert(e_copy);
    return s;
  }
  else if(e.id()==ID_and)
  { // Descend into and
    for(const auto &conjunct : e.operands())
    {
      const auto imps = implied_guards(conjunct);
      for(const auto &guard : imps)
        s.insert(guard);
    }

    return s;
  }
  else if(e.id()==ID_or)
  { // Descend into or
    std::vector<std::set<exprt> > rs;
    Forall_operands(it, e)
    {
      rs.push_back(implied_guards(*it));
    }
    for(std::set<exprt>::iterator i=rs.front().begin();
        i!=rs.front().end();)
    {
      for(std::vector<std::set<exprt> >::iterator j=rs.begin();
          j!=rs.end(); j++)
      {
        if(j==rs.begin())
          j++;
        std::set<exprt>::iterator k=i;
        i++;
        if(j->count(*k)==0)
        {
          rs.front().erase(k);
          break;
        }
      }
    }
    s=rs.front();
    return s;
  }

  return s;
}

bool symex_slice_by_tracet::implies_false(const exprt e)
{
  std::set<exprt> imps=implied_guards(e);

  for(const auto &implied_guard : imps)
  {
    exprt i_copy = boolean_negate(implied_guard);
    simplify(i_copy, ns);
    if(imps.count(i_copy)!=0)
      return true;
  }

  return false;
}
