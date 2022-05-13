/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#include "cone_of_influence.h"

void cone_of_influencet::cone_of_influence(
  const expr_sett &targets,
  expr_sett &cone)
{
  if(program.instructions.empty())
  {
    cone=targets;
    return;
  }

  for(goto_programt::instructionst::const_reverse_iterator
      rit=program.instructions.rbegin();
      rit != program.instructions.rend();
      ++rit)
  {
    expr_sett curr; // =targets;
    expr_sett next;

    if(rit == program.instructions.rbegin())
    {
      curr=targets;
    }
    else
    {
      get_succs(rit, curr);
    }

    cone_of_influence(*rit, curr, next);

    cone_map[rit->location_number]=next;

#ifdef DEBUG
    std::cout << "Previous cone: \n";

    for(const auto &expr : curr)
      std::cout << expr2c(expr, ns) << " ";

    std::cout << "\nCurrent cone: \n";

    for(const auto &expr : next)
      std::cout << expr2c(expr, ns) << " ";

    std::cout << '\n';
#endif
  }

  cone=cone_map[program.instructions.front().location_number];
}

void cone_of_influencet::cone_of_influence(
  const exprt &target,
  expr_sett &cone)
{
  expr_sett s;
  s.insert(target);
  cone_of_influence(s, cone);
}

void cone_of_influencet::get_succs(
  goto_programt::instructionst::const_reverse_iterator rit,
  expr_sett &targets)
{
  if(rit == program.instructions.rbegin())
  {
    return;
  }

  goto_programt::instructionst::const_reverse_iterator next=rit;
  --next;

  if(rit->is_goto())
  {
    if(!rit->condition().is_false())
    {
      // Branch can be taken.
      for(goto_programt::targetst::const_iterator t=rit->targets.begin();
          t != rit->targets.end();
          ++t)
      {
        unsigned int loc=(*t)->location_number;
        expr_sett &s=cone_map[loc];
        targets.insert(s.begin(), s.end());
      }
    }

    if(rit->condition().is_true())
    {
      return;
    }
  }
  else if(rit->is_assume() || rit->is_assert())
  {
    if(rit->condition().is_false())
    {
      return;
    }
  }

  unsigned int loc=next->location_number;
  expr_sett &s=cone_map[loc];
  targets.insert(s.begin(), s.end());
}

void cone_of_influencet::cone_of_influence(
  const goto_programt::instructiont &i,
  const expr_sett &curr,
  expr_sett &next)
{
  next.insert(curr.begin(), curr.end());

  if(i.is_assign())
  {
    expr_sett lhs_syms;
    bool care=false;

    gather_rvalues(i.assign_lhs(), lhs_syms);

    for(const auto &expr : lhs_syms)
      if(curr.find(expr)!=curr.end())
      {
        care=true;
        break;
      }

    next.erase(i.assign_lhs());

    if(care)
    {
      gather_rvalues(i.assign_rhs(), next);
    }
  }
}

void cone_of_influencet::gather_rvalues(const exprt &expr, expr_sett &rvals)
{
  if(expr.id() == ID_symbol ||
     expr.id() == ID_index ||
     expr.id() == ID_member ||
     expr.id() == ID_dereference)
  {
    rvals.insert(expr);
  }
  else
  {
    forall_operands(it, expr)
    {
      gather_rvalues(*it, rvals);
    }
  }
}
