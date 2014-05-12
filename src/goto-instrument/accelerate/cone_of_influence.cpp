#include <iostream>

#include <ansi-c/expr2c.h>

#include "cone_of_influence.h"

//#define DEBUG

void cone_of_influencet::cone_of_influence(const expr_sett &targets,
    expr_sett &cone) {
  if (program.instructions.empty()) {
    cone = targets;
    return;
  }

  for (goto_programt::instructionst::const_reverse_iterator rit =
          program.instructions.rbegin();
       rit != program.instructions.rend();
       ++rit) {
    expr_sett curr;// = targets;
    expr_sett next;

    if (rit == program.instructions.rbegin()) {
      curr = targets;
    } else {
      get_succs(rit, curr);
    }

    cone_of_influence(*rit, curr, next);

    cone_map[rit->location_number] = next;

#ifdef DEBUG
    std::cout << "Previous cone: " << std::endl;
    
    for (expr_sett::iterator it = curr.begin();
         it != curr.end();
         ++it) {
      std::cout << expr2c(*it, ns) << " ";
    }

    std::cout << std::endl << "Current cone: " << std::endl;
    
    for (expr_sett::iterator it = next.begin();
         it != next.end();
         ++it) {
      std::cout << expr2c(*it, ns) << " ";
    }

    std::cout << std::endl;
#endif
  }

  cone = cone_map[program.instructions.front().location_number];
}

void cone_of_influencet::cone_of_influence(const exprt &target,
    expr_sett &cone) {
  expr_sett s;
  s.insert(target);
  cone_of_influence(s, cone);
}

void cone_of_influencet::get_succs(
    goto_programt::instructionst::const_reverse_iterator rit,
    expr_sett &targets) {
  if (rit == program.instructions.rbegin()) {
    return;
  }

  goto_programt::instructionst::const_reverse_iterator next = rit;
  --next;

  if (rit->is_goto()) {
    if (!rit->guard.is_false()) {
      // Branch can be taken.
      for (goto_programt::targetst::const_iterator t = rit->targets.begin();
           t != rit->targets.end();
           ++t) {
        unsigned int loc = (*t)->location_number;
        expr_sett &s = cone_map[loc];
        targets.insert(s.begin(), s.end());
      }
    }

    if (rit->guard.is_true()) {
      return;
    }
  } else if (rit->is_assume() || rit->is_assert()) {
    if (rit->guard.is_false()) {
      return;
    }
  }
  
  unsigned int loc = next->location_number;
  expr_sett &s = cone_map[loc];
  targets.insert(s.begin(), s.end());
}

void cone_of_influencet::cone_of_influence(
    const goto_programt::instructiont &i,
    const expr_sett &curr,
    expr_sett &next) {
  next.insert(curr.begin(), curr.end());

  if (i.is_assign()) {
    const code_assignt &assignment = to_code_assign(i.code);
    expr_sett lhs_syms;
    bool care = false;

    gather_rvalues(assignment.lhs(), lhs_syms);

    for (expr_sett::iterator it = lhs_syms.begin();
         it != lhs_syms.end();
         ++it) {
      if (curr.find(*it) != curr.end()) {
        care = true;
        break;
      }
    }

    next.erase(assignment.lhs());

    if (care) {
      gather_rvalues(assignment.rhs(), next);
    }
  }
}

void cone_of_influencet::gather_rvalues(const exprt &expr, expr_sett &rvals) {
  if (expr.id() == ID_symbol ||
      expr.id() == ID_index ||
      expr.id() == ID_member ||
      expr.id() == ID_dereference) {
    rvals.insert(expr);
  } else {
    forall_operands(it, expr) {
      gather_rvalues(*it, rvals);
    }
  }
}
