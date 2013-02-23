#include <i2string.h>
#include <fixedbv.h>
#include <decision_procedure.h>

#include <goto-symex/slice.h>


#include "scratch_program.h"

//#define DEBUG

static int num_symbols;

symbolt scratch_programt::fresh_symbol(string base) {
  string name = base + "_" + i2string(num_symbols++);
  symbolt ret;
  ret.module = "scratch";
  ret.name = name;
  ret.base_name = name;
  ret.pretty_name = name;
  ret.type = signedbv_typet(32);

  shadow_symbol_table.add(ret);

  return ret;
}

bool scratch_programt::check_sat() {
  fix_types();

  add_instruction(END_FUNCTION);

#ifdef DEBUG
  cout << "Checking following program for satness:" << endl;
  output(ns, "scratch", cout);
#endif

  symex.constant_propagation = constant_propagation;
  goto_symex_statet::propagationt::valuest constants;

  symex(symex_state, functions, *this);
  slice(equation);
  equation.convert(checker);

  return (checker.dec_solve() == decision_proceduret::D_SATISFIABLE);
}

exprt scratch_programt::eval(exprt &e) {
  exprt ssa = e;

  symex_state.rename(ssa, ns);

  return checker.get(ssa);
}

void scratch_programt::append(goto_programt::instructionst &new_instructions) {
  instructions.insert(instructions.end(),
                      new_instructions.begin(), new_instructions.end());
}

goto_programt::targett scratch_programt::assign(const exprt &lhs, const exprt &rhs) {
  code_assignt assignment(lhs, rhs);
  targett instruction = add_instruction(ASSIGN);
  instruction->code = assignment;

  return instruction;
}

goto_programt::targett scratch_programt::assume(const exprt &guard) {
  targett instruction = add_instruction(ASSUME);
  instruction->guard = guard;

  return instruction;
}

static void fix_types(exprt &expr) {
  Forall_operands (it, expr) {
    fix_types(*it);
  }

  if (expr.id() == ID_equal) {
    equal_exprt &equal = to_equal_expr(expr);
    exprt &lhs = equal.lhs();
    exprt &rhs = equal.rhs();

    if (lhs.type() != rhs.type()) {
      typecast_exprt typecast(rhs, lhs.type());
      equal.rhs() = typecast;
      expr = equal;
    }
  }
}

void scratch_programt::fix_types() {
  for (goto_programt::instructionst::iterator it = instructions.begin();
       it != instructions.end();
       ++it) {
    if (it->is_assign()) {
      code_assignt &code = to_code_assign(it->code);

      if (code.lhs().type() != code.rhs().type()) {
        typecast_exprt typecast(code.rhs(), code.lhs().type());
        code.rhs() = typecast;
      }
    } else if (it->is_assume() || it->is_assert()) {
      ::fix_types(it->guard);
    }
  }
}
