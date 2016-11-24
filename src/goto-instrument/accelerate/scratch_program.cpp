#include <util/i2string.h>
#include <util/fixedbv.h>
#include <util/decision_procedure.h>

#include <goto-symex/slice.h>

#include <goto-programs/remove_skip.h>

#include "scratch_program.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

bool scratch_programt::check_sat(bool do_slice)
{
  fix_types();

  add_instruction(END_FUNCTION);

  remove_skip(*this);
  update();

#ifdef DEBUG
  cout << "Checking following program for satness:" << endl;
  output(ns, "scratch", cout);
#endif

  symex.constant_propagation = constant_propagation;
  goto_symex_statet::propagationt::valuest constants;

  symex(symex_state, functions, *this);

  if (do_slice) {
    slice(equation);
  }

  if (equation.count_assertions() == 0) {
    // Symex sliced away all our assertions.
#ifdef DEBUG
    std::cout << "Trivially unsat" << std::endl;
#endif
    return false;
  }

  equation.convert(*checker);

#ifdef DEBUG
  cout << "Finished symex, invoking decision procedure." << endl;
#endif

  return (checker->dec_solve() == decision_proceduret::D_SATISFIABLE);
}

exprt scratch_programt::eval(const exprt &e) {
  exprt ssa = e;

  symex_state.rename(ssa, ns);

  return checker->get(ssa);
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

  if (expr.id() == ID_equal ||
      expr.id() == ID_notequal ||
      expr.id() == ID_gt ||
      expr.id() == ID_lt ||
      expr.id() == ID_ge ||
      expr.id() == ID_le) {
    exprt &lhs = expr.op0();
    exprt &rhs = expr.op1();

    if (lhs.type() != rhs.type()) {
      typecast_exprt typecast(rhs, lhs.type());
      expr.op1().swap(typecast);
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

void scratch_programt::append_path(patht &path) {
  for (patht::iterator it = path.begin();
       it != path.end();
       ++it) {
    if (it->loc->is_assign() || it->loc->is_assume()) {
      instructions.push_back(*it->loc);
    } else if (it->loc->is_goto()) {
      if (it->guard.id() != ID_nil) {
        add_instruction(ASSUME)->guard = it->guard;
      }
    } else if (it->loc->is_assert()) {
      add_instruction(ASSUME)->guard = it->loc->guard;
    }
  }
}

void scratch_programt::append(goto_programt &program) {
  goto_programt scratch;

  scratch.copy_from(program);
  destructive_append(scratch);
}

void scratch_programt::append_loop(goto_programt &program,
    goto_programt::targett loop_header) {
  append(program);

  // Update any back jumps to the loop header.
  assume(false_exprt());

  goto_programt::targett end = add_instruction(SKIP);

  update();

  for (goto_programt::targett t = instructions.begin();
       t != instructions.end();
       ++t) {
    if (t->is_backwards_goto()) {
      t->targets.clear();
      t->targets.push_back(end);
    }
  }
}
