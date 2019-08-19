/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#include "scratch_program.h"

#include <util/fixedbv.h>

#include <solvers/decision_procedure.h>

#include <goto-symex/slice.h>

#include <goto-programs/remove_skip.h>

#ifdef DEBUG
#include <iostream>
#endif

bool scratch_programt::check_sat(bool do_slice, guard_managert &guard_manager)
{
  fix_types();

  add(goto_programt::make_end_function());

  remove_skip(*this);

#ifdef DEBUG
  std::cout << "Checking following program for satness:\n";
  output(ns, "scratch", std::cout);
#endif

  symex_state = util_make_unique<goto_symex_statet>(
    symex_targett::sourcet(goto_functionst::entry_point(), *this),
    DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE,
    guard_manager,
    [this](const irep_idt &id) {
      return path_storage.get_unique_l2_index(id);
    });

  symex.symex_with_state(
    *symex_state,
    [this](const irep_idt &key) -> const goto_functionst::goto_functiont & {
      return functions.function_map.at(key);
    },
    symex_symbol_table);

  if(do_slice)
  {
    slice(equation);
  }

  if(equation.count_assertions()==0)
  {
    // Symex sliced away all our assertions.
#ifdef DEBUG
    std::cout << "Trivially unsat\n";
#endif
    return false;
  }

  equation.convert(*checker);

#ifdef DEBUG
  std::cout << "Finished symex, invoking decision procedure.\n";
#endif

  return ((*checker)() == decision_proceduret::resultt::D_SATISFIABLE);
}

exprt scratch_programt::eval(const exprt &e)
{
  return checker->get(symex_state->rename<L2>(e, ns).get());
}

void scratch_programt::append(goto_programt::instructionst &new_instructions)
{
  instructions.insert(
    instructions.end(),
    new_instructions.begin(),
    new_instructions.end());
}

goto_programt::targett scratch_programt::assign(
  const exprt &lhs,
  const exprt &rhs)
{
  return add(goto_programt::make_assignment(lhs, rhs));
}

goto_programt::targett scratch_programt::assume(const exprt &guard)
{
  return add(goto_programt::make_assumption(guard));
}

static void fix_types(exprt &expr)
{
  Forall_operands(it, expr)
  {
    fix_types(*it);
  }

  if(expr.id()==ID_equal ||
     expr.id()==ID_notequal ||
     expr.id()==ID_gt ||
     expr.id()==ID_lt ||
     expr.id()==ID_ge ||
     expr.id()==ID_le)
  {
    auto &rel_expr = to_binary_relation_expr(expr);
    exprt &lhs = rel_expr.lhs();
    exprt &rhs = rel_expr.rhs();

    if(lhs.type()!=rhs.type())
    {
      typecast_exprt typecast(rhs, lhs.type());
      rel_expr.rhs().swap(typecast);
    }
  }
}

void scratch_programt::fix_types()
{
  for(goto_programt::instructionst::iterator it=instructions.begin();
      it!=instructions.end();
      ++it)
  {
    if(it->is_assign())
    {
      code_assignt &code=to_code_assign(it->code);

      if(code.lhs().type()!=code.rhs().type())
      {
        typecast_exprt typecast(code.rhs(), code.lhs().type());
        code.rhs()=typecast;
      }
    }
    else if(it->is_assume() || it->is_assert())
    {
      exprt cond = it->get_condition();
      ::fix_types(cond);
      it->set_condition(cond);
    }
  }
}

void scratch_programt::append_path(patht &path)
{
  for(patht::iterator it=path.begin();
      it!=path.end();
      ++it)
  {
    if(it->loc->is_assign() || it->loc->is_assume())
    {
      instructions.push_back(*it->loc);
    }
    else if(it->loc->is_goto())
    {
      if(it->guard.id()!=ID_nil)
      {
        add(goto_programt::make_assumption(it->guard));
      }
    }
    else if(it->loc->is_assert())
    {
      add(goto_programt::make_assumption(it->loc->get_condition()));
    }
  }
}

void scratch_programt::append(goto_programt &program)
{
  goto_programt scratch;

  scratch.copy_from(program);
  destructive_append(scratch);
}

void scratch_programt::append_loop(
  goto_programt &program,
  goto_programt::targett loop_header)
{
  append(program);

  // Update any back jumps to the loop header.
  (void)loop_header; // unused parameter
  assume(false_exprt());

  goto_programt::targett end = add(goto_programt::make_skip());

  update();

  for(goto_programt::targett t=instructions.begin();
      t!=instructions.end();
      ++t)
  {
    if(t->is_backwards_goto())
    {
      t->targets.clear();
      t->targets.push_back(end);
    }
  }
}

optionst scratch_programt::get_default_options()
{
  optionst ret;
  ret.set_option("simplify", true);
  return ret;
}
