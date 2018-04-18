/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#include "overflow_instrumenter.h"

#include <iostream>

#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>

#include <goto-programs/goto_program.h>

#include "util.h"

/*
 * This code is copied wholesale from analyses/goto_check.cpp.
 */


void overflow_instrumentert::add_overflow_checks()
{
  goto_programt::targett init_overflow=program.insert_before(
      program.instructions.begin());
  init_overflow->make_assignment();
  init_overflow->code=code_assignt(overflow_var, false_exprt());

  program.compute_location_numbers();
  checked.clear();

  Forall_goto_program_instructions(it, program)
  {
    add_overflow_checks(it);
  }
}

void overflow_instrumentert::add_overflow_checks(
  goto_programt::targett t,
  goto_programt::targetst &added)
{
  if(checked.find(t->location_number)!=checked.end())
  {
    return;
  }

  if(t->is_assign())
  {
    code_assignt &assignment=to_code_assign(t->code);

    if(assignment.lhs()==overflow_var)
    {
      return;
    }

    add_overflow_checks(t, assignment.lhs(), added);
    add_overflow_checks(t, assignment.rhs(), added);
  }

  add_overflow_checks(t, t->guard, added);

  checked.insert(t->location_number);
}

void overflow_instrumentert::add_overflow_checks(
  goto_programt::targett t)
{
  goto_programt::targetst ignore;
  add_overflow_checks(t, ignore);
}

void overflow_instrumentert::add_overflow_checks(
  goto_programt::targett t,
  const exprt &expr,
  goto_programt::targetst &added)
{
  exprt overflow;
  overflow_expr(expr, overflow);

  if(overflow!=false_exprt())
  {
    accumulate_overflow(t, overflow, added);
  }
}

void overflow_instrumentert::overflow_expr(
  const exprt &expr,
  expr_sett &cases)
{
  forall_operands(it, expr)
  {
    overflow_expr(*it, cases);
  }

  const typet &type=ns.follow(expr.type());

  if(expr.id()==ID_typecast)
  {
    if(expr.op0().id()==ID_constant)
    {
      return;
    }

    const typet &old_type=ns.follow(expr.op0().type());
    const std::size_t new_width = to_bitvector_type(expr.type()).get_width();
    const std::size_t old_width = to_bitvector_type(old_type).get_width();

    if(type.id()==ID_signedbv)
    {
      if(old_type.id()==ID_signedbv)
      {
        // signed -> signed
        if(new_width >= old_width)
        {
          // Always safe.
          return;
        }

        cases.insert(
          binary_relation_exprt(expr.op0(), ID_gt,
            from_integer(power(2, new_width - 1) - 1, old_type)));

        cases.insert(
            binary_relation_exprt(expr.op0(), ID_lt,
              from_integer(-power(2, new_width - 1), old_type)));
      }
      else if(old_type.id()==ID_unsignedbv)
      {
        // unsigned -> signed
        if(new_width >= old_width + 1)
        {
          // Always safe.
          return;
        }

        cases.insert(
            binary_relation_exprt(expr.op0(), ID_gt,
              from_integer(power(2, new_width - 1) - 1, old_type)));
      }
    }
    else if(type.id()==ID_unsignedbv)
    {
      if(old_type.id()==ID_signedbv)
      {
        // signed -> unsigned
        cases.insert(
            binary_relation_exprt(expr.op0(), ID_lt,
              from_integer(0, old_type)));
        if(new_width < old_width - 1)
        {
          // Need to check for overflow as well as signedness.
          cases.insert(
              binary_relation_exprt(expr.op0(), ID_gt,
                from_integer(power(2, new_width - 1) - 1, old_type)));
        }
      }
      else if(old_type.id()==ID_unsignedbv)
      {
        // unsigned -> unsigned
        if(new_width>=old_width)
        {
          // Always safe.
          return;
        }

        cases.insert(
            binary_relation_exprt(expr.op0(), ID_gt,
              from_integer(power(2, new_width - 1) - 1, old_type)));
      }
    }
  }
  else if(expr.id()==ID_div)
  {
    // Undefined for signed INT_MIN / -1
    if(type.id()==ID_signedbv)
    {
      equal_exprt int_min_eq(
        expr.op0(), to_signedbv_type(type).smallest_expr());
      equal_exprt minus_one_eq(expr.op1(), from_integer(-1, type));

      cases.insert(and_exprt(int_min_eq, minus_one_eq));
    }
  }
  else if(expr.id()==ID_unary_minus)
  {
    if(type.id()==ID_signedbv)
    {
      // Overflow on unary- can only happen with the smallest
      // representable number.
      cases.insert(
          equal_exprt(expr.op0(),
            to_signedbv_type(type).smallest_expr()));
    }
  }
  else if(expr.id()==ID_plus ||
          expr.id()==ID_minus ||
          expr.id()==ID_mult)
  {
    // A generic arithmetic operation.
    exprt overflow("overflow-" + expr.id_string(), bool_typet());
    overflow.operands()=expr.operands();

    if(expr.operands().size()>=3)
    {
      // The overflow checks are binary.
      for(std::size_t i=1; i<expr.operands().size(); i++)
      {
        exprt tmp;

        if(i==1)
        {
          tmp=expr.op0();
        }
        else
        {
          tmp=expr;
          tmp.operands().resize(i);
        }

        overflow.operands().resize(2);
        overflow.op0()=tmp;
        overflow.op1()=expr.operands()[i];

        fix_types(overflow);

        cases.insert(overflow);
      }
    }
    else
    {
      fix_types(overflow);
      cases.insert(overflow);
    }
  }
}

void overflow_instrumentert::overflow_expr(const exprt &expr, exprt &overflow)
{
  expr_sett cases;

  overflow_expr(expr, cases);

  overflow=false_exprt();

  for(expr_sett::iterator it=cases.begin();
      it!=cases.end();
      ++it)
  {
    if(overflow==false_exprt())
    {
      overflow=*it;
    }
    else
    {
      overflow=or_exprt(overflow, *it);
    }
  }
}

void overflow_instrumentert::fix_types(exprt &overflow)
{
  typet &t1=overflow.op0().type();
  typet &t2=overflow.op1().type();
  const typet &t=join_types(t1, t2);

  if(t1!=t)
  {
    overflow.op0()=typecast_exprt(overflow.op0(), t);
  }

  if(t2!=t)
  {
    overflow.op1()=typecast_exprt(overflow.op1(), t);
  }
}

void overflow_instrumentert::accumulate_overflow(
  goto_programt::targett t,
  const exprt &expr,
  goto_programt::targetst &added)
{
  goto_programt::instructiont a(ASSIGN);
  a.code=code_assignt(overflow_var, or_exprt(overflow_var, expr));
  goto_programt::targett assignment=program.insert_after(t);
  *assignment=a;
  assignment->swap(*t);

  added.push_back(assignment);
}
