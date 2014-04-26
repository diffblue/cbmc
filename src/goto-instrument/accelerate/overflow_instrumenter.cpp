#include <iostream>

#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/arith_tools.h>

#include <goto-programs/goto_program.h>

#include "overflow_instrumenter.h"

/*
 * This code is copied wholesale from analyses/goto_check.cpp.
 */


void overflow_instrumentert::add_overflow_checks() {
  goto_programt::targett init_overflow = program.insert_before(
      program.instructions.begin());
  init_overflow->make_assignment();
  init_overflow->code = code_assignt(overflow_var, false_exprt());

  program.compute_location_numbers();
  checked.clear();

  Forall_goto_program_instructions(it, program) {
    add_overflow_checks(it);
  }
}

void overflow_instrumentert::add_overflow_checks(goto_programt::targett t) {
  if (checked.find(t->location_number) != checked.end()) {
    return;
  }

  if (t->is_assign()) {
    code_assignt &assignment = to_code_assign(t->code);

    if (assignment.lhs() == overflow_var) {
      return;
    }

    add_overflow_checks(t, assignment.lhs());
    add_overflow_checks(t, assignment.rhs());
  }

  add_overflow_checks(t, t->guard);

  checked.insert(t->location_number);
}

void overflow_instrumentert::add_overflow_checks(goto_programt::targett t,
                                                 const exprt &expr) {
  forall_operands(it, expr) {
    add_overflow_checks(t, *it);
  }

  const typet &type = ns.follow(expr.type());

  if (expr.id() == ID_typecast) {
    const typet &old_type = ns.follow(expr.op0().type());
    unsigned new_width = expr.type().get_int(ID_width);
    unsigned old_width = old_type.get_int(ID_width);

    if (type.id() == ID_signedbv) {
      if (old_type.id() == ID_signedbv) {
        // signed -> signed
        if (new_width >= old_width) {
          // Always safe.
          return;
        }

        accumulate_overflow(t,
            binary_relation_exprt(expr.op0(), ID_gt,
              from_integer(power(2, new_width - 1) - 1, old_type)));

        accumulate_overflow(t,
            binary_relation_exprt(expr.op0(), ID_lt,
              from_integer(-power(2, new_width - 1), old_type)));
      } else if (old_type.id() == ID_unsignedbv) {
        // unsigned -> signed
        if (new_width >= old_width + 1) {
          // Always safe.
          return;
        }

        accumulate_overflow(t,
            binary_relation_exprt(expr.op0(), ID_gt,
              from_integer(power(2, new_width - 1) - 1, old_type)));
      }
    } else if (type.id() == ID_unsignedbv) {
      if (old_type.id() == ID_signedbv) {
        // signed -> unsigned
        accumulate_overflow(t,
            binary_relation_exprt(expr.op0(), ID_lt,
              from_integer(0, old_type)));
        if (new_width < old_width - 1) {
          // Need to check for overflow as well as signedness.
          accumulate_overflow(t,
              binary_relation_exprt(expr.op0(), ID_gt,
                from_integer(power(2, new_width - 1) - 1, old_type)));
        }
      } else if (old_type.id() == ID_unsignedbv) {
        // unsigned -> unsigned
        if (new_width >= old_width) {
          // Always safe.
          return;
        }

        accumulate_overflow(t,
            binary_relation_exprt(expr.op0(), ID_gt,
              from_integer(power(2, new_width - 1) - 1, old_type)));
      }
    }
  } else if (expr.id() == ID_div) {
    // Undefined for signed INT_MIN / -1
    if (type.id() == ID_signedbv) {
      equal_exprt int_min_eq(expr.op0(), to_signedbv_type(type).smallest_expr());
      equal_exprt minus_one_eq(expr.op1(), from_integer(-1, type));
      accumulate_overflow(t, and_exprt(int_min_eq, minus_one_eq));
    }
  } else if (expr.id() == ID_unary_minus) {
    if (type.id() == ID_signedbv) {
      // Overflow on unary- can only happen with the smallest representable number.
      accumulate_overflow(t,
          equal_exprt(expr.op0(),
            to_signedbv_type(type).smallest_expr()));
    }
  } else if (expr.id() == ID_plus ||
             expr.id() == ID_minus ||
             expr.id() == ID_mult) {
    // A generic arithmetic operation.
    exprt overflow("overflow-" + expr.id_string(), bool_typet());
    overflow.operands() = expr.operands();

    if (expr.operands().size() >= 3) {
      // The overflow checks are binary.
      for (unsigned i = 1; i < expr.operands().size(); i++) {
        exprt tmp;

        if (i == 1) {
          tmp = expr.op0();
        } else {
          tmp = expr;
          tmp.operands().resize(i);
        }

        overflow.operands().resize(2);
        overflow.op0() = tmp;
        overflow.op1() = expr.operands()[i];

        accumulate_overflow(t, overflow);
      }
    } else {
      accumulate_overflow(t, overflow);
    }
  }
}

void overflow_instrumentert::accumulate_overflow(goto_programt::targett t,
                                                 const exprt &expr) {
  goto_programt::instructiont a(ASSIGN);
  a.code = code_assignt(overflow_var, or_exprt(overflow_var, expr));
  program.insert_before_swap(t, a);
  return;

  goto_programt::targett assignment = program.insert_before(t);
  *assignment = a;
}
