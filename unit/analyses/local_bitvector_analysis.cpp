/*******************************************************************\

Module: Unit tests for local_bitvector_analysist

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Unit tests for local_bitvector_analysist

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <goto-programs/goto_model.h>

#include <analyses/local_bitvector_analysis.h>
#include <ansi-c/goto-conversion/goto_convert_functions.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "local_bitvector_analysis pointer-typed plus with 3+ operands",
  "[core][analyses][local_bitvector_analysis]")
{
  const pointer_typet ptr_type = pointer_type(signed_int_type());

  GIVEN("A 3-operand plus with pointer at op0")
  {
    goto_modelt goto_model;

    symbolt local_p{"main::p", ptr_type, ID_C};
    local_p.is_lvalue = true;
    symbolt local_q{"main::q", ptr_type, ID_C};
    local_q.is_lvalue = true;

    // q = p + 1 + 2  (pointer is op0)
    exprt::operandst ops;
    ops.push_back(local_p.symbol_expr());
    ops.push_back(from_integer(1, signed_int_type()));
    ops.push_back(from_integer(2, signed_int_type()));
    plus_exprt plus_op0_ptr(std::move(ops), ptr_type);

    code_blockt code(
      {code_declt(local_p.symbol_expr()),
       code_declt(local_q.symbol_expr()),
       code_assignt(local_q.symbol_expr(), plus_op0_ptr)});

    symbolt main_sym{"main", code_typet({}, empty_typet()), ID_C};
    main_sym.value = code;

    goto_model.symbol_table.add(local_p);
    goto_model.symbol_table.add(local_q);
    goto_model.symbol_table.add(main_sym);
    goto_convert(goto_model, null_message_handler);

    const auto &main_fn = goto_model.get_goto_function("main");
    const namespacet ns(goto_model.symbol_table);
    local_bitvector_analysist analysis(main_fn, ns);

    // Find the assignment to q
    auto it = main_fn.body.instructions.begin();
    while(it != main_fn.body.instructions.end() && !it->is_assign())
      ++it;
    REQUIRE(it != main_fn.body.instructions.end());

    THEN("The result includes uses_offset")
    {
      auto flags = analysis.get(it, plus_op0_ptr);
      REQUIRE(flags.is_uses_offset());
      REQUIRE_FALSE(flags.is_unknown());
    }
  }

  GIVEN("A 3-operand plus with pointer NOT at op0")
  {
    goto_modelt goto_model;

    symbolt local_p{"main::p", ptr_type, ID_C};
    local_p.is_lvalue = true;
    symbolt local_q{"main::q", ptr_type, ID_C};
    local_q.is_lvalue = true;

    // q = 1 + 2 + p  (pointer is op2, not op0)
    exprt::operandst ops;
    ops.push_back(from_integer(1, signed_int_type()));
    ops.push_back(from_integer(2, signed_int_type()));
    ops.push_back(local_p.symbol_expr());
    plus_exprt plus_ptr_last(std::move(ops), ptr_type);

    code_blockt code(
      {code_declt(local_p.symbol_expr()),
       code_declt(local_q.symbol_expr()),
       code_assignt(local_q.symbol_expr(), plus_ptr_last)});

    symbolt main_sym{"main", code_typet({}, empty_typet()), ID_C};
    main_sym.value = code;

    goto_model.symbol_table.add(local_p);
    goto_model.symbol_table.add(local_q);
    goto_model.symbol_table.add(main_sym);
    goto_convert(goto_model, null_message_handler);

    const auto &main_fn = goto_model.get_goto_function("main");
    const namespacet ns(goto_model.symbol_table);
    local_bitvector_analysist analysis(main_fn, ns);

    auto it = main_fn.body.instructions.begin();
    while(it != main_fn.body.instructions.end() && !it->is_assign())
      ++it;
    REQUIRE(it != main_fn.body.instructions.end());

    THEN("The result includes uses_offset even when pointer is not op0")
    {
      auto flags = analysis.get(it, plus_ptr_last);
      REQUIRE(flags.is_uses_offset());
      REQUIRE_FALSE(flags.is_unknown());
    }
  }

  GIVEN("A 3-operand plus with NO pointer operand")
  {
    goto_modelt goto_model;

    symbolt local_p{"main::p", ptr_type, ID_C};
    local_p.is_lvalue = true;

    // p = (int*)(1 + 2 + 3)  (no pointer operand in the plus)
    exprt::operandst ops;
    ops.push_back(from_integer(1, signed_int_type()));
    ops.push_back(from_integer(2, signed_int_type()));
    ops.push_back(from_integer(3, signed_int_type()));
    plus_exprt plus_no_ptr(std::move(ops), ptr_type);

    code_blockt code(
      {code_declt(local_p.symbol_expr()),
       code_assignt(local_p.symbol_expr(), plus_no_ptr)});

    symbolt main_sym{"main", code_typet({}, empty_typet()), ID_C};
    main_sym.value = code;

    goto_model.symbol_table.add(local_p);
    goto_model.symbol_table.add(main_sym);
    goto_convert(goto_model, null_message_handler);

    const auto &main_fn = goto_model.get_goto_function("main");
    const namespacet ns(goto_model.symbol_table);
    local_bitvector_analysist analysis(main_fn, ns);

    auto it = main_fn.body.instructions.begin();
    while(it != main_fn.body.instructions.end() && !it->is_assign())
      ++it;
    REQUIRE(it != main_fn.body.instructions.end());

    THEN("The result is unknown when no pointer operand exists")
    {
      auto flags = analysis.get(it, plus_no_ptr);
      REQUIRE(flags.is_unknown());
    }
  }
}
