/*******************************************************************\

Module: Unit test for constant propagation

Author: Diffblue Ltd

\*******************************************************************/

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <analyses/constant_propagator.h>

#include <goto-programs/goto_convert_functions.h>

#include <util/arith_tools.h>
#include <util/message.h>

static bool starts_with_x(const exprt &e, const namespacet &)
{
  if(e.id() != ID_symbol)
    return false;
  return has_prefix(id2string(to_symbol_expr(e).get_identifier()), "x");
}

SCENARIO("constant_propagator", "[core][analyses][constant_propagator]")
{
  GIVEN("A simple GOTO program")
  {
    goto_modelt goto_model;
    namespacet ns(goto_model.symbol_table);

    // Create the program:
    // int x = 1;
    // int y = 2;

    symbolt local_x;
    symbolt local_y;
    local_x.name = "x";
    local_x.type = integer_typet();
    local_x.mode = ID_C;
    local_y.name = "y";
    local_y.type = integer_typet();
    local_y.mode = ID_C;

    code_blockt code(
      {code_declt(local_x.symbol_expr()),
       code_declt(local_y.symbol_expr()),
       code_assignt(
         local_x.symbol_expr(), constant_exprt("1", integer_typet())),
       code_assignt(
         local_y.symbol_expr(), constant_exprt("2", integer_typet()))});

    symbolt main_function_symbol;
    main_function_symbol.name = "main";
    main_function_symbol.type = code_typet({}, void_typet());
    main_function_symbol.value = code;
    main_function_symbol.mode = ID_C;

    goto_model.symbol_table.add(local_x);
    goto_model.symbol_table.add(local_y);
    goto_model.symbol_table.add(main_function_symbol);

    goto_convert(goto_model, null_message_handler);

    const goto_functiont &main_function = goto_model.get_goto_function("main");

    // Find the instruction after "y = 2;"
    goto_programt::const_targett test_instruction =
      main_function.body.instructions.begin();
    while(
      test_instruction != main_function.body.instructions.end() &&
      (!test_instruction->is_assign() ||
       to_code_assign(test_instruction->code).lhs() != local_y.symbol_expr()))
    {
      ++test_instruction;
    }

    REQUIRE(test_instruction != main_function.body.instructions.end());
    ++test_instruction;

    WHEN("We apply conventional constant propagation")
    {
      constant_propagator_ait constant_propagator(main_function);
      constant_propagator(main_function_symbol.name, main_function, ns);

      THEN("The propagator should discover values for both 'x' and 'y'")
      {
        const auto &final_domain = constant_propagator[test_instruction];

        REQUIRE(final_domain.values.is_constant(local_x.symbol_expr()));
        REQUIRE(final_domain.values.is_constant(local_y.symbol_expr()));
      }
    }

    WHEN("We apply constant propagation for symbols beginning with 'x'")
    {
      constant_propagator_ait constant_propagator(main_function, starts_with_x);
      constant_propagator(main_function_symbol.name, main_function, ns);

      THEN("The propagator should discover a value for 'x' but not 'y'")
      {
        const auto &final_domain = constant_propagator[test_instruction];

        REQUIRE(final_domain.values.is_constant(local_x.symbol_expr()));
        REQUIRE(!final_domain.values.is_constant(local_y.symbol_expr()));
      }
    }
  }

  GIVEN("A GOTO program featuring a condition over a boolean")
  {
    // Create a program like:
    // bool b;
    // if(!b)
    //   b = true;
    // Repeat this using bool_typet and c_bool_typet for "bool".

    goto_modelt goto_model;
    namespacet ns(goto_model.symbol_table);

    symbolt bool_local;
    symbolt c_bool_local;
    bool_local.name = "bool_local";
    bool_local.type = bool_typet();
    bool_local.mode = ID_C;
    c_bool_local.name = "c_bool_local";
    c_bool_local.type = c_bool_typet(8);
    c_bool_local.mode = ID_C;

    code_blockt code({code_declt(bool_local.symbol_expr()),
                      code_declt(c_bool_local.symbol_expr())});

    code_ifthenelset bool_cond_block(
      not_exprt(bool_local.symbol_expr()),
      code_assignt(bool_local.symbol_expr(), true_exprt()));

    const exprt c_bool_true = from_integer(1, c_bool_typet(8));
    code_ifthenelset c_bool_cond_block(
      notequal_exprt(c_bool_local.symbol_expr(), c_bool_true),
      code_assignt(c_bool_local.symbol_expr(), c_bool_true));

    code.add(std::move(bool_cond_block));
    code.add(std::move(c_bool_cond_block));

    symbolt main_function_symbol;
    main_function_symbol.name = "main";
    main_function_symbol.type = code_typet({}, void_typet());
    main_function_symbol.value = code;
    main_function_symbol.mode = ID_C;

    goto_model.symbol_table.add(bool_local);
    goto_model.symbol_table.add(c_bool_local);
    goto_model.symbol_table.add(main_function_symbol);

    goto_convert(goto_model, null_message_handler);

    const goto_functiont &main_function = goto_model.get_goto_function("main");

    // Find the first DEAD instruction -- we will test our results there, after
    // the function body but before the exit sequence.
    goto_programt::const_targett test_instruction =
      main_function.body.instructions.begin();
    while(test_instruction != main_function.body.instructions.end() &&
          !test_instruction->is_dead())
    {
      ++test_instruction;
    }

    REQUIRE(test_instruction != main_function.body.instructions.end());

    WHEN("Constant propagation is performed")
    {
      constant_propagator_ait constant_propagator(main_function);
      constant_propagator(main_function_symbol.name, main_function, ns);

      THEN(
        "The propagator should conclude that both booleans are true at the "
        "end of the function")
      {
        const auto &final_domain = constant_propagator[test_instruction];

        REQUIRE(final_domain.values.is_constant(bool_local.symbol_expr()));
        REQUIRE(final_domain.values.is_constant(c_bool_local.symbol_expr()));
      }
    }
  }

  GIVEN("A GOTO program testing ways of expressing boolean tests")
  {
    // Create a program like:
    // bool b0, b1, b2, ...;
    // int marker;
    // if(b0)
    //   if(!b1)
    //     if(b2 && b3)
    //       if(b4 == TRUE)
    //         if(b5 == FALSE)
    //           if(b6 != TRUE)
    //             if(b7 != FALSE)
    //               if((int)b8 == 0)
    //                 if((char)b9 == '\1')
    //                   marker = 1234;

    // At the marker assignment we should have:
    // b0, !b1, b2, b3, b4, !b5, !b6, b7, !b8, b9 all known.
    // Then repeat the whole thing with C_bools instead of plain bools,
    // except for the first two (b0 and !b1), which can't be done with C_bool.

    std::vector<symbolt> bool_locals;
    std::vector<symbolt> c_bool_locals;
    const size_t n_bool_locals = 10;
    const size_t n_c_bool_locals = 8;

    for(size_t i = 0; i < n_bool_locals; ++i)
    {
      symbolt bool_local;
      bool_local.name = "b" + std::to_string(i);
      bool_local.type = bool_typet();
      bool_local.mode = ID_C;
      bool_locals.push_back(bool_local);
    }

    for(size_t i = 0; i < n_c_bool_locals; ++i)
    {
      symbolt c_bool_local;
      c_bool_local.name = "cb" + std::to_string(i);
      c_bool_local.type = c_bool_typet(8);
      c_bool_local.mode = ID_C;
      c_bool_locals.push_back(c_bool_local);
    }

    const exprt bool_tests[] = {
      bool_locals.at(0).symbol_expr(),
      not_exprt(bool_locals.at(1).symbol_expr()),
      and_exprt(
        bool_locals.at(2).symbol_expr(), bool_locals.at(3).symbol_expr()),
      equal_exprt(bool_locals.at(4).symbol_expr(), true_exprt()),
      equal_exprt(bool_locals.at(5).symbol_expr(), false_exprt()),
      notequal_exprt(bool_locals.at(6).symbol_expr(), true_exprt()),
      notequal_exprt(bool_locals.at(7).symbol_expr(), false_exprt()),
      equal_exprt(
        typecast_exprt(bool_locals.at(8).symbol_expr(), signedbv_typet(32)),
        from_integer(0, signedbv_typet(32))),
      equal_exprt(
        typecast_exprt(bool_locals.at(9).symbol_expr(), unsignedbv_typet(8)),
        from_integer(1, unsignedbv_typet(8)))};

    const exprt c_bool_false = from_integer(0, c_bool_typet(8));
    const exprt c_bool_true = from_integer(1, c_bool_typet(8));

    const exprt c_bool_tests[] = {
      and_exprt(
        equal_exprt(c_bool_locals.at(0).symbol_expr(), c_bool_true),
        equal_exprt(c_bool_locals.at(1).symbol_expr(), c_bool_true)),
      equal_exprt(c_bool_locals.at(2).symbol_expr(), c_bool_true),
      equal_exprt(c_bool_locals.at(3).symbol_expr(), c_bool_false),
      notequal_exprt(c_bool_locals.at(4).symbol_expr(), c_bool_true),
      notequal_exprt(c_bool_locals.at(5).symbol_expr(), c_bool_false),
      equal_exprt(
        typecast_exprt(c_bool_locals.at(6).symbol_expr(), signedbv_typet(32)),
        from_integer(0, signedbv_typet(32))),
      equal_exprt(
        typecast_exprt(c_bool_locals.at(7).symbol_expr(), unsignedbv_typet(8)),
        from_integer(1, unsignedbv_typet(8)))};

    const bool bool_expectations[n_bool_locals] = {
      true, false, true, true, true, false, false, true, false, true};

    const bool c_bool_expectations[n_c_bool_locals] = {
      true, true, true, false, false, true, false, true};

    symbolt marker_symbol;
    marker_symbol.type = signedbv_typet(32);
    marker_symbol.name = "marker";
    marker_symbol.mode = ID_C;

    codet program = code_assignt(
      marker_symbol.symbol_expr(), from_integer(1234, marker_symbol.type));

    // Build a big nested-if around the marker assignment:
    for(const exprt &test : bool_tests)
      program = code_ifthenelset(test, program);
    for(const exprt &test : c_bool_tests)
      program = code_ifthenelset(test, program);

    goto_modelt goto_model;
    namespacet ns(goto_model.symbol_table);

    for(const symbolt &symbol : bool_locals)
      goto_model.symbol_table.add(symbol);
    for(const symbolt &symbol : c_bool_locals)
      goto_model.symbol_table.add(symbol);

    symbolt main_function_symbol;
    main_function_symbol.name = "main";
    main_function_symbol.type = code_typet({}, void_typet());
    main_function_symbol.value = program;
    main_function_symbol.mode = ID_C;

    goto_model.symbol_table.add(marker_symbol);
    goto_model.symbol_table.add(main_function_symbol);

    goto_convert(goto_model, null_message_handler);

    const goto_functiont &main_function = goto_model.get_goto_function("main");

    // Find the marker assignment: we will check that the correct constants
    // have been propagated once we reach it.
    goto_programt::const_targett test_instruction =
      main_function.body.instructions.begin();
    while(test_instruction != main_function.body.instructions.end() &&
          !(test_instruction->is_assign() &&
            to_code_assign(test_instruction->code).lhs() ==
              marker_symbol.symbol_expr()))
    {
      ++test_instruction;
    }

    REQUIRE(test_instruction != main_function.body.instructions.end());

    WHEN("Constant propagation is performed")
    {
      constant_propagator_ait constant_propagator(main_function);
      constant_propagator(main_function_symbol.name, main_function, ns);

      THEN("The propagator should match our expectations")
      {
        const auto &final_domain = constant_propagator[test_instruction];

        for(size_t i = 0; i < n_bool_locals; ++i)
        {
          exprt bool_local = bool_locals[i].symbol_expr();

          REQUIRE(final_domain.values.is_constant(bool_local));

          final_domain.values.replace_const.replace(bool_local);

          exprt expected;
          if(bool_expectations[i])
            expected = true_exprt();
          else
            expected = false_exprt();

          REQUIRE(bool_local == expected);
        }

        for(size_t i = 0; i < n_c_bool_locals; ++i)
        {
          exprt c_bool_local = c_bool_locals[i].symbol_expr();

          REQUIRE(final_domain.values.is_constant(c_bool_local));

          final_domain.values.replace_const.replace(c_bool_local);

          const exprt expected =
            c_bool_expectations[i] ? c_bool_true : c_bool_false;

          REQUIRE(c_bool_local == expected);
        }
      }
    }
  }
}
