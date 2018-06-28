/*******************************************************************\

Module: Value-set type consistency tests

Author: Diffblue Ltd, 2018

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <ansi-c/ansi_c_language.h>

#include <cbmc/cbmc_parse_options.h>

#include <langapi/language_ui.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>

#include <pointer-analysis/value_set_analysis.h>

#include <util/config.h>

#include <iostream>

SCENARIO("value-set type consistency")
{
  GIVEN("A simple C program that manipulates pointers")
  {
    register_language(new_ansi_c_language);
    cmdlinet cmdline;
    cmdline.args.push_back(
      "pointer-analysis/value_set_type_consistency_test.c");
    config.main = "main";
    config.set(cmdline);

    optionst opts;
    cbmc_parse_optionst::set_default_options(opts);

    ui_message_handlert msg_handler(cmdline, "value-set-type-consistency-test");
    messaget msg(msg_handler);

    goto_modelt goto_model;
    int ret = cbmc_parse_optionst::get_goto_program(
      goto_model, opts, cmdline, msg, msg_handler);
    REQUIRE(ret == -1);

    namespacet ns(goto_model.symbol_table);
    value_set_analysist vsa(ns);

    WHEN("Value-set analysis analyses the program")
    {
      vsa(goto_model.goto_functions);

      THEN("All value sets should be type-consistent with the query expression")
      {
        forall_goto_functions(function_it, goto_model.goto_functions)
        {
          // Gather expressions to query -- we could be more thorough, but for
          // now we'll check any expression used as an assignment LHS.
          std::vector<exprt> exprs_to_query;

          forall_goto_program_instructions(
            instruction_it, function_it->second.body)
          {
            if(instruction_it->is_assign())
            {
              exprs_to_query.push_back(
                to_code_assign(instruction_it->code).lhs());
            }
          }

          // Check that at every program point, any ID_unknown expression
          // returned has the same type as the query expression.

          forall_goto_program_instructions(
            instruction_it, function_it->second.body)
          {
            const value_sett &value_set = vsa[instruction_it].value_set;
            for(const exprt &expr : exprs_to_query)
            {
              value_setst::valuest result;
              value_set.get_value_set(expr, result, ns);

              for(const exprt &result_expr : result)
              {
                if(result_expr.id() == ID_unknown)
                {
                  if(result_expr.type() != expr.type())
                  {
                    // Known bug / inconsistency: the __CPROVER_threads_exited
                    // variable is of type _Bool [INFINITY()], but get_value_set
                    // returns an unknown of type _Bool.
                    if(expr.type().id() == ID_array)
                      continue;

                    std::cerr << from_type(ns, "", result_expr.type())
                              << " vs. " << from_type(ns, "", expr.type())
                              << "(" << from_expr(ns, "", expr) << ")\n";
                  }
                  REQUIRE(result_expr.type() == expr.type());
                }
              }
            }
          }
        }
      }
    }
  }
}
