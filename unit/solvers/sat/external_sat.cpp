/// \file
/// Unit tests for calling external SAT solver
/// \author Francis Botero <fbbotero@amazon.com>

#include <solvers/sat/external_sat.h>
#include <testing-utils/use_catch.h>
#include <util/cout_message.h>

class external_sat_test : public external_satt
{
public:
  external_sat_test(message_handlert &message_handler, std::string cmd)
    : external_satt(message_handler, cmd)
  {
  }

  resultt parse_result(std::string result)
  {
    return external_satt::parse_result(result);
  }
};

SCENARIO("external_sat", "[core][solvers][sat][external_sat]")
{
  console_message_handlert message_handler;
  message_handler.set_verbosity(0);

  GIVEN("External SAT solver is used")
  {
    external_sat_test satcheck(message_handler, "cmd");
    AND_GIVEN("the output is malformed")
    {
      auto result = GENERATE(
        as<std::string>(),
        "c comment line\nc another comment\n",
        "c no results but assignments present\nv 1 2 3 4\n",
        "c too many assignments\ns SATISFIABLE\nv 1 2 3 4",
        "v_starts the line but is malformed",
        "s_starts the line but is malformed",
        "s SOMETHING STRANGE",
        "another result");
      WHEN("the solver output contains:\n" << result)
      {
        THEN("the result is set to error")
        {
          REQUIRE(satcheck.parse_result(result) == propt::resultt::P_ERROR);
        }
      }
    }

    AND_GIVEN("the output is malformed")
    {
      auto result = "c too few assignments\ns SATISFIABLE\nv 1 2 3 4";
      WHEN("the solver output contains:\n" << result)
      {
        THEN("the result is set to error")
        {
          satcheck.set_no_variables(100);
          REQUIRE(satcheck.parse_result(result) == propt::resultt::P_ERROR);
        }
      }
    }

    AND_GIVEN("SAT instance is unsatisfiable")
    {
      std::string unsat_result = GENERATE(
        as<std::string>(),
        "s UNSATISFIABLE",
        "s UNSATISFIABLE\ns SATISFIABLE",
        "s SATISFIABLE\ns UNSATISFIABLE");
      WHEN("the solver output contains:\n" << unsat_result)
      {
        THEN("the result is set to unsatisfiable")
        {
          REQUIRE(
            satcheck.parse_result(unsat_result) ==
            propt::resultt::P_UNSATISFIABLE);
        }
      }
    }

    AND_GIVEN("SAT instance is satisfiable")
    {
      auto gen = GENERATE(
        std::make_tuple(
          "s SATISFIABLE\nv 1 2 3 4",
          std::vector<bool>{true, true, true, true}),
        std::make_tuple(
          "s SATISFIABLE\nv 1 2 -3 -4",
          std::vector<bool>{true, true, false, false}),
        std::make_tuple(
          "s SATISFIABLE\nv 1 -2 3 -4",
          std::vector<bool>{true, false, true, false}),
        std::make_tuple(
          "s SATISFIABLE\nv -1 2 -3 4",
          std::vector<bool>{false, true, false, true}),
        std::make_tuple(
          "s SATISFIABLE\nv -1 -2 -3 -4",
          std::vector<bool>{false, false, false, false}),
        std::make_tuple(
          "v 4\ns SATISFIABLE\nv -1\nv 2\nv -3\n",
          std::vector<bool>{false, true, false, true}));
      WHEN("the solver output contains:\n" << std::get<0>(gen))
      {
        THEN("the result is set to satisfiable")
        {
          auto arr = std::get<1>(gen);
          // add false to the start for element at 0
          arr.insert(arr.begin(), false);
          satcheck.set_no_variables(arr.size());
          auto results_vector =
            std::vector<bool>(satcheck.no_variables(), false);
          REQUIRE(
            satcheck.parse_result(std::get<0>(gen)) ==
            propt::resultt::P_SATISFIABLE);
          AND_THEN("has correct assignments")
          {
            auto assignments = satcheck.get_assignment();
            for(size_t i = 1; i < satcheck.no_variables(); i++)
            {
              results_vector[i] = assignments[i].is_true();
            }
            REQUIRE_THAT(results_vector, Catch::Equals(arr));
          }
        }
      }
    }
  }
}
