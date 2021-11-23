// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt2_incremental_decision_procedure.h>
#include <solvers/smt2_incremental/smt_commands.h>
#include <solvers/smt2_incremental/smt_core_theory.h>
#include <solvers/smt2_incremental/smt_responses.h>
#include <solvers/smt2_incremental/smt_solver_process.h>
#include <solvers/smt2_incremental/smt_sorts.h>
#include <solvers/smt2_incremental/smt_terms.h>
#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/make_unique.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

// Used by catch framework for printing in the case of test failures. This
// means that we get error messages showing the smt formula expressed as SMT2
// strings instead of `{?}` being printed. It works because catch uses the
// appropriate overload of `operator<<` where it exists.
#include <solvers/smt2_incremental/smt_to_smt2_string.h>

#include <deque>

class smt_mock_solver_processt : public smt_base_solver_processt
{
public:
  const std::string &description() override
  {
    UNREACHABLE;
  }

  void send(const smt_commandt &smt_command) override
  {
    sent_commands.push_back(smt_command);
  }

  std::deque<smt_responset> responses;

  smt_responset receive_response() override
  {
    INVARIANT(
      !responses.empty(), "There must be responses remaining for test.");
    smt_responset response = responses.front();
    responses.pop_front();
    return response;
  }

  std::vector<smt_commandt> sent_commands;

  ~smt_mock_solver_processt() override = default;
};

static symbolt make_test_symbol(irep_idt id, typet type)
{
  symbolt new_symbol;
  new_symbol.name = std::move(id);
  new_symbol.type = std::move(type);
  return new_symbol;
}

static symbolt make_test_symbol(irep_idt id, exprt value)
{
  symbolt new_symbol;
  new_symbol.name = std::move(id);
  new_symbol.type = value.type();
  new_symbol.value = std::move(value);
  return new_symbol;
}

TEST_CASE(
  "smt2_incremental_decision_proceduret commands sent",
  "[core][smt2_incremental]")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  auto mock_process = util_make_unique<smt_mock_solver_processt>();
  auto &sent_commands = mock_process->sent_commands;
  null_message_handlert message_handler;
  SECTION("Construction / solver initialisation.")
  {
    smt2_incremental_decision_proceduret procedure{
      ns, std::move(mock_process), message_handler};
    REQUIRE(
      sent_commands ==
      std::vector<smt_commandt>{
        smt_set_option_commandt{smt_option_produce_modelst{true}},
        smt_set_logic_commandt{
          smt_logic_quantifier_free_uninterpreted_functions_bit_vectorst{}}});
    sent_commands.clear();
    SECTION("Set symbol to true.")
    {
      const symbolt foo = make_test_symbol("foo", bool_typet{});
      const smt_identifier_termt foo_term{"foo", smt_bool_sortt{}};
      procedure.set_to(foo.symbol_expr(), true);
      REQUIRE(
        sent_commands ==
        std::vector<smt_commandt>{smt_declare_function_commandt{foo_term, {}},
                                  smt_assert_commandt{foo_term}});
    }
    SECTION("Set symbol to false.")
    {
      const symbolt foo = make_test_symbol("foo", bool_typet{});
      const smt_identifier_termt foo_term{"foo", smt_bool_sortt{}};
      procedure.set_to(foo.symbol_expr(), false);
      REQUIRE(
        sent_commands ==
        std::vector<smt_commandt>{
          smt_declare_function_commandt{foo_term, {}},
          smt_assert_commandt{smt_core_theoryt::make_not(foo_term)}});
    }
    SECTION("Set using chaining of symbol expressions.")
    {
      const symbolt forty_two =
        make_test_symbol("forty_two", from_integer({42}, signedbv_typet{16}));
      symbol_table.insert(forty_two);
      const smt_identifier_termt forty_two_term{"forty_two",
                                                smt_bit_vector_sortt{16}};
      const symbolt nondet_int_a =
        make_test_symbol("nondet_int_a", signedbv_typet{16});
      symbol_table.insert(nondet_int_a);
      const smt_identifier_termt nondet_int_a_term{"nondet_int_a",
                                                   smt_bit_vector_sortt{16}};
      const symbolt nondet_int_b =
        make_test_symbol("nondet_int_b", signedbv_typet{16});
      symbol_table.insert(nondet_int_b);
      const smt_identifier_termt nondet_int_b_term{"nondet_int_b",
                                                   smt_bit_vector_sortt{16}};
      const symbolt first_comparison = make_test_symbol(
        "first_comparison",
        equal_exprt{nondet_int_a.symbol_expr(), forty_two.symbol_expr()});
      symbol_table.insert(first_comparison);
      const symbolt second_comparison = make_test_symbol(
        "second_comparison",
        not_exprt{
          equal_exprt{nondet_int_b.symbol_expr(), forty_two.symbol_expr()}});
      symbol_table.insert(second_comparison);
      const symbolt third_comparison = make_test_symbol(
        "third_comparison",
        equal_exprt{nondet_int_a.symbol_expr(), nondet_int_b.symbol_expr()});
      symbol_table.insert(third_comparison);
      const symbolt comparison_conjunction = make_test_symbol(
        "comparison_conjunction",
        and_exprt{{first_comparison.symbol_expr(),
                   second_comparison.symbol_expr(),
                   third_comparison.symbol_expr()}});
      symbol_table.insert(comparison_conjunction);
      smt_identifier_termt comparison_conjunction_term{"comparison_conjunction",
                                                       smt_bool_sortt{}};
      procedure.set_to(comparison_conjunction.symbol_expr(), true);
      REQUIRE(
        sent_commands ==
        std::vector<smt_commandt>{
          smt_declare_function_commandt{nondet_int_a_term, {}},
          smt_define_function_commandt{
            "forty_two", {}, smt_bit_vector_constant_termt{42, 16}},
          smt_define_function_commandt{
            "first_comparison",
            {},
            smt_core_theoryt::equal(nondet_int_a_term, forty_two_term)},
          smt_declare_function_commandt{nondet_int_b_term, {}},
          smt_define_function_commandt{
            "second_comparison",
            {},
            smt_core_theoryt::make_not(
              smt_core_theoryt::equal(nondet_int_b_term, forty_two_term))},
          smt_define_function_commandt{
            "third_comparison",
            {},
            smt_core_theoryt::equal(nondet_int_a_term, nondet_int_b_term)},
          smt_define_function_commandt{
            "comparison_conjunction",
            {},
            smt_core_theoryt::make_and(
              smt_core_theoryt::make_and(
                smt_identifier_termt{"first_comparison", smt_bool_sortt{}},
                smt_identifier_termt{"second_comparison", smt_bool_sortt{}}),
              smt_identifier_termt{"third_comparison", smt_bool_sortt{}})},
          smt_assert_commandt{comparison_conjunction_term}});
    }
    SECTION("Handle of value-less symbol.")
    {
      const symbolt foo = make_test_symbol("foo", bool_typet{});
      const smt_identifier_termt foo_term{"foo", smt_bool_sortt{}};
      procedure.handle(foo.symbol_expr());
      REQUIRE(
        sent_commands == std::vector<smt_commandt>{
                           smt_declare_function_commandt{foo_term, {}},
                           smt_define_function_commandt{"B0", {}, foo_term}});
      sent_commands.clear();
      SECTION("Handle of previously handled expression.")
      {
        procedure.handle(foo.symbol_expr());
        REQUIRE(sent_commands.empty());
      }
      SECTION("Handle of new expression containing previously defined symbol.")
      {
        procedure.handle(equal_exprt{foo.symbol_expr(), foo.symbol_expr()});
        REQUIRE(
          sent_commands ==
          std::vector<smt_commandt>{smt_define_function_commandt{
            "B1", {}, smt_core_theoryt::equal(foo_term, foo_term)}});
      }
    }
    SECTION("Handle of symbol with value.")
    {
      const symbolt bar =
        make_test_symbol("bar", from_integer({42}, signedbv_typet{8}));
      symbol_table.insert(bar);
      procedure.handle(bar.symbol_expr());
      REQUIRE(
        sent_commands ==
        std::vector<smt_commandt>{
          smt_define_function_commandt{
            "bar", {}, smt_bit_vector_constant_termt{42, 8}},
          smt_define_function_commandt{
            "B0", {}, smt_identifier_termt{"bar", smt_bit_vector_sortt{8}}}});
    }
  }
}

TEST_CASE(
  "smt2_incremental_decision_proceduret number of solver calls.",
  "[core][smt2_incremental]")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  auto mock_process = util_make_unique<smt_mock_solver_processt>();
  auto &responses = mock_process->responses;
  null_message_handlert message_handler;
  smt2_incremental_decision_proceduret procedure{
    ns, std::move(mock_process), message_handler};
  REQUIRE(procedure.get_number_of_solver_calls() == 0);
  responses.push_back(smt_check_sat_responset{smt_unsat_responset{}});
  procedure();
  REQUIRE(procedure.get_number_of_solver_calls() == 1);
  responses.push_back(smt_check_sat_responset{smt_unsat_responset{}});
  procedure();
  REQUIRE(procedure.get_number_of_solver_calls() == 2);
}
