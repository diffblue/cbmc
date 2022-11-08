// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/config.h>
#include <util/exception_utils.h>
#include <util/make_unique.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include <solvers/smt2_incremental/ast/smt_commands.h>
#include <solvers/smt2_incremental/ast/smt_responses.h>
#include <solvers/smt2_incremental/ast/smt_sorts.h>
#include <solvers/smt2_incremental/ast/smt_terms.h>
#include <solvers/smt2_incremental/smt2_incremental_decision_procedure.h>
#include <solvers/smt2_incremental/smt_solver_process.h>
#include <solvers/smt2_incremental/theories/smt_array_theory.h>
#include <solvers/smt2_incremental/theories/smt_core_theory.h>
#include <testing-utils/invariant.h>
#include <testing-utils/use_catch.h>

// Used by catch framework for printing in the case of test failures. This
// means that we get error messages showing the smt formula expressed as SMT2
// strings instead of `{?}` being printed. It works because catch uses the
// appropriate overload of `operator<<` where it exists.
#include <goto-symex/path_storage.h>
#include <solvers/smt2_incremental/smt_to_smt2_string.h>

#include <deque>

class analysis_execption_with_messaget
  : public Catch::MatcherBase<analysis_exceptiont>
{
public:
  explicit analysis_execption_with_messaget(std::string message);
  bool match(const analysis_exceptiont &exception) const override;
  std::string describe() const override;

private:
  std::string expected;
};

analysis_execption_with_messaget::analysis_execption_with_messaget(
  std::string message)
  : expected{std::move(message)}
{
}

bool analysis_execption_with_messaget::match(
  const analysis_exceptiont &exception) const
{
  return expected == exception.what();
}

std::string analysis_execption_with_messaget::describe() const
{
  return std::string{"analysis_exceptiont with `.what' containing - \""} +
         expected + "\"";
}

class smt_mock_solver_processt : public smt_base_solver_processt
{
  std::function<void(const smt_commandt &)> _send;
  std::function<smt_responset()> _receive;

public:
  smt_mock_solver_processt(
    std::function<void(const smt_commandt &)> send,
    std::function<smt_responset()> receive)
    : _send{std::move(send)}, _receive{std::move(receive)}
  {
  }

  const std::string &description() override
  {
    UNREACHABLE;
  }

  void send(const smt_commandt &smt_command) override
  {
    _send(smt_command);
  }

  smt_responset receive_response(
    const std::unordered_map<irep_idt, smt_identifier_termt> &identifier_table)
    override
  {
    return _receive();
  }

  ~smt_mock_solver_processt() override = default;
};

/// \brief Data structures and their initialisation shared between tests.
/// \details
///   Instantiates a `smt2_incremental_decision_proceduret` using a mock of the
///   solver process to direct communication with the solver to collections of
///   `sent_commands` and `mock_responses`. The `mock_respones` must be
///   populated by the test, before the decision procedure expects them. The
///   `sent_commands` should be checked by the test after the decision procedure
///   has sent them.
struct decision_procedure_test_environmentt final
{
  void send(const smt_commandt &smt_command);
  smt_responset receive_response();

  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  std::deque<smt_responset> mock_responses;
  std::vector<smt_commandt> sent_commands;
  null_message_handlert message_handler;
  smt_object_sizet object_size_function;
  smt2_incremental_decision_proceduret procedure{
    ns,
    util_make_unique<smt_mock_solver_processt>(
      [&](const smt_commandt &smt_command) { this->send(smt_command); },
      [&]() { return this->receive_response(); }),
    message_handler};
  static decision_procedure_test_environmentt make()
  {
    // These config lines are necessary before construction because pointer
    // widths and object bit width encodings depend on the global configuration.
    config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
    config.ansi_c.set_arch_spec_i386();
    return {};
  }

private:
  // This is private to ensure the above make() function is used to make
  // correctly configured instances.
  decision_procedure_test_environmentt() = default;
};

void decision_procedure_test_environmentt::send(const smt_commandt &smt_command)
{
  sent_commands.push_back(smt_command);
}

smt_responset decision_procedure_test_environmentt::receive_response()
{
  INVARIANT(
    !mock_responses.empty(), "There must be responses remaining for test.");
  smt_responset response = mock_responses.front();
  mock_responses.pop_front();
  return response;
}

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
  auto test = decision_procedure_test_environmentt::make();
  SECTION("Construction / solver initialisation.")
  {
    REQUIRE(
      test.sent_commands ==
      std::vector<smt_commandt>{
        smt_set_option_commandt{smt_option_produce_modelst{true}},
        smt_set_logic_commandt{smt_logic_allt{}},
        test.object_size_function.declaration});
    test.sent_commands.clear();
    SECTION("Set symbol to true.")
    {
      const symbolt foo = make_test_symbol("foo", bool_typet{});
      const smt_identifier_termt foo_term{"foo", smt_bool_sortt{}};
      test.procedure.set_to(foo.symbol_expr(), true);
      REQUIRE(
        test.sent_commands ==
        std::vector<smt_commandt>{smt_declare_function_commandt{foo_term, {}},
                                  smt_assert_commandt{foo_term}});
    }
    SECTION("Set symbol to false.")
    {
      const symbolt foo = make_test_symbol("foo", bool_typet{});
      const smt_identifier_termt foo_term{"foo", smt_bool_sortt{}};
      test.procedure.set_to(foo.symbol_expr(), false);
      REQUIRE(
        test.sent_commands ==
        std::vector<smt_commandt>{
          smt_declare_function_commandt{foo_term, {}},
          smt_assert_commandt{smt_core_theoryt::make_not(foo_term)}});
    }
    SECTION("Set using chaining of symbol expressions.")
    {
      const symbolt forty_two =
        make_test_symbol("forty_two", from_integer({42}, signedbv_typet{16}));
      test.symbol_table.insert(forty_two);
      const smt_identifier_termt forty_two_term{"forty_two",
                                                smt_bit_vector_sortt{16}};
      const symbolt nondet_int_a =
        make_test_symbol("nondet_int_a", signedbv_typet{16});
      test.symbol_table.insert(nondet_int_a);
      const smt_identifier_termt nondet_int_a_term{"nondet_int_a",
                                                   smt_bit_vector_sortt{16}};
      const symbolt nondet_int_b =
        make_test_symbol("nondet_int_b", signedbv_typet{16});
      test.symbol_table.insert(nondet_int_b);
      const smt_identifier_termt nondet_int_b_term{"nondet_int_b",
                                                   smt_bit_vector_sortt{16}};
      const symbolt first_comparison = make_test_symbol(
        "first_comparison",
        equal_exprt{nondet_int_a.symbol_expr(), forty_two.symbol_expr()});
      test.symbol_table.insert(first_comparison);
      const symbolt second_comparison = make_test_symbol(
        "second_comparison",
        not_exprt{
          equal_exprt{nondet_int_b.symbol_expr(), forty_two.symbol_expr()}});
      test.symbol_table.insert(second_comparison);
      const symbolt third_comparison = make_test_symbol(
        "third_comparison",
        equal_exprt{nondet_int_a.symbol_expr(), nondet_int_b.symbol_expr()});
      test.symbol_table.insert(third_comparison);
      const symbolt comparison_conjunction = make_test_symbol(
        "comparison_conjunction",
        and_exprt{{first_comparison.symbol_expr(),
                   second_comparison.symbol_expr(),
                   third_comparison.symbol_expr()}});
      test.symbol_table.insert(comparison_conjunction);
      smt_identifier_termt comparison_conjunction_term{"comparison_conjunction",
                                                       smt_bool_sortt{}};
      test.procedure.set_to(comparison_conjunction.symbol_expr(), true);
      REQUIRE(
        test.sent_commands ==
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
      test.procedure.handle(foo.symbol_expr());
      REQUIRE(
        test.sent_commands ==
        std::vector<smt_commandt>{
          smt_declare_function_commandt{foo_term, {}},
          smt_define_function_commandt{"B0", {}, foo_term}});
      test.sent_commands.clear();
      SECTION("Handle of previously handled expression.")
      {
        test.procedure.handle(foo.symbol_expr());
        REQUIRE(test.sent_commands.empty());
      }
      SECTION("Handle of new expression containing previously defined symbol.")
      {
        test.procedure.handle(
          equal_exprt{foo.symbol_expr(), foo.symbol_expr()});
        REQUIRE(
          test.sent_commands ==
          std::vector<smt_commandt>{smt_define_function_commandt{
            "B1", {}, smt_core_theoryt::equal(foo_term, foo_term)}});
      }
    }
    SECTION("Handle of symbol with value.")
    {
      const symbolt bar =
        make_test_symbol("bar", from_integer({42}, signedbv_typet{8}));
      test.symbol_table.insert(bar);
      test.procedure.handle(bar.symbol_expr());
      REQUIRE(
        test.sent_commands ==
        std::vector<smt_commandt>{
          smt_define_function_commandt{
            "bar", {}, smt_bit_vector_constant_termt{42, 8}},
          smt_define_function_commandt{
            "B0", {}, smt_identifier_termt{"bar", smt_bit_vector_sortt{8}}}});
    }
  }
  SECTION("Handle single nondet_symbol")
  {
    // Using the standard way to create nondet_symbol_exprt.
    ::symex_nondet_generatort generator;
    const nondet_symbol_exprt nondet_symbol0 =
      generator(bool_typet{}, source_locationt{});
    const smt_identifier_termt nondet_symbol_term0{
      nondet_symbol0.get_identifier(), smt_bool_sortt{}};
    test.sent_commands.clear();
    test.procedure.handle(nondet_symbol0);
    REQUIRE(
      test.sent_commands ==
      std::vector<smt_commandt>{
        smt_declare_function_commandt{nondet_symbol_term0, {}},
        smt_define_function_commandt{"B0", {}, nondet_symbol_term0}});
  }
  SECTION("Handle multiple nested nondet_symbol")
  {
    ::symex_nondet_generatort generator;
    const nondet_symbol_exprt nondet_symbol1 =
      generator(bv_typet(42), source_locationt{});
    const smt_identifier_termt nondet_symbol_term1{
      nondet_symbol1.get_identifier(), smt_bit_vector_sortt{42}};
    const nondet_symbol_exprt nondet_symbol2 =
      generator(bv_typet(42), source_locationt{});
    const smt_identifier_termt nondet_symbol_term2{
      nondet_symbol2.get_identifier(), smt_bit_vector_sortt{42}};
    // Check that the 2 calls to the generator returns unique nondet_symbols.
    REQUIRE(
      nondet_symbol1.get_identifier() != nondet_symbol_term2.identifier());
    test.sent_commands.clear();
    test.procedure.handle(equal_exprt{nondet_symbol1, nondet_symbol2});
    // Checking that we defined 2 symbols and that they are correctly compared.
    REQUIRE(
      test.sent_commands ==
      std::vector<smt_commandt>{
        smt_declare_function_commandt{nondet_symbol_term1, {}},
        smt_declare_function_commandt{nondet_symbol_term2, {}},
        smt_define_function_commandt{
          "B0",
          {},
          smt_core_theoryt::equal(nondet_symbol_term1, nondet_symbol_term2)}});
  }
}

TEST_CASE(
  "smt2_incremental_decision_proceduret number of solver calls.",
  "[core][smt2_incremental]")
{
  auto test = decision_procedure_test_environmentt::make();
  REQUIRE(test.procedure.get_number_of_solver_calls() == 0);
  test.mock_responses.push_back(smt_check_sat_responset{smt_unsat_responset{}});
  test.procedure();
  REQUIRE(test.procedure.get_number_of_solver_calls() == 1);
  test.mock_responses.push_back(smt_check_sat_responset{smt_unsat_responset{}});
  test.procedure();
  REQUIRE(test.procedure.get_number_of_solver_calls() == 2);
}

TEST_CASE(
  "smt2_incremental_decision_proceduret mapping solver check-sat responses to "
  "internal decision_proceduret::resultt",
  "[core][smt2_incremental]")
{
  auto test = decision_procedure_test_environmentt::make();
  SECTION("sat")
  {
    test.mock_responses = {smt_check_sat_responset{smt_sat_responset{}}};
    CHECK(test.procedure() == decision_proceduret::resultt::D_SATISFIABLE);
  }
  SECTION("unsat")
  {
    test.mock_responses = {smt_check_sat_responset{smt_unsat_responset{}}};
    CHECK(test.procedure() == decision_proceduret::resultt::D_UNSATISFIABLE);
  }
  SECTION("unknown")
  {
    test.mock_responses = {smt_check_sat_responset{smt_unknown_responset{}}};
    CHECK(test.procedure() == decision_proceduret::resultt::D_ERROR);
  }
}

TEST_CASE(
  "smt2_incremental_decision_proceduret receives success and check-sat "
  "response.",
  "[core][smt2_incremental]")
{
  auto test = decision_procedure_test_environmentt::make();
  SECTION("Expected success response.")
  {
    test.mock_responses = {smt_success_responset{},
                           smt_check_sat_responset{smt_sat_responset{}}};
    REQUIRE_NOTHROW(test.procedure());
  }
  SECTION("Duplicated success messages.")
  {
    test.mock_responses = {smt_success_responset{},
                           smt_success_responset{},
                           smt_check_sat_responset{smt_sat_responset{}}};
    REQUIRE_THROWS_MATCHES(
      test.procedure(),
      analysis_exceptiont,
      analysis_execption_with_messaget{
        "Unexpected kind of response from SMT solver."});
  }
}

TEST_CASE(
  "smt2_incremental_decision_proceduret receives unexpected responses to "
  "check-sat.",
  "[core][smt2_incremental]")
{
  auto test = decision_procedure_test_environmentt::make();
  SECTION("get-value response")
  {
    test.mock_responses = {
      smt_get_value_responset{{{"x", smt_bool_literal_termt{false}}}}};
    REQUIRE_THROWS_MATCHES(
      test.procedure(),
      analysis_exceptiont,
      analysis_execption_with_messaget{
        "Unexpected kind of response from SMT solver."});
  }
  SECTION("error message response")
  {
    test.mock_responses = {smt_error_responset{"foobar"}};
    REQUIRE_THROWS_MATCHES(
      test.procedure(),
      analysis_exceptiont,
      analysis_execption_with_messaget{
        "SMT solver returned an error message - foobar"});
  }
  SECTION("unsupported response")
  {
    test.mock_responses = {smt_unsupported_responset{}};
    REQUIRE_THROWS_MATCHES(
      test.procedure(),
      analysis_exceptiont,
      analysis_execption_with_messaget{
        "SMT solver does not support given command."});
  }
}

TEST_CASE(
  "smt2_incremental_decision_proceduret getting values back from solver.",
  "[core][smt2_incremental]")
{
  auto test = decision_procedure_test_environmentt::make();
  const auto null_object_size_definition =
    test.object_size_function.make_definition(
      0, smt_bit_vector_constant_termt{0, 32});
  const auto invalid_pointer_object_size_definition =
    test.object_size_function.make_definition(
      1, smt_bit_vector_constant_termt{0, 32});
  const symbolt foo = make_test_symbol("foo", signedbv_typet{16});
  const smt_identifier_termt foo_term{"foo", smt_bit_vector_sortt{16}};
  const exprt expr_42 = from_integer({42}, signedbv_typet{16});
  const smt_bit_vector_constant_termt term_42{42, 16};
  SECTION("Set \"foo\" identifier and solve.")
  {
    test.sent_commands.clear();
    const exprt equal_42 = equal_exprt{foo.symbol_expr(), expr_42};
    test.procedure.set_to(equal_42, true);
    test.mock_responses.push_back(smt_check_sat_responset{smt_sat_responset{}});
    test.procedure();
    std::vector<smt_commandt> expected_commands{
      smt_declare_function_commandt{foo_term, {}},
      smt_assert_commandt{smt_core_theoryt::equal(foo_term, term_42)},
      invalid_pointer_object_size_definition,
      null_object_size_definition,
      smt_check_sat_commandt{}};
    REQUIRE(
      (test.sent_commands.size() == expected_commands.size() &&
       std::all_of(
         expected_commands.begin(),
         expected_commands.end(),
         [&](const smt_commandt &command) -> bool {
           return std::find(
                    test.sent_commands.begin(),
                    test.sent_commands.end(),
                    command) != test.sent_commands.end();
         })));
    SECTION("Get \"foo\" value back")
    {
      test.sent_commands.clear();
      test.mock_responses.push_back(
        smt_get_value_responset{{{foo_term, term_42}}});
      REQUIRE(test.procedure.get(foo.symbol_expr()) == expr_42);
      REQUIRE(
        test.sent_commands ==
        std::vector<smt_commandt>{smt_get_value_commandt{foo_term}});
    }
    SECTION("Get value of non-set symbol")
    {
      // smt2_incremental_decision_proceduret is used this way when cbmc is
      // invoked with the combination of `--trace` and `--slice-formula`.
      test.sent_commands.clear();
      const exprt bar =
        make_test_symbol("bar", signedbv_typet{16}).symbol_expr();
      REQUIRE(test.procedure.get(bar) == bar);
      REQUIRE(test.sent_commands.empty());
    }
    SECTION("Get value of type less symbol back")
    {
      // smt2_incremental_decision_proceduret is used this way as part of
      // building the goto trace, to get the partial order concurrency clock
      // values.
      test.sent_commands.clear();
      const symbol_exprt baz = symbol_exprt::typeless("baz");
      REQUIRE(test.procedure.get(baz) == baz);
      REQUIRE(test.sent_commands.empty());
    }
    SECTION("Get value of trivially solved expression")
    {
      test.sent_commands.clear();
      const smt_termt not_true_term =
        smt_core_theoryt::make_not(smt_bool_literal_termt{true});
      test.mock_responses.push_back(smt_get_value_responset{
        {{not_true_term, smt_bool_literal_termt{false}}}});
      REQUIRE(test.procedure.get(not_exprt{true_exprt{}}) == false_exprt{});
      REQUIRE(
        test.sent_commands ==
        std::vector<smt_commandt>{smt_get_value_commandt{not_true_term}});
    }
    SECTION("Invariant violated due to expression in unexpected form.")
    {
      const mult_exprt unexpected{foo.symbol_expr(), from_integer(2, foo.type)};
      const cbmc_invariants_should_throwt invariants_throw;
      REQUIRE_THROWS_MATCHES(
        test.procedure.get(unexpected),
        invariant_failedt,
        invariant_failure_containing(
          "Unhandled expressions are expected to be symbols"));
    }
    SECTION("Error handling of mismatched response.")
    {
      test.sent_commands.clear();
      const smt_check_sat_responset unexpected{smt_sat_responset{}};
      test.mock_responses.push_back(unexpected);
      REQUIRE_THROWS_MATCHES(
        test.procedure.get(foo.symbol_expr()),
        analysis_exceptiont,
        analysis_execption_with_messaget{
          "Expected get-value response from solver, but received - " +
          unexpected.pretty()});
      REQUIRE(
        test.sent_commands ==
        std::vector<smt_commandt>{smt_get_value_commandt{foo_term}});
    }
    SECTION("Error handling of multiple responses.")
    {
      test.sent_commands.clear();
      const smt_get_value_responset unexpected{
        {{foo_term, term_42}, {foo_term, term_42}}};
      test.mock_responses.push_back(unexpected);
      REQUIRE_THROWS_MATCHES(
        test.procedure.get(foo.symbol_expr()),
        analysis_exceptiont,
        analysis_execption_with_messaget{
          "Expected single valuation pair in get-value response from solver, "
          "but received multiple pairs - " +
          unexpected.pretty()});
      REQUIRE(
        test.sent_commands ==
        std::vector<smt_commandt>{smt_get_value_commandt{foo_term}});
    }
  }
}

TEST_CASE(
  "smt2_incremental_decision_proceduret array commands.",
  "[core][smt2_incremental]")
{
  auto test = decision_procedure_test_environmentt::make();
  const auto index_type = signedbv_typet{32};
  const symbolt index = make_test_symbol("index", index_type);
  const auto value_type = signedbv_typet{8};
  const symbolt foo = make_test_symbol("foo", value_type);
  const auto array_type = array_typet{value_type, from_integer(2, index_type)};
  SECTION("array_exprt - list of literal array elements")
  {
    const array_exprt array_literal{
      {from_integer(9, value_type), from_integer(12, value_type)}, array_type};
    test.sent_commands.clear();
    test.procedure.set_to(
      equal_exprt{
        foo.symbol_expr(), index_exprt{array_literal, index.symbol_expr()}},
      true);
    const auto foo_term = smt_identifier_termt{"foo", smt_bit_vector_sortt{8}};
    const auto array_term = smt_identifier_termt{
      "array_0",
      smt_array_sortt{smt_bit_vector_sortt{32}, smt_bit_vector_sortt{8}}};
    const auto index_term =
      smt_identifier_termt{"index", smt_bit_vector_sortt{32}};
    const std::vector<smt_commandt> expected_commands{
      smt_declare_function_commandt{foo_term, {}},
      smt_declare_function_commandt{array_term, {}},
      smt_assert_commandt{smt_core_theoryt::equal(
        smt_array_theoryt::select(
          array_term, smt_bit_vector_constant_termt{0, 32}),
        smt_bit_vector_constant_termt{9, 8})},
      smt_assert_commandt{smt_core_theoryt::equal(
        smt_array_theoryt::select(
          array_term, smt_bit_vector_constant_termt{1, 32}),
        smt_bit_vector_constant_termt{12, 8})},
      smt_declare_function_commandt{index_term, {}},
      smt_assert_commandt{smt_core_theoryt::equal(
        foo_term, smt_array_theoryt::select(array_term, index_term))}};
    REQUIRE(test.sent_commands == expected_commands);

    SECTION("Get values of array literal")
    {
      test.sent_commands.clear();
      test.mock_responses = {
        // get-value response for array_size
        smt_get_value_responset{
          {{{smt_bit_vector_constant_termt{2, 32}},
            smt_bit_vector_constant_termt{2, 32}}}},
        // get-value response for first element
        smt_get_value_responset{
          {{{smt_array_theoryt::select(
              array_term, smt_bit_vector_constant_termt{0, 32})},
            smt_bit_vector_constant_termt{9, 8}}}},
        // get-value response for second element
        smt_get_value_responset{
          {{{smt_array_theoryt::select(
              array_term, smt_bit_vector_constant_termt{1, 32})},
            smt_bit_vector_constant_termt{12, 8}}}}};
      REQUIRE(test.procedure.get(array_literal) == array_literal);
    }
  }
  SECTION("array_of_exprt - all elements set to a given value")
  {
    const array_of_exprt array_of_expr{
      from_integer(42, value_type), array_type};
    test.sent_commands.clear();
    test.procedure.set_to(
      equal_exprt{
        foo.symbol_expr(), index_exprt{array_of_expr, index.symbol_expr()}},
      true);
    const auto foo_term = smt_identifier_termt{"foo", smt_bit_vector_sortt{8}};
    const auto array_term = smt_identifier_termt{
      "array_0",
      smt_array_sortt{smt_bit_vector_sortt{32}, smt_bit_vector_sortt{8}}};
    const auto index_term =
      smt_identifier_termt{"index", smt_bit_vector_sortt{32}};
    const auto forall_term =
      smt_identifier_termt{"array_0_index", smt_bit_vector_sortt{32}};
    const std::vector<smt_commandt> expected_commands{
      smt_declare_function_commandt{foo_term, {}},
      smt_declare_function_commandt{array_term, {}},
      smt_assert_commandt{smt_forall_termt{
        {forall_term},
        smt_core_theoryt::equal(
          smt_array_theoryt::select(array_term, forall_term),
          smt_bit_vector_constant_termt{42, 8})}},
      smt_declare_function_commandt{index_term, {}},
      smt_assert_commandt{smt_core_theoryt::equal(
        foo_term, smt_array_theoryt::select(array_term, index_term))}};
    REQUIRE(test.sent_commands == expected_commands);
  }
}

TEST_CASE(
  "smt2_incremental_decision_proceduret multi-ary with_exprt introduces "
  "correct number of indexes.",
  "[core][smt2_incremental]")
{
  auto test = decision_procedure_test_environmentt::make();
  const signedbv_typet index_type{32};
  const signedbv_typet value_type{8};
  const array_typet array_type{value_type, from_integer(3, index_type)};
  const auto original_array_symbol =
    make_test_symbol("original_array", array_type);
  const auto result_array_symbol = make_test_symbol("result_array", array_type);
  with_exprt with_expr{
    original_array_symbol.symbol_expr(),
    from_integer(0, index_type),
    from_integer(0, value_type)};
  with_expr.add_to_operands(
    from_integer(1, index_type), from_integer(1, value_type));
  with_expr.add_to_operands(
    from_integer(2, index_type), from_integer(2, value_type));
  const equal_exprt equal_expr{result_array_symbol.symbol_expr(), with_expr};
  test.sent_commands.clear();
  test.procedure.set_to(equal_expr, true);

  const smt_bit_vector_sortt smt_index_sort{32};
  const smt_bit_vector_sortt smt_value_sort{8};
  const smt_array_sortt smt_array_sort{smt_index_sort, smt_value_sort};
  const smt_identifier_termt smt_original_array_term{
    "original_array", smt_array_sort};
  const smt_identifier_termt smt_result_array_term{
    "result_array", smt_array_sort};
  const smt_identifier_termt index_0_term{"index_0", smt_index_sort};
  const smt_identifier_termt index_1_term{"index_1", smt_index_sort};
  const smt_identifier_termt index_2_term{"index_2", smt_index_sort};
  const smt_termt store_term = smt_array_theoryt::store(
    smt_array_theoryt::store(
      smt_array_theoryt::store(
        smt_original_array_term,
        index_0_term,
        smt_bit_vector_constant_termt{0, smt_value_sort}),
      index_1_term,
      smt_bit_vector_constant_termt{1, smt_value_sort}),
    index_2_term,
    smt_bit_vector_constant_termt{2, smt_value_sort});
  const auto smt_assertion = smt_assert_commandt{
    smt_core_theoryt::equal(smt_result_array_term, store_term)};
  const std::vector<smt_commandt> expected_commands{
    smt_declare_function_commandt(smt_result_array_term, {}),
    smt_declare_function_commandt(smt_original_array_term, {}),
    smt_define_function_commandt{
      index_0_term.identifier(),
      {},
      smt_bit_vector_constant_termt{0, smt_index_sort}},
    smt_define_function_commandt{
      index_1_term.identifier(),
      {},
      smt_bit_vector_constant_termt{1, smt_index_sort}},
    smt_define_function_commandt{
      index_2_term.identifier(),
      {},
      smt_bit_vector_constant_termt{2, smt_index_sort}},
    smt_assertion};
  REQUIRE(test.sent_commands == expected_commands);
}
