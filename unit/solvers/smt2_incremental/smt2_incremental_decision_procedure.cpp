// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/config.h>
#include <util/exception_utils.h>
#include <util/namespace.h>
#include <util/string_constant.h>
#include <util/symbol_table.h>

#include <solvers/smt2_incremental/ast/smt_commands.h>
#include <solvers/smt2_incremental/ast/smt_responses.h>
#include <solvers/smt2_incremental/ast/smt_sorts.h>
#include <solvers/smt2_incremental/ast/smt_terms.h>
#include <solvers/smt2_incremental/encoding/nondet_padding.h>
#include <solvers/smt2_incremental/smt2_incremental_decision_procedure.h>
#include <solvers/smt2_incremental/smt_solver_process.h>
#include <solvers/smt2_incremental/theories/smt_array_theory.h>
#include <solvers/smt2_incremental/theories/smt_bit_vector_theory.h>
#include <solvers/smt2_incremental/theories/smt_core_theory.h>
#include <testing-utils/invariant.h>
#include <testing-utils/use_catch.h>

// Used by catch framework for printing in the case of test failures. This
// means that we get error messages showing the smt formula expressed as SMT2
// strings instead of `{?}` being printed. It works because catch uses the
// appropriate overload of `operator<<` where it exists.
#include <util/byte_operators.h>
#include <util/c_types.h>

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
  smt_is_dynamic_objectt is_dynamic_object_function;
  smt2_incremental_decision_proceduret procedure{
    ns,
    std::make_unique<smt_mock_solver_processt>(
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
  return symbolt{std::move(id), std::move(type), irep_idt{}};
}

static symbolt make_test_symbol(irep_idt id, exprt value)
{
  symbolt new_symbol{std::move(id), value.type(), irep_idt{}};
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
        test.object_size_function.declaration,
        test.is_dynamic_object_function.declaration});
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
          smt_declare_function_commandt{comparison_conjunction_term, {}},
          smt_assert_commandt{comparison_conjunction_term}});
    }
    SECTION("Set with nondet_padding")
    {
      const exprt to_set = equal_exprt{
        concatenation_exprt{
          {nondet_padding_exprt{bv_typet{8}}, from_integer(42, bv_typet{8})},
          bv_typet{16}},
        from_integer(42, bv_typet{16})};
      test.sent_commands.clear();
      test.procedure.set_to(to_set, true);
      // (declare-fun padding_0 () (_ BitVec 8))
      // (assert (= (concat padding_0 (_ bv42 8)) (_ bv42 16)))
      const auto expected_padding_term =
        smt_identifier_termt{"padding_0", smt_bit_vector_sortt{8}};
      REQUIRE(
        test.sent_commands ==
        std::vector<smt_commandt>{
          smt_declare_function_commandt{expected_padding_term, {}},
          smt_assert_commandt{smt_core_theoryt::equal(
            smt_bit_vector_theoryt::concat(
              expected_padding_term, smt_bit_vector_constant_termt{42, 8}),
            smt_bit_vector_constant_termt{42, 16})}});
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
          smt_declare_function_commandt{
            smt_identifier_termt{"bar", smt_bit_vector_sortt{8}}, {}},
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
  const auto null_object_dynamic_definition =
    test.is_dynamic_object_function.make_definition(0, false);
  const auto invalid_pointer_object_dynamic_definition =
    test.is_dynamic_object_function.make_definition(1, false);
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
      null_object_dynamic_definition,
      invalid_pointer_object_dynamic_definition,
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
    SECTION("Invariant violation due to non-set symbol")
    {
      test.sent_commands.clear();
      const exprt bar =
        make_test_symbol("bar", signedbv_typet{16}).symbol_expr();
      REQUIRE(test.sent_commands.empty());
      cbmc_invariants_should_throwt invariants_throw;
      REQUIRE_THROWS_MATCHES(
        test.procedure.get(bar),
        invariant_failedt,
        invariant_failure_containing(
          "symbol expressions must have a known value"));
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
      const auto offset = from_integer(2, signedbv_typet{64});
      const byte_extract_exprt byte_extract_expr{
        ID_byte_extract_little_endian,
        foo.symbol_expr(),
        offset,
        8,
        unsignedbv_typet{8}};
      test.mock_responses.push_back(
        smt_get_value_responset{{{foo_term, term_42}}});
      test.mock_responses.push_back(smt_get_value_responset{
        {{smt_bit_vector_constant_termt{2, 64},
          smt_bit_vector_constant_termt{2, 64}}}});
      REQUIRE(
        test.procedure.get(byte_extract_expr) ==
        byte_extract_exprt{
          ID_byte_extract_little_endian,
          expr_42,
          offset,
          8,
          unsignedbv_typet{8}});
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
  "smt2_incremental_decision_proceduret string literal commands.",
  "[core][smt2_incremental]")
{
  auto test = decision_procedure_test_environmentt::make();
  const string_constantt constant{"Chips"};
  const typet array_type = constant.to_array_expr().type();
  const symbolt fish{"fish", array_type, ID_C};
  test.symbol_table.insert(fish);
  test.sent_commands.clear();
  test.procedure.set_to(equal_exprt{fish.symbol_expr(), constant}, true);
  const smt_array_sortt expected_sort{
    smt_bit_vector_sortt{32}, smt_bit_vector_sortt{8}};
  const smt_identifier_termt expected_fish{"fish", expected_sort};
  const smt_identifier_termt expected_chips{"array_0", expected_sort};
  const std::vector<smt_commandt> expected_commands{
    smt_declare_function_commandt{expected_fish, {}},
    smt_declare_function_commandt{expected_chips, {}},
    smt_assert_commandt{smt_core_theoryt::equal(
      smt_array_theoryt::select(
        expected_chips, smt_bit_vector_constant_termt{0, 32}),
      smt_bit_vector_constant_termt{'C', 8})},
    smt_assert_commandt{smt_core_theoryt::equal(
      smt_array_theoryt::select(
        expected_chips, smt_bit_vector_constant_termt{1, 32}),
      smt_bit_vector_constant_termt{'h', 8})},
    smt_assert_commandt{smt_core_theoryt::equal(
      smt_array_theoryt::select(
        expected_chips, smt_bit_vector_constant_termt{2, 32}),
      smt_bit_vector_constant_termt{'i', 8})},
    smt_assert_commandt{smt_core_theoryt::equal(
      smt_array_theoryt::select(
        expected_chips, smt_bit_vector_constant_termt{3, 32}),
      smt_bit_vector_constant_termt{'p', 8})},
    smt_assert_commandt{smt_core_theoryt::equal(
      smt_array_theoryt::select(
        expected_chips, smt_bit_vector_constant_termt{4, 32}),
      smt_bit_vector_constant_termt{'s', 8})},
    smt_assert_commandt{smt_core_theoryt::equal(
      smt_array_theoryt::select(
        expected_chips, smt_bit_vector_constant_termt{5, 32}),
      smt_bit_vector_constant_termt{'\0', 8})},
    smt_assert_commandt{
      smt_core_theoryt::equal(expected_fish, expected_chips)}};
  REQUIRE(test.sent_commands == expected_commands);
}

TEST_CASE(
  "smt2_incremental_decision_proceduret function pointer support.",
  "[core][smt2_incremental]")
{
  auto test = decision_procedure_test_environmentt::make();
  const code_typet function_type{{}, void_type()};
  const symbolt function{"opaque", function_type, ID_C};
  test.symbol_table.insert(function);
  const address_of_exprt function_pointer{function.symbol_expr()};
  const equal_exprt equals_null{
    function_pointer, null_pointer_exprt{pointer_typet{function_type, 32}}};

  test.sent_commands.clear();
  test.procedure.set_to(equals_null, false);

  const std::vector<smt_commandt> expected_commands{
    smt_assert_commandt{smt_core_theoryt::make_not(smt_core_theoryt::equal(
      smt_bit_vector_theoryt::concat(
        smt_bit_vector_constant_termt{2, 8},
        smt_bit_vector_constant_termt{0, 24}),
      smt_bit_vector_constant_termt{0, 32}))}};
  REQUIRE(test.sent_commands == expected_commands);
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

TEST_CASE(
  "smt2_incremental_decision_proceduret union support.",
  "[core][smt2_incremental]")
{
  auto test = decision_procedure_test_environmentt::make();
  // union foot{ int8_t eggs, uint32_t ham } foo;
  const struct_union_typet::componentst components{
    {"eggs", unsignedbv_typet{8}}, {"ham", signedbv_typet{32}}};
  const type_symbolt type_symbol{"foot", union_typet{components}, ID_C};
  test.symbol_table.insert(type_symbol);
  const union_tag_typet union_tag{type_symbol.name};
  const symbolt union_value_symbol{"foo", union_tag, ID_C};
  test.symbol_table.insert(union_value_symbol);
  // assume(foo == foot{ .eggs = 12 });
  const auto symbol_expr = union_value_symbol.symbol_expr();
  const auto dozen = from_integer(12, unsignedbv_typet{8});
  const auto union_needing_padding = union_exprt{"eggs", dozen, union_tag};
  const auto equals = equal_exprt{symbol_expr, union_needing_padding};
  test.sent_commands.clear();
  test.procedure.set_to(equals, true);

  // (declare-fun foo () (_ BitVec 32))
  // (declare-fun padding_0 () (_ BitVec 24))
  // (assert (= foo (concat padding_0 (_ bv12 8)))) }
  const auto foo_term = smt_identifier_termt{"foo", smt_bit_vector_sortt{32}};
  const auto padding_term =
    smt_identifier_termt{"padding_0", smt_bit_vector_sortt{24}};
  const std::vector<smt_commandt> expected_set_commands{
    smt_declare_function_commandt{foo_term, {}},
    smt_declare_function_commandt{padding_term, {}},
    smt_assert_commandt{smt_core_theoryt::equal(
      foo_term,
      smt_bit_vector_theoryt::concat(
        padding_term, smt_bit_vector_constant_termt{12, 8}))}};
  REQUIRE(test.sent_commands == expected_set_commands);

  INFO("Ensuring decision procedure in suitable state for getting values.");
  test.mock_responses.push_back(smt_check_sat_responset{smt_sat_responset{}});
  test.procedure();

  INFO("Getting union typed value.");
  test.sent_commands.clear();
  test.mock_responses.push_back(smt_get_value_responset{
    {{foo_term, smt_bit_vector_constant_termt{~uint32_t{255} | 12, 32}}}});
  const auto expected_value = union_exprt{"eggs", dozen, union_tag};
  REQUIRE(test.procedure.get(symbol_expr) == expected_value);
  const std::vector<smt_commandt> expected_get_commands{
    smt_get_value_commandt{foo_term}};
  REQUIRE(test.sent_commands == expected_get_commands);
}

TEST_CASE(
  "smt2_incremental_decision_proceduret byte update-extract commands.",
  "[core][smt2_incremental]")
{
  auto test = decision_procedure_test_environmentt::make();
  SECTION("byte_extract - byte from int correctly extracted.")
  {
    const auto int64_type = signedbv_typet(64);
    const auto byte_type = signedbv_typet(8);
    const auto extracted_byte_symbol =
      make_test_symbol("extracted_byte", byte_type);
    const auto original_int_symbol =
      make_test_symbol("original_int", int64_type);
    const auto byte_extract = make_byte_extract(
      original_int_symbol.symbol_expr(),
      from_integer(1, int64_type),
      byte_type);
    const typecast_exprt typecast_expr{byte_extract, byte_type};
    const equal_exprt equal_expr{
      extracted_byte_symbol.symbol_expr(), typecast_expr};
    test.sent_commands.clear();
    test.procedure.set_to(equal_expr, true);
    const smt_bit_vector_sortt smt_int64_type{64};
    const smt_bit_vector_sortt smt_byte_type{8};
    const smt_identifier_termt extracted_byte_term{
      "extracted_byte", smt_byte_type};
    const smt_identifier_termt original_int{"original_int", smt_int64_type};
    const smt_termt smt_equal_term = smt_core_theoryt::equal(
      extracted_byte_term,
      smt_bit_vector_theoryt::extract(15, 8)(original_int));
    const auto smt_assertion = smt_assert_commandt{smt_equal_term};
    const std::vector<smt_commandt> expected_commands{
      smt_declare_function_commandt(extracted_byte_term, {}),
      smt_declare_function_commandt(original_int, {}),
      smt_assertion};
    REQUIRE(test.sent_commands == expected_commands);
  }
  SECTION("byte_extract - int from byte correctly extracted.")
  {
    const auto byte_type = signedbv_typet(8);
    const auto int16_type = signedbv_typet(16);
    const auto ptr_type = signedbv_typet(32);
    const auto extracted_int_symbol =
      make_test_symbol("extracted_int", int16_type);
    const auto original_byte_array_symbol = make_test_symbol(
      "original_byte_array", array_typet(byte_type, from_integer(2, ptr_type)));
    const auto byte_extract = make_byte_extract(
      original_byte_array_symbol.symbol_expr(),
      from_integer(0, ptr_type),
      int16_type);
    const equal_exprt equal_expr{
      extracted_int_symbol.symbol_expr(), byte_extract};
    test.sent_commands.clear();
    test.procedure.set_to(equal_expr, true);
    const smt_bit_vector_sortt smt_int16_type{16};
    const smt_bit_vector_sortt smt_ptr_type{32};
    const smt_bit_vector_sortt smt_byte_type{8};
    const smt_identifier_termt extracted_int_term{
      "extracted_int", smt_int16_type};
    const smt_identifier_termt original_byte_array_term{
      "original_byte_array", smt_array_sortt{smt_ptr_type, smt_byte_type}};
    const smt_termt smt_equal_term = smt_core_theoryt::equal(
      extracted_int_term,
      smt_bit_vector_theoryt::concat(
        smt_array_theoryt::select(
          original_byte_array_term,
          smt_bit_vector_constant_termt{1, smt_ptr_type}),
        smt_array_theoryt::select(
          original_byte_array_term,
          smt_bit_vector_constant_termt{0, smt_ptr_type})));
    const auto smt_assertion = smt_assert_commandt{smt_equal_term};
    const std::vector<smt_commandt> expected_commands{
      smt_declare_function_commandt(extracted_int_term, {}),
      smt_declare_function_commandt(original_byte_array_term, {}),
      smt_assertion};
    REQUIRE(test.sent_commands == expected_commands);
  }
  SECTION("byte_update - write bytes into int.")
  {
    const auto int64_type = signedbv_typet(64);
    const auto byte_type = signedbv_typet(8);
    const auto result_int_symbol = make_test_symbol("result_int", int64_type);
    const auto original_int_symbol =
      make_test_symbol("original_int", int64_type);
    const auto byte_update = make_byte_update(
      original_int_symbol.symbol_expr(),
      from_integer(1, int64_type),
      from_integer(0x0B, byte_type));
    const equal_exprt equal_expr{result_int_symbol.symbol_expr(), byte_update};
    test.sent_commands.clear();
    test.procedure.set_to(equal_expr, true);
    const smt_bit_vector_sortt smt_value_type{64};
    const smt_identifier_termt result_int_term{"result_int", smt_value_type};
    const smt_identifier_termt original_int_term{
      "original_int", smt_value_type};
    const smt_termt smt_equal_term = smt_core_theoryt::equal(
      result_int_term,
      smt_bit_vector_theoryt::make_or(
        smt_bit_vector_theoryt::make_and(
          original_int_term,
          smt_bit_vector_constant_termt{0xFFFFFFFFFFFF00FF, 64}),
        smt_bit_vector_constant_termt{0x0B00, 64}));
    const auto smt_assertion = smt_assert_commandt{smt_equal_term};
    const std::vector<smt_commandt> expected_commands{
      smt_declare_function_commandt{result_int_term, {}},
      smt_declare_function_commandt{original_int_term, {}},
      smt_assertion};
    REQUIRE(test.sent_commands == expected_commands);
  }
  SECTION("byte_update - writes int into byte array.")
  {
    const auto int32_type = signedbv_typet(32);
    const auto int16_type = signedbv_typet(16);
    const auto byte_type = signedbv_typet(8);
    const array_typet byte_array_type{byte_type, from_integer(2, int32_type)};
    const auto result_array_symbol =
      make_test_symbol("result_array", byte_array_type);
    const auto original_array_symbol =
      make_test_symbol("original_array", byte_array_type);
    const auto byte_update = make_byte_update(
      original_array_symbol.symbol_expr(),
      from_integer(0, int32_type),
      from_integer(0x0102, int16_type));
    const equal_exprt equal_expr{
      result_array_symbol.symbol_expr(), byte_update};
    test.sent_commands.clear();
    test.procedure.set_to(equal_expr, true);
    const smt_bit_vector_sortt smt_byte_type{8};
    const smt_bit_vector_sortt smt_index_type{32};
    const smt_array_sortt smt_array_type{smt_index_type, smt_byte_type};
    const smt_identifier_termt result_array_term{
      "result_array", smt_array_type};
    const smt_identifier_termt original_array_term{
      "original_array", smt_array_type};
    const smt_identifier_termt index_0_term{"index_0", smt_index_type};
    const smt_identifier_termt index_1_term{"index_1", smt_index_type};
    const smt_termt smt_equal_term = smt_core_theoryt::equal(
      result_array_term,
      smt_array_theoryt::store(
        smt_array_theoryt::store(
          original_array_term,
          index_0_term,
          smt_bit_vector_constant_termt{2, smt_byte_type}),
        index_1_term,
        smt_bit_vector_constant_termt{1, smt_byte_type}));
    const auto smt_assertion = smt_assert_commandt{smt_equal_term};
    const std::vector<smt_commandt> expected_commands{
      smt_declare_function_commandt{result_array_term, {}},
      smt_declare_function_commandt{original_array_term, {}},
      smt_define_function_commandt{
        index_0_term.identifier(),
        {},
        smt_bit_vector_constant_termt{0, smt_index_type}},
      smt_define_function_commandt{
        index_1_term.identifier(),
        {},
        smt_bit_vector_constant_termt{1, smt_index_type}},
      smt_assertion};
    REQUIRE(test.sent_commands == expected_commands);
  }
}

static c_enum_typet make_c_enum_type(
  const unsignedbv_typet &underlying_type,
  unsigned int value_count)
{
  c_enum_typet enum_type{underlying_type};

  auto &members = enum_type.members();
  members.reserve(value_count);

  for(unsigned int i = 0; i < value_count; ++i)
  {
    c_enum_typet::c_enum_membert member;
    member.set_identifier("V" + std::to_string(i));
    member.set_base_name("V" + std::to_string(i));
    member.set_value(integer2bvrep(i, underlying_type.get_width()));
    members.push_back(member);
  }
  return enum_type;
}

TEST_CASE(
  "smt2_incremental_decision_proceduret getting enum values back from solver.",
  "[core][smt2_incremental]")
{
  auto test = decision_procedure_test_environmentt::make();
  const unsignedbv_typet enum_underlying_type{32};
  const c_enum_typet enum_type = make_c_enum_type(enum_underlying_type, 5);
  const type_symbolt enum_symbol{"my_enum", enum_type, ID_C};
  test.symbol_table.insert(enum_symbol);
  const c_enum_tag_typet enum_tag{enum_symbol.name};
  const symbolt enum_value_symbol{"my_enum_value", enum_tag, ID_C};
  test.symbol_table.insert(enum_value_symbol);
  const auto symbol_expr = enum_value_symbol.symbol_expr();
  const auto eq_expr = equal_exprt{symbol_expr, symbol_expr};

  test.procedure.handle(eq_expr);
  test.mock_responses.push_back(
    smt_get_value_responset{{{"B0", smt_bool_literal_termt{true}}}});
  auto returned = test.procedure.get(eq_expr);

  REQUIRE(returned == constant_exprt{"true", bool_typet{}});
}

TEST_CASE(
  "smt2_incremental_decision_proceduret getting value of empty struct",
  "[core][smt2_incremental]")
{
  auto test = decision_procedure_test_environmentt::make();
  const struct_union_typet::componentst component_types{};
  const type_symbolt type_symbol{"emptyt", struct_typet{component_types}, ID_C};
  test.symbol_table.insert(type_symbol);
  const struct_tag_typet type_reference{type_symbol.name};
  const symbolt foo{"foo", type_reference, ID_C};
  test.symbol_table.insert(foo);
  const symbolt bar{"bar", type_reference, ID_C};
  test.symbol_table.insert(bar);

  INFO("Sanity checking decision procedure and flushing size definitions");
  test.mock_responses.push_front(smt_check_sat_responset{smt_sat_responset{}});
  CHECK(test.procedure() == decision_proceduret::resultt::D_SATISFIABLE);
  test.sent_commands.clear();

  INFO("Defining an equality over empty structs");
  const auto equality_expression =
    test.procedure.handle(equal_exprt{foo.symbol_expr(), bar.symbol_expr()});
  test.procedure.set_to(equality_expression, true);
  const smt_identifier_termt expected_foo{"foo", smt_bit_vector_sortt{8}};
  const smt_identifier_termt expected_bar{"bar", smt_bit_vector_sortt{8}};
  const smt_identifier_termt expected_handle{"B0", smt_bool_sortt{}};
  const smt_termt expected_equality =
    smt_core_theoryt::equal(expected_foo, expected_bar);
  const std::vector<smt_commandt> expected_problem_commands{
    smt_declare_function_commandt{expected_foo, {}},
    smt_declare_function_commandt{expected_bar, {}},
    smt_define_function_commandt{"B0", {}, expected_equality},
    smt_assert_commandt{expected_equality}};
  REQUIRE(test.sent_commands == expected_problem_commands);
  test.sent_commands.clear();

  INFO("Ensuring decision procedure is in suitable state for getting output.");
  const std::vector<smt_commandt> expected_check_commands{
    smt_check_sat_commandt{}};
  test.mock_responses.push_front(smt_check_sat_responset{smt_sat_responset{}});
  REQUIRE(test.procedure() == decision_proceduret::resultt::D_SATISFIABLE);
  CHECK(test.sent_commands == expected_check_commands);
  test.sent_commands.clear();

  INFO("Getting values involving empty structs.");
  test.mock_responses.push_front(
    smt_get_value_responset{{{expected_handle, smt_bool_literal_termt{true}}}});
  CHECK(test.procedure.get(equality_expression) == true_exprt{});
  test.mock_responses.push_front(smt_get_value_responset{
    {{smt_identifier_termt{"foo", smt_bit_vector_sortt{8}},
      smt_bit_vector_constant_termt{0, 8}}}});
  const struct_exprt expected_empty{{}, type_reference};
  CHECK(test.procedure.get(foo.symbol_expr()) == expected_empty);
  const std::vector<smt_commandt> expected_get_commands{
    smt_get_value_commandt{expected_handle},
    smt_get_value_commandt{expected_foo}};
  CHECK(test.sent_commands == expected_get_commands);
}

TEST_CASE(
  "smt2_incremental_decision_proceduret getting value of struct-symbols with "
  "value in the symbol table",
  "[core][util][expr_initializer]")
{
  auto test = decision_procedure_test_environmentt::make();

  const struct_union_typet::componentst inner_struct_type_components{
    {"foo", signedbv_typet{32}}, {"bar", unsignedbv_typet{16}}};
  const struct_typet inner_struct_type{inner_struct_type_components};
  const type_symbolt inner_struct_type_symbol{
    "inner_struct_type_symbol", inner_struct_type, ID_C};
  test.symbol_table.insert(inner_struct_type_symbol);
  const struct_tag_typet inner_struct_type_tag{inner_struct_type_symbol.name};

  const struct_union_typet::componentst struct_components{
    {"fizz", c_bool_type()}, {"bar", inner_struct_type_tag}};
  const struct_typet struct_type{struct_components};
  const type_symbolt struct_type_symbol{
    "struct_type_symbol", struct_type, ID_C};
  test.symbol_table.insert(struct_type_symbol);
  const struct_tag_typet struct_tag{struct_type_symbol.name};

  const exprt::operandst inner_struct_operands{
    from_integer(10, signedbv_typet{32}),
    from_integer(23, unsignedbv_typet{16})};
  const struct_exprt inner_struct_expr{
    inner_struct_operands, inner_struct_type_tag};
  symbolt inner_symbol_with_value{
    "inner_symbol_with_value", inner_struct_type_tag, ID_C};
  inner_symbol_with_value.value = inner_struct_expr;
  test.symbol_table.insert(inner_symbol_with_value);
  const symbol_exprt inner_symbol_expr{
    inner_symbol_with_value.name, inner_symbol_with_value.type};

  const exprt::operandst struct_operands{
    from_integer(1, c_bool_type()), inner_symbol_expr};
  const struct_exprt struct_expr{struct_operands, struct_tag};

  symbolt symbol_with_value{"symbol_with_value", struct_tag, ID_C};
  symbol_with_value.value = struct_expr;
  test.symbol_table.insert(symbol_with_value);

  const symbol_exprt symbol_expr{
    symbol_with_value.name, symbol_with_value.type};

  const equal_exprt equal_expr{symbol_expr, symbol_expr};

  test.sent_commands.clear();
  test.procedure.set_to(equal_expr, true);

  std::vector<smt_commandt> expected_commands{
    smt_declare_function_commandt{
      smt_identifier_termt{symbol_with_value.name, smt_bit_vector_sortt{56}},
      {}},
    smt_assert_commandt{smt_core_theoryt::equal(
      smt_identifier_termt{symbol_with_value.name, smt_bit_vector_sortt{56}},
      smt_identifier_termt{symbol_with_value.name, smt_bit_vector_sortt{56}})}};

  CHECK(test.sent_commands == expected_commands);
}
