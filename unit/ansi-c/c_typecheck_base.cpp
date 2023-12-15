//
// Author: Enrico Steffinlongo for Diffblue Ltd
//

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/string_constant.h>
#include <util/symbol_table.h>

#include <ansi-c/c_typecheck_base.h>
#include <ansi-c/expr2c.h>
#include <testing-utils/use_catch.h>

class c_typecheck_testt : public c_typecheck_baset
{
public:
  c_typecheck_testt(
    symbol_table_baset &_symbol_table,
    const std::string &_module,
    message_handlert &_message_handler)
    : c_typecheck_baset(_symbol_table, _module, _message_handler)
  {
  }

  void typecheck() override
  {
  }

  std::optional<symbol_exprt> test_typecheck_shadow_memory_builtin(
    const side_effect_expr_function_callt &expr)
  {
    return typecheck_shadow_memory_builtin(expr);
  }

  void test_typecheck_side_effect_function_call(
    side_effect_expr_function_callt &expr)
  {
    typecheck_side_effect_function_call(expr);
  }
};

/// Helper struct to hold useful test components.
struct c_typecheck_test_environmentt
{
  symbol_tablet symbol_table;
  source_locationt loc{};
  null_message_handlert message_handler{};
  c_typecheck_testt c_typecheck_test{symbol_table, "test", message_handler};

  static c_typecheck_test_environmentt make()
  {
    // These config lines are necessary before construction because char size
    // depend on the global configuration.
    config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
    config.ansi_c.set_arch_spec_x86_64();
    c_typecheck_test_environmentt result;
    result.loc.set_file("a_file");
    result.loc.set_line(0);
    result.loc.set_column(0);
    return result;
  }

private:
  c_typecheck_test_environmentt() = default;
};

TEST_CASE(
  "typecheck shadow memory declaration functions",
  "[core][ansi-c][typecheck_shadow_memory_builtin]")
{
  auto test = c_typecheck_test_environmentt::make();

  const std::string function_call_name = GENERATE(
    CPROVER_PREFIX "field_decl_local", CPROVER_PREFIX "field_decl_global");

  SECTION("works on " + function_call_name)
  {
    exprt init_value = GENERATE(
      static_cast<exprt>(from_integer(0, unsigned_char_type())),
      static_cast<exprt>(from_integer(0, char_type())),
      static_cast<exprt>(from_integer(0, bool_typet{})),
      static_cast<exprt>(from_integer(0, unsignedbv_typet{5})),
      static_cast<exprt>(from_integer(0, signedbv_typet{5})),
      typecast_exprt::conditional_cast(
        from_integer(0, unsignedbv_typet{32}), char_type()),
      typecast_exprt::conditional_cast(
        from_integer(0, unsignedbv_typet{32}), bool_typet{}));
    SECTION(
      "with init_value " + type2c(init_value.type(), test.c_typecheck_test) +
      expr2c(init_value, test.c_typecheck_test))
    {
      symbol_exprt symbol_expr{function_call_name, empty_typet{}};
      symbol_expr.add_source_location() = test.loc;
      const side_effect_expr_function_callt expr{
        symbol_expr,
        {string_constantt{"field"}, init_value},
        void_type(),
        test.loc};
      const auto builtin_result =
        test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr);

      code_typet expected_code_type{{}, void_type()};
      expected_code_type.make_ellipsis();
      symbol_exprt expected_symbol_expr{function_call_name, expected_code_type};
      expected_symbol_expr.add_source_location() = test.loc;

      REQUIRE(builtin_result);
      REQUIRE(builtin_result.value() == expected_symbol_expr);
      REQUIRE(test.symbol_table.symbols.empty());

      side_effect_expr_function_callt expr_to_typecheck = expr;

      symbolt expected_symbol{function_call_name, builtin_result->type(), ID_C};
      expected_symbol.base_name = function_call_name;
      expected_symbol.location = expr.source_location();
      expected_symbol.value = code_blockt{};

      test.c_typecheck_test.test_typecheck_side_effect_function_call(
        expr_to_typecheck);

      // We changed the `function()` field of `expr` as expected
      REQUIRE(expr_to_typecheck.function() == builtin_result.value());
      REQUIRE(test.symbol_table.has_symbol(function_call_name));
      REQUIRE(*test.symbol_table.lookup(function_call_name) == expected_symbol);
    }
  }
}

TEST_CASE(
  "typecheck shadow memory declaration functions fail correctly",
  "[core][ansi-c][typecheck_shadow_memory_builtin]")
{
  auto test = c_typecheck_test_environmentt::make();

  const std::string function_call_name = GENERATE(
    CPROVER_PREFIX "field_decl_local", CPROVER_PREFIX "field_decl_global");

  SECTION(" when wrong argument number is provided")
  {
    symbol_exprt symbol_expr{function_call_name, empty_typet{}};
    symbol_expr.add_source_location() = test.loc;
    const side_effect_expr_function_callt expr{
      symbol_expr, {string_constantt{"field"}}, void_type(), test.loc};

    const cbmc_invariants_should_throwt invariants_throw;

    REQUIRE_THROWS_AS(
      test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr),
      invalid_source_file_exceptiont);
  }

  SECTION("when field_name is not a constant_string")
  {
    symbol_exprt symbol_expr{function_call_name, empty_typet{}};
    symbol_expr.add_source_location() = test.loc;
    const side_effect_expr_function_callt expr{
      symbol_expr, {true_exprt(), true_exprt()}, void_type(), test.loc};

    const cbmc_invariants_should_throwt invariants_throw;

    REQUIRE_THROWS_AS(
      test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr),
      invalid_source_file_exceptiont);
  }

  SECTION("when field type is wrong")
  {
    exprt init_value = GENERATE(
      static_cast<exprt>(from_integer(0, unsignedbv_typet{10})),
      from_integer(0, float_type()),
      from_integer(0, pointer_typet{char_type(), 32}),
      string_constantt{"a_value"});

    SECTION(
      "init_value is " + type2c(init_value.type(), test.c_typecheck_test) +
      " " + expr2c(init_value, test.c_typecheck_test))
    {
      symbol_exprt symbol_expr{function_call_name, empty_typet{}};
      symbol_expr.add_source_location() = test.loc;
      const side_effect_expr_function_callt expr{
        symbol_expr,
        {string_constantt{"field"}, init_value},
        void_type(),
        test.loc};

      const cbmc_invariants_should_throwt invariants_throw;

      REQUIRE_THROWS_AS(
        test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr),
        invalid_source_file_exceptiont);
    }
  }
}

TEST_CASE(
  "typecheck shadow memory get_field works",
  "[core][ansi-c][typecheck_shadow_memory_builtin]")
{
  auto test = c_typecheck_test_environmentt::make();

  const std::string function_call_name = CPROVER_PREFIX "get_field";

  const pointer_typet pointer_type{char_type(), 32};
  // We don't care that the pointer is null. At typecheck we just care that the
  // type of the argument is pointer.
  const null_pointer_exprt pointer{pointer_type};

  symbol_exprt symbol_expr{function_call_name, empty_typet{}};
  symbol_expr.add_source_location() = test.loc;
  const side_effect_expr_function_callt expr{
    symbol_expr, {pointer, string_constantt{"field"}}, void_type(), test.loc};
  const auto builtin_result =
    test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr);

  code_typet expected_code_type{{}, signed_int_type()};
  expected_code_type.make_ellipsis();
  symbol_exprt expected_symbol_expr{function_call_name, expected_code_type};
  expected_symbol_expr.add_source_location() = test.loc;

  REQUIRE(builtin_result);
  REQUIRE(builtin_result.value() == expected_symbol_expr);
  REQUIRE(test.symbol_table.symbols.empty());

  side_effect_expr_function_callt expr_to_typecheck = expr;

  symbolt expected_symbol{function_call_name, builtin_result->type(), ID_C};
  expected_symbol.base_name = function_call_name;
  expected_symbol.location = expr.source_location();
  expected_symbol.value = code_blockt{};

  test.c_typecheck_test.test_typecheck_side_effect_function_call(
    expr_to_typecheck);

  // We changed the `function()` field of `expr` as expected
  REQUIRE(expr_to_typecheck.function() == builtin_result.value());
  REQUIRE(test.symbol_table.has_symbol(function_call_name));
  REQUIRE(*test.symbol_table.lookup(function_call_name) == expected_symbol);
}

TEST_CASE(
  "typecheck shadow memory get_field fails correctly",
  "[core][ansi-c][typecheck_shadow_memory_builtin]")
{
  auto test = c_typecheck_test_environmentt::make();

  const std::string function_call_name = CPROVER_PREFIX "get_field";

  SECTION(" when wrong argument number is provided")
  {
    symbol_exprt symbol_expr{function_call_name, empty_typet{}};
    symbol_expr.add_source_location() = test.loc;
    const side_effect_expr_function_callt expr{
      symbol_expr, {string_constantt{"field"}}, void_type(), test.loc};

    const cbmc_invariants_should_throwt invariants_throw;

    REQUIRE_THROWS_AS(
      test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr),
      invalid_source_file_exceptiont);
  }

  SECTION("when pointer type is wrong")
  {
    exprt pointer_value = GENERATE(
      from_integer(0, unsignedbv_typet{32}),
      from_integer(0, pointer_typet{void_type(), 32}));

    SECTION(
      "pointer_value is " +
      type2c(pointer_value.type(), test.c_typecheck_test) + " " +
      expr2c(pointer_value, test.c_typecheck_test))
    {
      symbol_exprt symbol_expr{function_call_name, empty_typet{}};
      symbol_expr.add_source_location() = test.loc;
      const side_effect_expr_function_callt expr{
        symbol_expr,
        {pointer_value, string_constantt{"field"}},
        void_type(),
        test.loc};

      const cbmc_invariants_should_throwt invariants_throw;

      REQUIRE_THROWS_AS(
        test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr),
        invalid_source_file_exceptiont);
    }
  }

  SECTION("when field_name is not a constant_string")
  {
    symbol_exprt symbol_expr{function_call_name, empty_typet{}};
    symbol_expr.add_source_location() = test.loc;
    const side_effect_expr_function_callt expr{
      symbol_expr,
      {from_integer(0, pointer_typet{char_type(), 32}), true_exprt()},
      void_type(),
      test.loc};

    const cbmc_invariants_should_throwt invariants_throw;

    REQUIRE_THROWS_AS(
      test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr),
      invalid_source_file_exceptiont);
  }
}

TEST_CASE(
  "typecheck shadow memory set_field works",
  "[core][ansi-c][typecheck_shadow_memory_builtin]")
{
  auto test = c_typecheck_test_environmentt::make();

  const std::string function_call_name = CPROVER_PREFIX "set_field";

  const pointer_typet pointer_type{char_type(), 32};
  // We don't care that the pointer is null. At typecheck we just care that the
  // type of the argument is pointer.
  const null_pointer_exprt pointer{pointer_type};

  exprt set_value = GENERATE(
    from_integer(0, unsigned_char_type()),
    from_integer(0, char_type()),
    from_integer(0, bool_typet{}),
    from_integer(0, unsignedbv_typet{5}),
    from_integer(0, signedbv_typet{5}),
    from_integer(0, signedbv_typet{32}),
    from_integer(0, unsignedbv_typet{32}));

  SECTION(
    "with init_value: " + type2c(set_value.type(), test.c_typecheck_test) +
    " " + expr2c(set_value, test.c_typecheck_test))
  {
    symbol_exprt symbol_expr{function_call_name, empty_typet{}};
    symbol_expr.add_source_location() = test.loc;
    const side_effect_expr_function_callt expr{
      symbol_expr,
      {pointer, string_constantt{"field"}, set_value},
      void_type(),
      test.loc};
    const auto builtin_result =
      test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr);

    code_typet expected_code_type{{}, void_type()};
    expected_code_type.make_ellipsis();
    symbol_exprt expected_symbol_expr{function_call_name, expected_code_type};
    expected_symbol_expr.add_source_location() = test.loc;

    REQUIRE(builtin_result);
    REQUIRE(builtin_result.value() == expected_symbol_expr);
    REQUIRE(test.symbol_table.symbols.empty());

    side_effect_expr_function_callt expr_to_typecheck = expr;

    symbolt expected_symbol{function_call_name, builtin_result->type(), ID_C};
    expected_symbol.base_name = function_call_name;
    expected_symbol.location = expr.source_location();
    expected_symbol.value = code_blockt{};

    test.c_typecheck_test.test_typecheck_side_effect_function_call(
      expr_to_typecheck);

    // We changed the `function()` field of `expr` as expected
    REQUIRE(expr_to_typecheck.function() == builtin_result.value());
    REQUIRE(test.symbol_table.has_symbol(function_call_name));
    REQUIRE(*test.symbol_table.lookup(function_call_name) == expected_symbol);
  }
}

TEST_CASE(
  "typecheck shadow memory set_field fails correctly",
  "[core][ansi-c][typecheck_shadow_memory_builtin]")
{
  auto test = c_typecheck_test_environmentt::make();

  const std::string function_call_name = CPROVER_PREFIX "set_field";

  SECTION("when wrong argument number is provided")
  {
    symbol_exprt symbol_expr{function_call_name, empty_typet{}};
    symbol_expr.add_source_location() = test.loc;
    const side_effect_expr_function_callt expr{
      symbol_expr, {string_constantt{"field"}}, void_type(), test.loc};

    const cbmc_invariants_should_throwt invariants_throw;

    REQUIRE_THROWS_AS(
      test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr),
      invalid_source_file_exceptiont);
  }

  SECTION("when pointer type is wrong")
  {
    exprt pointer_value = GENERATE(
      from_integer(0, unsignedbv_typet{32}),
      from_integer(0, pointer_typet{void_type(), 32}));

    SECTION(
      "pointer_value is " +
      type2c(pointer_value.type(), test.c_typecheck_test) + " " +
      expr2c(pointer_value, test.c_typecheck_test))
    {
      symbol_exprt symbol_expr{function_call_name, empty_typet{}};
      symbol_expr.add_source_location() = test.loc;
      const side_effect_expr_function_callt expr{
        symbol_expr,
        {pointer_value, string_constantt{"field"}, true_exprt{}},
        void_type(),
        test.loc};

      const cbmc_invariants_should_throwt invariants_throw;

      REQUIRE_THROWS_AS(
        test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr),
        invalid_source_file_exceptiont);
    }
  }

  SECTION("when field_name is not a constant_string")
  {
    symbol_exprt symbol_expr{function_call_name, empty_typet{}};
    symbol_expr.add_source_location() = test.loc;
    const side_effect_expr_function_callt expr{
      symbol_expr,
      {from_integer(0, pointer_typet{char_type(), 32}),
       true_exprt(),
       true_exprt{}},
      void_type(),
      test.loc};

    const cbmc_invariants_should_throwt invariants_throw;

    REQUIRE_THROWS_AS(
      test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr),
      invalid_source_file_exceptiont);
  }

  SECTION("when set_value is not valid")
  {
    symbol_exprt symbol_expr{function_call_name, empty_typet{}};
    symbol_expr.add_source_location() = test.loc;
    const side_effect_expr_function_callt expr{
      symbol_expr,
      {from_integer(0, pointer_typet{char_type(), 32}),
       string_constantt{"field"},
       string_constantt{"a_value"}},
      void_type(),
      test.loc};

    const cbmc_invariants_should_throwt invariants_throw;

    REQUIRE_THROWS_AS(
      test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr),
      invalid_source_file_exceptiont);
  }
}

TEST_CASE(
  "typecheck_shadow_memory_builtin returns nothing if not shadow memory",
  "[core][ansi-c][typecheck_shadow_memory_builtin]")
{
  auto test = c_typecheck_test_environmentt::make();

  const std::string function_call_name = "foo";

  symbol_exprt symbol_expr{function_call_name, empty_typet{}};
  const side_effect_expr_function_callt expr{
    symbol_expr, {string_constantt{"field"}}, void_type(), test.loc};
  const auto builtin_result =
    test.c_typecheck_test.test_typecheck_shadow_memory_builtin(expr);

  REQUIRE_FALSE(builtin_result.has_value());
}
