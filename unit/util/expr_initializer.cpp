// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_initializer.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

#include <testing-utils/invariant.h>
#include <testing-utils/use_catch.h>

#include <iomanip>
#include <sstream>

/// Helper struct to hold useful test components.
struct expr_initializer_test_environmentt
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  source_locationt loc{};

  static expr_initializer_test_environmentt make()
  {
    // These config lines are necessary before construction because char size
    // depend on the global configuration.
    config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
    config.ansi_c.set_arch_spec_x86_64();
    return {};
  }

private:
  expr_initializer_test_environmentt() = default;
};

/// Helper function to create and populate a c_enum_typet type.
static c_enum_typet make_c_enum_type(const unsignedbv_typet &underlying_type)
{
  c_enum_typet enum_type{underlying_type};

  auto &members = enum_type.members();
  members.reserve(3);

  for(unsigned int i = 0; i < 3; ++i)
  {
    c_enum_typet::c_enum_membert member;
    member.set_identifier("V" + std::to_string(i));
    member.set_base_name("V" + std::to_string(i));
    member.set_value(integer2bvrep(i, underlying_type.get_width()));
    members.push_back(member);
  }
  return enum_type;
}

/// Create a type symbol and a type_tag and populate with the symbol_table in
/// with the symbol.
static tag_typet
create_tag_populate_env(const typet &type, symbol_tablet &symbol_table)
{
  const type_symbolt type_symbol{"my_type_symbol", type, ID_C};
  symbol_table.insert(type_symbol);

  if(can_cast_type<c_enum_typet>(type))
  {
    return c_enum_tag_typet{type_symbol.name};
  }
  else if(can_cast_type<struct_typet>(type))
  {
    return struct_tag_typet{type_symbol.name};
  }
  else if(can_cast_type<union_typet>(type))
  {
    return union_tag_typet{type_symbol.name};
  }
  UNREACHABLE;
}

exprt replicate_expression(
  const exprt &expr,
  const typet &output_type,
  std::size_t times)
{
  if(times == 1)
  {
    return expr;
  }
  exprt::operandst operands;
  operands.push_back(expr);
  for(std::size_t i = 1; i < times; ++i)
  {
    operands.push_back(
      shl_exprt{expr, from_integer(config.ansi_c.char_width * i, size_type())});
  }
  return multi_ary_exprt{ID_bitor, operands, output_type};
}

TEST_CASE(
  "duplicate_per_byte precondition works",
  "[core][util][duplicate_per_byte]")
{
  auto test = expr_initializer_test_environmentt::make();
  typet input_type = signedbv_typet{8};

  SECTION("duplicate_per_byte fails when init type is not a bitvector")
  {
    const array_typet array_type{
      bool_typet{}, from_integer(3, signedbv_typet{8})};

    const cbmc_invariants_should_throwt invariants_throw;

    REQUIRE_THROWS_MATCHES(
      duplicate_per_byte(
        array_of_exprt{true_exprt{}, array_type}, input_type, test.ns),
      invariant_failedt,
      invariant_failure_containing(
        "Condition: (init_type_as_bitvector && "
        "init_type_as_bitvector->get_width() <= config.ansi_c.char_width) || "
        "init_byte_expr.type().id() == ID_bool"));
  }

  SECTION(
    "duplicate_per_byte fails when init type is a bitvector larger than "
    "char_width bits")
  {
    const cbmc_invariants_should_throwt invariants_throw;

    REQUIRE_THROWS_MATCHES(
      duplicate_per_byte(
        from_integer(0, unsignedbv_typet{10}), input_type, test.ns),
      invariant_failedt,
      invariant_failure_containing(
        "init_type_as_bitvector->get_width() <= config.ansi_c.char_width"));
  }
}

std::string to_hex(unsigned int value)
{
  std::stringstream ss;
  ss << "0x" << std::hex << value;
  return ss.str();
}

TEST_CASE(
  "duplicate_per_byte on bitvector types with constant",
  "[core][util][duplicate_per_byte]")
{
  auto test = expr_initializer_test_environmentt::make();
  // values: init_expr_value, init_expr_size, output_expected_value, output_size
  using rowt = std::tuple<std::size_t, unsigned int, std::size_t, unsigned int>;
  unsigned int init_expr_value, output_expected_value;
  std::size_t output_size, init_expr_size;
  std::tie(
    init_expr_value, init_expr_size, output_expected_value, output_size) =
    GENERATE(
      rowt{0xFF, 8, 0xFF, 8},      // same-type constant
      rowt{0x2, 2, 0x02, 8},       // smaller-type constant gets promoted
      rowt{0x11, 5, 0x11, 5},      // same-type constant
      rowt{0x21, 8, 0x01, 5},      // bigger-type constant gets truncated
      rowt{0x2, 3, 0x02, 5},       // smaller-type constant gets promoted
      rowt{0xAB, 8, 0xABAB, 16},   // smaller-type constant gets replicated
      rowt{0xAB, 8, 0xBABAB, 20}); // smaller-type constant gets replicated
  SECTION(
    "Testing with init value " + to_hex(init_expr_value) + " of size " +
    std::to_string(init_expr_size))
  {
    SECTION("filling unsignedbv of size " + std::to_string(output_size))
    {
      typet output_type = unsignedbv_typet{output_size};
      const auto result = duplicate_per_byte(
        from_integer(init_expr_value, unsignedbv_typet{init_expr_size}),
        output_type,
        test.ns);
      const auto expected =
        from_integer(output_expected_value, unsignedbv_typet{output_size});
      REQUIRE(result == expected);

      // Check that signed-bv values are replicated including the sign bit.
      const auto result_with_signed_init_type = duplicate_per_byte(
        from_integer(init_expr_value, signedbv_typet{init_expr_size}),
        output_type,
        test.ns);
      REQUIRE(result_with_signed_init_type == result);
    }

    SECTION("filling signedbv of size " + std::to_string(output_size))
    {
      typet output_type = signedbv_typet{output_size};
      const auto result = duplicate_per_byte(
        from_integer(init_expr_value, unsignedbv_typet{init_expr_size}),
        output_type,
        test.ns);
      const auto expected =
        from_integer(output_expected_value, signedbv_typet{output_size});
      REQUIRE(result == expected);

      // Check that signed-bv values are replicated including the sign bit.
      const auto result_with_signed_init_type = duplicate_per_byte(
        from_integer(init_expr_value, signedbv_typet{init_expr_size}),
        output_type,
        test.ns);
      REQUIRE(result_with_signed_init_type == result);
    }

    SECTION("filling pointer of size " + std::to_string(output_size))
    {
      // Check that replicating a pointer_value is same as unsigned_bv.
      const pointer_typet output_type{bool_typet{}, output_size};
      const auto result = duplicate_per_byte(
        from_integer(init_expr_value, signedbv_typet{init_expr_size}),
        output_type,
        test.ns);
      auto expected =
        from_integer(output_expected_value, unsignedbv_typet{output_size});
      // Forcing the type to be pointer_typet otherwise from_integer fails when
      // the init value is not 0 (NULL).
      expected.type() = output_type;
      REQUIRE(result == expected);
    }

    SECTION("filling float")
    {
      // Check that replicating to a float_value is same as unsigned_bv.
      const auto result = duplicate_per_byte(
        from_integer(init_expr_value, unsignedbv_typet{init_expr_size}),
        float_type(),
        test.ns);
      const auto expected_unsigned_value =
        expr_try_dynamic_cast<constant_exprt>(duplicate_per_byte(
          from_integer(init_expr_value, unsignedbv_typet{init_expr_size}),
          unsignedbv_typet{float_type().get_width()},
          test.ns));
      REQUIRE(expected_unsigned_value);
      const auto expected =
        constant_exprt{expected_unsigned_value->get_value(), float_type()};
      REQUIRE(result == expected);
    }
  }
}

TEST_CASE(
  "duplicate_per_byte calls simplify",
  "[core][util][duplicate_per_byte]")
{
  auto test = expr_initializer_test_environmentt::make();
  // elements are init_expr, expected_value
  using rowt = std::tuple<exprt, std::size_t>;
  exprt init_expr;
  std::size_t expected_value;
  std::tie(init_expr, expected_value) = GENERATE(
    rowt{
      from_integer(0xAB, char_type()), 0xABAB}, // char type, no simplification
    rowt{
      typecast_exprt::conditional_cast(
        from_integer(0xAAB, unsignedbv_typet{24}), char_type()),
      0xABAB}, // cast to smaller type (truncating
    rowt{
      typecast_exprt::conditional_cast(
        from_integer(0xA, unsignedbv_typet{4}), unsignedbv_typet(8)),
      0x0A0A}, // cast to bigger type (zero-extended)
    rowt{
      plus_exprt{
        from_integer(0x0B, char_type()), from_integer(0xA0, char_type())},
      0xABAB}, // arithmetic operation on char type
    rowt{
      typecast_exprt::conditional_cast(
        plus_exprt{
          from_integer(0x0B, unsignedbv_typet{24}),
          from_integer(0xAA0, unsignedbv_typet(24))},
        char_type()),
      0xABAB}); // arithmetic operation with narrowing cast to char type

  SECTION("Testing with expression")
  {
    const auto output_type = unsignedbv_typet{config.ansi_c.char_width * 2};

    const auto result = duplicate_per_byte(init_expr, output_type, test.ns);

    const auto expected = from_integer(expected_value, output_type);

    REQUIRE(result == expected);
  }
}

TEST_CASE(
  "duplicate_per_byte on unsigned_bv with non-constant expr",
  "[core][util][duplicate_per_byte]")
{
  auto test = expr_initializer_test_environmentt::make();
  // elements are init_expr_size, output_size, replication_count
  using rowt = std::tuple<std::size_t, std::size_t, std::size_t>;
  std::size_t init_expr_size, output_size, replication_count;
  std::tie(init_expr_size, output_size, replication_count) = GENERATE(
    rowt{8, 8, 1},   // same-type expr no-cast
    rowt{2, 2, 1},   // same-type expr no-cast
    rowt{3, 8, 1},   // smaller-type gets promoted
    rowt{8, 2, 1},   // bigger type gets truncated
    rowt{8, 16, 2},  // replicated twice
    rowt{8, 20, 3}); // replicated three times and truncated
  SECTION("Testing with init size " + std::to_string(init_expr_size))
  {
    const auto init_expr = plus_exprt{
      symbol_exprt{"a_symbol", unsignedbv_typet{init_expr_size}},
      from_integer(2, unsignedbv_typet{init_expr_size})};
    SECTION("filling signedbv of size " + std::to_string(output_size))
    {
      typet output_type = signedbv_typet{output_size};

      const auto result = duplicate_per_byte(init_expr, output_type, test.ns);

      const auto operation_type = unsignedbv_typet{output_size};
      const auto casted_init_expr = typecast_exprt::conditional_cast(
        typecast_exprt::conditional_cast(
          init_expr, unsignedbv_typet{init_expr_size}),
        operation_type);
      const auto expected = typecast_exprt::conditional_cast(
        replicate_expression(
          casted_init_expr, operation_type, replication_count),
        output_type);

      REQUIRE(result == expected);
    }

    SECTION("filling unsignedbv of size " + std::to_string(output_size))
    {
      typet output_type = unsignedbv_typet{output_size};
      const auto result = duplicate_per_byte(init_expr, output_type, test.ns);

      const auto casted_init_expr =
        typecast_exprt::conditional_cast(init_expr, output_type);
      const auto expected =
        replicate_expression(casted_init_expr, output_type, replication_count);

      REQUIRE(result == expected);
    }

    SECTION("filling pointer of size " + std::to_string(output_size))
    {
      // Check that replicating a pointer_value is same as unsigned_bv modulo a
      // byte_extract outside.
      const pointer_typet output_type{bool_typet{}, output_size};
      const auto result = duplicate_per_byte(init_expr, output_type, test.ns);
      const auto unsigned_corr_type = unsignedbv_typet{output_size};
      const auto unsigned_init_expr =
        typecast_exprt::conditional_cast(init_expr, unsigned_corr_type);
      const auto expected = make_byte_extract(
        replicate_expression(
          unsigned_init_expr, unsigned_corr_type, replication_count),
        from_integer(0, char_type()),
        output_type);

      REQUIRE(result == expected);
    }

    SECTION("filling float")
    {
      // Check that replicating a float is same as unsigned_bv modulo a
      // byte_extract outside.
      // We ignore the output size and replication_count passed above as float
      // size is constant
      const std::size_t float_replication_count =
        (float_type().get_width() + config.ansi_c.char_width - 1) /
        config.ansi_c.char_width;
      const auto result = duplicate_per_byte(init_expr, float_type(), test.ns);
      const auto unsigned_corr_type =
        unsignedbv_typet{float_type().get_width()};
      const auto unsigned_init_expr =
        typecast_exprt::conditional_cast(init_expr, unsigned_corr_type);
      const auto expected = make_byte_extract(
        replicate_expression(
          unsigned_init_expr, unsigned_corr_type, float_replication_count),
        from_integer(0, char_type()),
        float_type());

      REQUIRE(result == expected);
    }
  }
}

TEST_CASE("expr_initializer boolean", "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  typet input = bool_typet{};
  SECTION("nondet_initializer")
  {
    const auto result = nondet_initializer(input, test.loc, test.ns);
    REQUIRE(result.has_value());
    const auto expected = side_effect_expr_nondett{bool_typet{}, test.loc};
    REQUIRE(result.value() == expected);
    const auto expr_result =
      expr_initializer(input, test.loc, test.ns, exprt(ID_nondet));
    REQUIRE(expr_result == result);
  }
  SECTION("zero_initializer")
  {
    const auto result = zero_initializer(input, test.loc, test.ns);
    REQUIRE(result.has_value());
    const auto expected = from_integer(0, bool_typet());
    REQUIRE(result.value() == expected);
    const auto expr_result = expr_initializer(
      input, test.loc, test.ns, constant_exprt(ID_0, char_type()));
    REQUIRE(expr_result == result);
  }
  SECTION("expr_initializer with same-type constant")
  {
    const auto result =
      expr_initializer(input, test.loc, test.ns, true_exprt{});
    REQUIRE(result.has_value());
    const auto expected = true_exprt{};
    REQUIRE(result.value() == expected);
  }
  SECTION("expr_initializer with other-type constant")
  {
    const auto result = expr_initializer(
      input, test.loc, test.ns, from_integer(1, signedbv_typet{8}));
    REQUIRE(result.has_value());
    const auto expected =
      typecast_exprt{from_integer(1, signedbv_typet{8}), bool_typet{}};
    REQUIRE(result.value() == expected);
  }
  SECTION("expr_initializer with non-constant expr")
  {
    const auto result = expr_initializer(
      input, test.loc, test.ns, or_exprt{true_exprt(), true_exprt{}});
    REQUIRE(result.has_value());
    const auto expected = or_exprt{true_exprt{}, true_exprt{}};
    REQUIRE(result.value() == expected);
  }
}

TEST_CASE(
  "expr_initializer on variable-bit unsigned_bv",
  "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  const std::size_t input_type_size = GENERATE(3, 8, 16, 20);
  SECTION(
    "Testing with expected type as unsigned_bv of size " +
    std::to_string(input_type_size))
  {
    typet input_type = unsignedbv_typet{input_type_size};
    SECTION("nondet_initializer works")
    {
      const auto result = nondet_initializer(input_type, test.loc, test.ns);
      REQUIRE(result.has_value());
      const auto expected =
        side_effect_expr_nondett{unsignedbv_typet{input_type_size}, test.loc};
      REQUIRE(result.value() == expected);
      const auto expr_result =
        expr_initializer(input_type, test.loc, test.ns, exprt(ID_nondet));
      REQUIRE(expr_result == result);
    }
    SECTION("zero_initializer works")
    {
      const auto result = zero_initializer(input_type, test.loc, test.ns);
      REQUIRE(result.has_value());
      const auto expected = from_integer(0, unsignedbv_typet{input_type_size});
      REQUIRE(result.value() == expected);
      const auto expr_result = expr_initializer(
        input_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
      REQUIRE(expr_result == result);
    }
    SECTION("expr_initializer calls duplicate_per_byte")
    {
      const exprt init_value =
        from_integer(0x0A, unsignedbv_typet{config.ansi_c.char_width});
      const auto result =
        expr_initializer(input_type, test.loc, test.ns, init_value);
      REQUIRE(result.has_value());
      const auto expected = duplicate_per_byte(
        init_value, unsignedbv_typet{input_type_size}, test.ns);
      REQUIRE(result.value() == expected);
    }
  }
}

TEST_CASE(
  "expr_initializer on variable-bit pointer type",
  "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  const std::size_t input_type_size = GENERATE(3, 8, 16, 20);
  SECTION(
    "Testing with expected type as unsigned_bv of size " +
    std::to_string(input_type_size))
  {
    typet input_type = pointer_typet{bool_typet{}, input_type_size};
    SECTION("nondet_initializer works")
    {
      const auto result = nondet_initializer(input_type, test.loc, test.ns);
      REQUIRE(result.has_value());
      const auto expected = side_effect_expr_nondett{
        pointer_typet{bool_typet{}, input_type_size}, test.loc};
      REQUIRE(result.value() == expected);
      const auto expr_result =
        expr_initializer(input_type, test.loc, test.ns, exprt(ID_nondet));
      REQUIRE(expr_result == result);
    }
    SECTION("zero_initializer works")
    {
      const auto result = zero_initializer(input_type, test.loc, test.ns);
      REQUIRE(result.has_value());
      auto expected =
        from_integer(0, pointer_typet{bool_typet{}, input_type_size});
      REQUIRE(result.value() == expected);
      const auto expr_result = expr_initializer(
        input_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
      REQUIRE(expr_result == result);
    }
    SECTION("expr_initializer calls duplicate_per_byte")
    {
      const exprt init_value =
        from_integer(0x0A, unsignedbv_typet{config.ansi_c.char_width});
      const auto result =
        expr_initializer(input_type, test.loc, test.ns, init_value);
      REQUIRE(result.has_value());
      const auto expected = duplicate_per_byte(
        init_value, pointer_typet{bool_typet{}, input_type_size}, test.ns);
      REQUIRE(result.value() == expected);
    }
  }
}

TEST_CASE("expr_initializer on float type", "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  SECTION("Testing with expected type as float")
  {
    const typet input_type = float_type();
    SECTION("nondet_initializer works")
    {
      const auto result = nondet_initializer(input_type, test.loc, test.ns);
      REQUIRE(result.has_value());
      const auto expected = side_effect_expr_nondett{float_type(), test.loc};
      REQUIRE(result.value() == expected);
      const auto expr_result =
        expr_initializer(input_type, test.loc, test.ns, exprt(ID_nondet));
      REQUIRE(expr_result == result);
    }
    SECTION("zero_initializer works")
    {
      const auto result = zero_initializer(input_type, test.loc, test.ns);
      REQUIRE(result.has_value());
      auto expected = from_integer(0, float_type());
      REQUIRE(result.value() == expected);
      const auto expr_result = expr_initializer(
        input_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
      REQUIRE(expr_result == result);
    }
    SECTION("expr_initializer calls duplicate_per_byte")
    {
      const exprt init_value =
        from_integer(0x0A, unsignedbv_typet{config.ansi_c.char_width});
      const auto result =
        expr_initializer(input_type, test.loc, test.ns, init_value);
      REQUIRE(result.has_value());
      const auto expected =
        duplicate_per_byte(init_value, float_type(), test.ns);
      REQUIRE(result.value() == expected);
    }
  }
}

TEST_CASE(
  "expr_initializer on c_enum and c_enum_tag",
  "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  const unsignedbv_typet enum_underlying_type{8};
  const auto enum_type = make_c_enum_type(enum_underlying_type);
  // Repeat with the c_enum_tag_typet instead of the c_enum_typet it points to
  const auto c_enum_tag_type =
    create_tag_populate_env(enum_type, test.symbol_table);
  SECTION("nondet_initializer works")
  {
    const auto result = nondet_initializer(enum_type, test.loc, test.ns);
    const auto expected = side_effect_expr_nondett{enum_type, test.loc};
    REQUIRE(result.has_value());
    REQUIRE(result.value() == expected);
    const auto expr_result =
      expr_initializer(enum_type, test.loc, test.ns, exprt(ID_nondet));
    REQUIRE(expr_result == result);

    const auto tag_result =
      nondet_initializer(c_enum_tag_type, test.loc, test.ns);
    const auto tag_expected =
      side_effect_expr_nondett{c_enum_tag_type, test.loc};
    REQUIRE(tag_result.has_value());
    REQUIRE(tag_result.value() == tag_expected);
    const auto tag_expr_result =
      expr_initializer(c_enum_tag_type, test.loc, test.ns, exprt(ID_nondet));
    REQUIRE(tag_expr_result == tag_result);
  }

  SECTION("zero_initializer works")
  {
    const auto result = zero_initializer(enum_type, test.loc, test.ns);
    const auto expected = from_integer(0, enum_type);
    REQUIRE(result.has_value());
    REQUIRE(result.value() == expected);
    const auto expr_result = expr_initializer(
      enum_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
    REQUIRE(expr_result == result);

    const auto tag_result =
      zero_initializer(c_enum_tag_type, test.loc, test.ns);
    auto tag_expected = from_integer(0, enum_type);
    tag_expected.type() = c_enum_tag_type;
    REQUIRE(tag_result.has_value());
    REQUIRE(tag_result.value() == tag_expected);
    const auto tag_expr_result = expr_initializer(
      c_enum_tag_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
    REQUIRE(tag_expr_result == tag_result);
  }
  SECTION("expr_initializer calls duplicate_per_byte")
  {
    const exprt init_value =
      from_integer(0xAB, signedbv_typet{config.ansi_c.char_width});
    const auto result =
      expr_initializer(enum_type, test.loc, test.ns, init_value);
    const auto expected = duplicate_per_byte(init_value, enum_type, test.ns);
    REQUIRE(result.has_value());
    REQUIRE(result.value() == expected);

    const auto tag_result =
      expr_initializer(c_enum_tag_type, test.loc, test.ns, init_value);
    auto tag_expected = duplicate_per_byte(init_value, enum_type, test.ns);
    tag_expected.type() = c_enum_tag_type;
    REQUIRE(tag_result.has_value());
    REQUIRE(tag_result.value() == tag_expected);
  }
}

TEST_CASE(
  "expr_initializer on fixed-size array of signed 8 bit elements",
  "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  typet inner_type = signedbv_typet{8};
  const std::size_t elem_count = 3;
  typet array_type =
    array_typet{inner_type, from_integer(elem_count, signedbv_typet{8})};

  SECTION("nodet_initializer works")
  {
    const auto result = nondet_initializer(array_type, test.loc, test.ns);
    REQUIRE(result.has_value());
    std::vector<exprt> array_values{
      elem_count, side_effect_expr_nondett{signedbv_typet{8}, test.loc}};
    const auto expected = array_exprt{
      array_values,
      array_typet{
        signedbv_typet{8}, from_integer(elem_count, signedbv_typet{8})}};
    REQUIRE(result.value() == expected);
    const auto expr_result =
      expr_initializer(array_type, test.loc, test.ns, exprt(ID_nondet));
    REQUIRE(expr_result == result);
  }

  SECTION("zero_initializer works")
  {
    const auto result = zero_initializer(array_type, test.loc, test.ns);
    REQUIRE(result.has_value());
    std::vector<exprt> array_values{elem_count, from_integer(0, inner_type)};
    const auto expected = array_exprt{
      array_values,
      array_typet{
        signedbv_typet{8}, from_integer(elem_count, signedbv_typet{8})}};
    REQUIRE(result.value() == expected);
    const auto expr_result = expr_initializer(
      array_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
    REQUIRE(expr_result == result);
  }

  SECTION("expr_initializer calls duplicate_per_byte")
  {
    const exprt init_value =
      from_integer(0xAB, signedbv_typet{config.ansi_c.char_width});
    const auto result =
      expr_initializer(array_type, test.loc, test.ns, init_value);
    REQUIRE(result.has_value());
    std::vector<exprt> array_values{
      elem_count, duplicate_per_byte(init_value, inner_type, test.ns)};
    const auto expected = array_exprt{
      array_values,
      array_typet{
        signedbv_typet{8}, from_integer(elem_count, signedbv_typet{8})}};
    REQUIRE(result.value() == expected);
  }
}

TEST_CASE(
  "expr_initializer on array of nondet size",
  "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  typet inner_type = signedbv_typet{8};
  typet array_type = array_typet{
    inner_type, side_effect_expr_nondett{signedbv_typet{8}, test.loc}};

  SECTION("nondet_initializer works")
  {
    const auto result = nondet_initializer(array_type, test.loc, test.ns);
    REQUIRE(result.has_value());
    const auto expected = side_effect_expr_nondett{
      array_typet{
        inner_type, side_effect_expr_nondett{signedbv_typet{8}, test.loc}},
      test.loc};
    REQUIRE(result.value() == expected);
    const auto expr_result =
      expr_initializer(array_type, test.loc, test.ns, exprt(ID_nondet));
    REQUIRE(expr_result == result);
  }

  SECTION("zero_initializer works")
  {
    const auto result = zero_initializer(array_type, test.loc, test.ns);
    REQUIRE(result.has_value());
    const auto expected = array_of_exprt{
      from_integer(0, inner_type),
      array_typet{
        inner_type, side_effect_expr_nondett{signedbv_typet{8}, test.loc}}};
    REQUIRE(result.value() == expected);
    const auto expr_result = expr_initializer(
      array_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
    REQUIRE(expr_result == result);
  }

  SECTION("expr_initializer calls duplicate_per_byte")
  {
    const exprt init_value =
      from_integer(0xAB, signedbv_typet{config.ansi_c.char_width});
    const auto result =
      expr_initializer(array_type, test.loc, test.ns, init_value);
    REQUIRE(result.has_value());
    const auto expected = array_of_exprt{
      duplicate_per_byte(init_value, inner_type, test.ns),
      array_typet{
        inner_type, side_effect_expr_nondett{signedbv_typet{8}, test.loc}}};
    REQUIRE(result.value() == expected);
  }
}

TEST_CASE(
  "expr_initializer on fixed-size array of fixed-size arrays",
  "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  typet inner_type = signedbv_typet{8};
  const std::size_t elem_count = 3;
  typet inner_array_type =
    array_typet{inner_type, from_integer(elem_count, signedbv_typet{8})};
  typet array_type =
    array_typet{inner_array_type, from_integer(elem_count, signedbv_typet{8})};

  SECTION("nondet_initializer works")
  {
    const auto result = nondet_initializer(array_type, test.loc, test.ns);
    REQUIRE(result.has_value());
    std::vector<exprt> inner_array_values{
      elem_count, side_effect_expr_nondett{signedbv_typet{8}, test.loc}};
    const auto inner_expected = array_exprt{
      inner_array_values,
      array_typet{
        signedbv_typet{8}, from_integer(elem_count, signedbv_typet{8})}};
    std::vector<exprt> array_values{elem_count, inner_expected};
    const auto expected = array_exprt{
      array_values,
      array_typet{
        array_typet{
          signedbv_typet{8}, from_integer(elem_count, signedbv_typet{8})},
        from_integer(elem_count, signedbv_typet{8})}};
    REQUIRE(result.value() == expected);
    const auto expr_result =
      expr_initializer(array_type, test.loc, test.ns, exprt(ID_nondet));
    REQUIRE(expr_result == result);
  }

  SECTION("zero_initializer works")
  {
    const auto result = zero_initializer(array_type, test.loc, test.ns);
    REQUIRE(result.has_value());
    std::vector<exprt> inner_array_values{
      elem_count, from_integer(0, inner_type)};
    const auto inner_expected = array_exprt{
      inner_array_values,
      array_typet{
        signedbv_typet{8}, from_integer(elem_count, signedbv_typet{8})}};
    std::vector<exprt> array_values{elem_count, inner_expected};
    const auto expected = array_exprt{
      array_values,
      array_typet{
        array_typet{
          signedbv_typet{8}, from_integer(elem_count, signedbv_typet{8})},
        from_integer(elem_count, signedbv_typet{8})}};
    REQUIRE(result.value() == expected);
    const auto expr_result = expr_initializer(
      array_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
    REQUIRE(expr_result == result);
  }
  SECTION("expr_initializer calls duplicate_per_byte")
  {
    const exprt init_value =
      from_integer(0xAB, signedbv_typet{config.ansi_c.char_width});
    const auto result =
      expr_initializer(array_type, test.loc, test.ns, init_value);
    REQUIRE(result.has_value());
    std::vector<exprt> inner_array_values{
      elem_count, duplicate_per_byte(init_value, inner_type, test.ns)};
    const auto inner_expected = array_exprt{
      inner_array_values,
      array_typet{
        signedbv_typet{8}, from_integer(elem_count, signedbv_typet{8})}};
    std::vector<exprt> array_values{elem_count, inner_expected};
    const auto expected = array_exprt{
      array_values,
      array_typet{
        array_typet{
          signedbv_typet{8}, from_integer(elem_count, signedbv_typet{8})},
        from_integer(elem_count, signedbv_typet{8})}};
    REQUIRE(result.value() == expected);
  }
}

TEST_CASE(
  "expr_initializer on nested struct type",
  "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  const struct_union_typet::componentst sub_struct_components{
    {"foo", signedbv_typet{32}}, {"bar", unsignedbv_typet{16}}};
  const struct_typet inner_struct_type{sub_struct_components};
  const struct_union_typet::componentst struct_components{
    {"fizz", bool_typet{}}, {"bar", inner_struct_type}};
  const struct_typet struct_type{struct_components};
  SECTION("nondet_initializer works")
  {
    const auto result = nondet_initializer(struct_type, test.loc, test.ns);
    REQUIRE(result.has_value());
    const exprt::operandst expected_inner_struct_fields{
      side_effect_expr_nondett{signedbv_typet{32}, test.loc},
      side_effect_expr_nondett{unsignedbv_typet{16}, test.loc}};
    const struct_exprt expected_inner_struct_expr{
      expected_inner_struct_fields, inner_struct_type};
    const exprt::operandst expected_struct_fields{
      side_effect_expr_nondett{bool_typet{}, test.loc},
      expected_inner_struct_expr};
    const struct_exprt expected_struct_expr{
      expected_struct_fields, struct_type};
    REQUIRE(result.value() == expected_struct_expr);
    const auto expr_result =
      expr_initializer(struct_type, test.loc, test.ns, exprt(ID_nondet));
    REQUIRE(expr_result == result);

    const auto struct_tag_type =
      create_tag_populate_env(struct_type, test.symbol_table);
    const auto tag_result =
      nondet_initializer(struct_tag_type, test.loc, test.ns);
    REQUIRE(tag_result.has_value());
    const struct_exprt expected_struct_tag_expr{
      expected_struct_fields, struct_tag_type};
    REQUIRE(tag_result.value() == expected_struct_tag_expr);
    const auto tag_expr_result =
      expr_initializer(struct_tag_type, test.loc, test.ns, exprt(ID_nondet));
    REQUIRE(tag_expr_result == tag_result);
  }

  SECTION("zero_initializer works")
  {
    const auto result = zero_initializer(struct_type, test.loc, test.ns);
    REQUIRE(result.has_value());
    const exprt::operandst expected_inner_struct_fields{
      from_integer(0, signedbv_typet{32}),
      from_integer(0, unsignedbv_typet{16})};
    const struct_exprt expected_inner_struct_expr{
      expected_inner_struct_fields, inner_struct_type};
    const exprt::operandst expected_struct_fields{
      from_integer(0, bool_typet{}), expected_inner_struct_expr};
    const struct_exprt expected_struct_expr{
      expected_struct_fields, struct_type};
    REQUIRE(result.value() == expected_struct_expr);
    const auto expr_result = expr_initializer(
      struct_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
    REQUIRE(expr_result == result);

    const auto struct_tag_type =
      create_tag_populate_env(struct_type, test.symbol_table);
    const auto tag_result =
      zero_initializer(struct_tag_type, test.loc, test.ns);
    REQUIRE(tag_result.has_value());
    const struct_exprt expected_struct_tag_expr{
      expected_struct_fields, struct_tag_type};
    REQUIRE(tag_result.value() == expected_struct_tag_expr);
    const auto tag_expr_result = expr_initializer(
      struct_tag_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
    REQUIRE(tag_expr_result == tag_result);
  }
  SECTION("expr_initializer calls duplicate_per_byte")
  {
    const exprt init_value =
      from_integer(0xAB, signedbv_typet{config.ansi_c.char_width});
    const auto result =
      expr_initializer(struct_type, test.loc, test.ns, init_value);
    REQUIRE(result.has_value());
    const exprt::operandst expected_inner_struct_fields{
      duplicate_per_byte(init_value, signedbv_typet{32}, test.ns),
      duplicate_per_byte(init_value, unsignedbv_typet{16}, test.ns)};
    const struct_exprt expected_inner_struct_expr{
      expected_inner_struct_fields, inner_struct_type};
    const exprt::operandst expected_struct_fields{
      duplicate_per_byte(init_value, bool_typet{}, test.ns),
      expected_inner_struct_expr};
    const struct_exprt expected_struct_expr{
      expected_struct_fields, struct_type};
    REQUIRE(result.value() == expected_struct_expr);

    const auto struct_tag_type =
      create_tag_populate_env(struct_type, test.symbol_table);
    const auto tag_result =
      expr_initializer(struct_tag_type, test.loc, test.ns, init_value);
    REQUIRE(tag_result.has_value());
    const struct_exprt expected_struct_tag_expr{
      expected_struct_fields, struct_tag_type};
    REQUIRE(tag_result.value() == expected_struct_tag_expr);
  }
}

TEST_CASE("expr_initializer on union type", "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  const struct_union_typet::componentst inner_struct_components{
    {"foo", signedbv_typet{32}}, {"bar", unsignedbv_typet{16}}};
  const struct_typet inner_struct_type{inner_struct_components};
  const struct_union_typet::componentst union_components{
    {"foo", signedbv_typet{256}},
    {"bar", unsignedbv_typet{16}},
    {"fizz", bool_typet{}},
    {"array",
     array_typet{signedbv_typet{8}, from_integer(8, signedbv_typet{8})}},
    {"struct", inner_struct_type}};
  const union_typet union_type{union_components};

  SECTION("nondet_initializer works")
  {
    const auto result = nondet_initializer(union_type, test.loc, test.ns);
    REQUIRE(result.has_value());
    const union_exprt expected_union{
      "foo",
      side_effect_expr_nondett{signedbv_typet{256}, test.loc},
      union_type};
    REQUIRE(result.value() == expected_union);

    const auto union_tag_type =
      create_tag_populate_env(union_type, test.symbol_table);
    const auto tag_result =
      nondet_initializer(union_tag_type, test.loc, test.ns);
    REQUIRE(tag_result.has_value());
    const union_exprt expected_union_tag{
      "foo",
      side_effect_expr_nondett{signedbv_typet{256}, test.loc},
      union_tag_type};
    REQUIRE(tag_result.value() == expected_union_tag);
  }

  SECTION("zero_initializer works")
  {
    const auto result = zero_initializer(union_type, test.loc, test.ns);
    REQUIRE(result.has_value());
    const union_exprt expected_union{
      "foo", from_integer(0, signedbv_typet{256}), union_type};
    REQUIRE(result.value() == expected_union);
    const auto expr_result = expr_initializer(
      union_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
    REQUIRE(expr_result == result);

    const auto union_tag_type =
      create_tag_populate_env(union_type, test.symbol_table);
    const auto tag_result = zero_initializer(union_tag_type, test.loc, test.ns);
    REQUIRE(tag_result.has_value());
    const union_exprt expected_union_tag{
      "foo", from_integer(0, signedbv_typet{256}), union_tag_type};
    REQUIRE(tag_result.value() == expected_union_tag);
    const auto tag_expr_result = expr_initializer(
      union_tag_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
    REQUIRE(*tag_expr_result == *tag_result);
  }
  SECTION("expr_initializer calls duplicate_per_byte")
  {
    const exprt init_value =
      from_integer(0xAB, signedbv_typet{config.ansi_c.char_width});
    const auto result =
      expr_initializer(union_type, test.loc, test.ns, init_value);
    REQUIRE(result.has_value());
    const union_exprt expected_union{
      "foo",
      duplicate_per_byte(init_value, signedbv_typet{256}, test.ns),
      union_type};
    REQUIRE(result.value() == expected_union);

    const auto union_tag_type =
      create_tag_populate_env(union_type, test.symbol_table);
    const auto tag_result =
      expr_initializer(union_tag_type, test.loc, test.ns, init_value);
    REQUIRE(tag_result.has_value());
    const union_exprt expected_union_tag{
      "foo",
      duplicate_per_byte(init_value, signedbv_typet{256}, test.ns),
      union_tag_type};
    REQUIRE(tag_result.value() == expected_union_tag);
  }
}

TEST_CASE(
  "expr_initializer on union type with nondet sized array (fails)",
  "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  const struct_union_typet::componentst union_components{
    {"foo", signedbv_typet{256}},
    {"array",
     array_typet{
       signedbv_typet{8},
       side_effect_expr_nondett{signedbv_typet{8}, test.loc}}}};
  const union_typet union_type{union_components};

  SECTION("nondet_initializer fails correctly")
  {
    const auto result = nondet_initializer(union_type, test.loc, test.ns);
    REQUIRE_FALSE(result.has_value());
    const auto expr_result =
      expr_initializer(union_type, test.loc, test.ns, exprt(ID_nondet));
    REQUIRE(expr_result == result);
  }

  SECTION("zero_initializer works")
  {
    const auto result = zero_initializer(union_type, test.loc, test.ns);
    REQUIRE_FALSE(result.has_value());
    const auto expr_result = expr_initializer(
      union_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
    REQUIRE(expr_result == result);
  }
  SECTION("expr_initializer calls duplicate_per_byte")
  {
    const exprt init_value =
      from_integer(0xAB, signedbv_typet{config.ansi_c.char_width});
    const auto result =
      expr_initializer(union_type, test.loc, test.ns, init_value);
    REQUIRE_FALSE(result.has_value());
  }
}

TEST_CASE("expr_initializer on string type", "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  const string_typet string_type{};

  SECTION("nondet_initializer works")
  {
    const auto result = nondet_initializer(string_type, test.loc, test.ns);
    REQUIRE(result.has_value());
    const side_effect_expr_nondett expected_string{string_typet{}, test.loc};
    REQUIRE(result.value() == expected_string);
    const auto expr_result =
      expr_initializer(string_type, test.loc, test.ns, exprt(ID_nondet));
    REQUIRE(expr_result == result);
  }

  SECTION("zero_initializer works")
  {
    const auto result = zero_initializer(string_type, test.loc, test.ns);
    REQUIRE(result.has_value());
    const auto expected_string = constant_exprt{irep_idt(), string_typet{}};
    REQUIRE(result.value() == expected_string);
    const auto expr_result = expr_initializer(
      string_type, test.loc, test.ns, constant_exprt(ID_0, char_type()));
    REQUIRE(expr_result == result);
  }
  SECTION("expr_initializer calls duplicate_per_byte")
  {
    const exprt init_value =
      from_integer(0xAB, signedbv_typet{config.ansi_c.char_width});
    const auto result =
      expr_initializer(string_type, test.loc, test.ns, init_value);
    REQUIRE(result.has_value());
    const auto expected_string =
      duplicate_per_byte(init_value, string_type, test.ns);
    REQUIRE(result.value() == expected_string);
  }
}
