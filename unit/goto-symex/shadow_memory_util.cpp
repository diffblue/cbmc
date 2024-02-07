// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/pointer_expr.h>
#include <util/string_constant.h>

#include <goto-symex/shadow_memory_util.h>
#include <testing-utils/invariant.h>

#include <array>

/// Helper struct to hold useful test components.
struct shadow_memory_util_test_environmentt
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  source_locationt loc{};
  null_message_handlert null_message_handler{};
  messaget log{null_message_handler};

  static shadow_memory_util_test_environmentt make()
  {
    // These config lines are necessary before construction because char size
    // depend on the global configuration.
    config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
    config.ansi_c.set_arch_spec_x86_64();
    return {};
  }

private:
  shadow_memory_util_test_environmentt() = default;
};

TEST_CASE("extract_field_name works", "[core][goto-symex][extract_field_name]")
{
  SECTION("with string_constantt")
  {
    const std::string name = "field_name";
    const string_constantt string_constant{name};
    irep_idt field_name = extract_field_name(string_constant);
    REQUIRE(field_name == name);
  }
  SECTION("with typecast_exprt")
  {
    const std::string name = "field_name";
    const string_constantt string_constant{name};
    const typecast_exprt typecast_expr{string_constant, unsignedbv_typet{10}};
    irep_idt field_name = extract_field_name(typecast_expr);
    REQUIRE(field_name == name);
  }
  SECTION("with address_of_exprt")
  {
    const std::string name = "address_of_name";
    const string_constantt string_constant{name};
    const address_of_exprt address_of_expr{string_constant};
    irep_idt field_name = extract_field_name(address_of_expr);
    REQUIRE(field_name == name);
  }
  SECTION("with index_exprt")
  {
    const std::string name = "array_name";
    const string_constantt string_constant{name};
    const index_exprt index_expr{string_constant, false_exprt{}};
    irep_idt field_name = extract_field_name(index_expr);
    REQUIRE(field_name == name);
  }
}

TEST_CASE(
  "extract_field_name correctly fails",
  "[core][goto-symex][extract_field_name]")
{
  const exprt unsignedbv_expr = from_integer(42, unsignedbv_typet{10});

  const cbmc_invariants_should_throwt invariants_throw;

  SECTION("with simple non string_constantt")
  {
    REQUIRE_THROWS_MATCHES(
      extract_field_name(unsignedbv_expr),
      invariant_failedt,
      invariant_failure_containing(
        "Failed to extract shadow memory field name."));
  }
  SECTION("with typecast_exprt")
  {
    const typecast_exprt typecast_expr{unsignedbv_expr, unsignedbv_typet{10}};
    REQUIRE_THROWS_MATCHES(
      extract_field_name(typecast_expr),
      invariant_failedt,
      invariant_failure_containing(
        "Failed to extract shadow memory field name."));
  }
  SECTION("with address_of_exprt")
  {
    const address_of_exprt address_of_expr{unsignedbv_expr};

    REQUIRE_THROWS_MATCHES(
      extract_field_name(address_of_expr),
      invariant_failedt,
      invariant_failure_containing(
        "Failed to extract shadow memory field name."));
  }
  SECTION("with index_exprt")
  {
    const array_exprt array_expr{
      {unsignedbv_expr, unsignedbv_expr},
      array_typet{
        unsignedbv_expr.type(), from_integer(2, unsignedbv_typet{32})}};
    const index_exprt index_expr{array_expr, false_exprt{}};

    REQUIRE_THROWS_MATCHES(
      extract_field_name(index_expr),
      invariant_failedt,
      invariant_failure_containing(
        "Failed to extract shadow memory field name."));
  }
}

TEST_CASE("deref_expr works correctly", "[core][goto-symex][deref_expr]")
{
  exprt expr = from_integer(0, pointer_typet{bool_typet{}, 64});
  SECTION("with array_of_exprt")
  {
    const auto wrapped = address_of_exprt{expr};
    const auto dereferenced = deref_expr(wrapped);

    REQUIRE(dereferenced == expr);
  }

  SECTION("with generic exprt")
  {
    const auto dereference_expr = deref_expr(expr);
    const auto expected = dereference_exprt{expr};

    REQUIRE(dereference_expr == expected);
  }
}

std::size_t max(const std::array<mp_integer, 7> &values)
{
  return std::max(
    {values[0].to_long(),
     values[1].to_long(),
     values[2].to_long(),
     values[3].to_long(),
     values[4].to_long(),
     values[5].to_long(),
     values[6].to_long()});
}

TEST_CASE(
  "compute_max_over_bytes works correctly",
  "[core][goto-symex][compute_max_over_bytes]")
{
  auto test = shadow_memory_util_test_environmentt::make();
  const auto sm_type = unsigned_char_type();

  // Using mp_integer types otherwise on 32-bit machines n << 48 wraps around.
  std::array<mp_integer, 7> values = GENERATE(
    std::array<mp_integer, 7>{{0, 0, 0, 0, 0, 0, 0}},
    std::array<mp_integer, 7>{{1, 2, 3, 4, 5, 6, 7}},
    std::array<mp_integer, 7>{{2, 3, 4, 5, 6, 7, 1}},
    std::array<mp_integer, 7>{{3, 4, 5, 6, 7, 1, 2}},
    std::array<mp_integer, 7>{{4, 5, 6, 7, 1, 2, 3}},
    std::array<mp_integer, 7>{{5, 6, 7, 1, 2, 3, 4}},
    std::array<mp_integer, 7>{{6, 7, 1, 2, 3, 4, 5}},
    std::array<mp_integer, 7>{{7, 1, 2, 3, 4, 5, 6}},
    std::array<mp_integer, 7>{{8, 8, 8, 8, 8, 8, 8}});

  SECTION("test set " + std::to_string(values[0].to_long()))
  {
    SECTION("on bitvector")
    {
      const exprt bitvector = from_integer(
        values[0] + (values[1] << 8) + (values[2] << 16) + (values[3] << 24) +
          (values[4] << 32) + (values[5] << 40) + (values[6] << 48),
        unsignedbv_typet{56});

      const exprt max_over_struct =
        compute_max_over_bytes(bitvector, sm_type, test.ns);

      const exprt simplified = simplify_expr(max_over_struct, test.ns);

      REQUIRE(simplified == from_integer(max(values), sm_type));
    }
    SECTION("on array")
    {
      const array_typet array_type{
        unsigned_char_type(), from_integer(7, unsigned_long_int_type())};
      const array_exprt::operandst array_operands{
        from_integer(values[0], unsigned_char_type()),
        from_integer(values[1], unsigned_char_type()),
        from_integer(values[2], unsigned_char_type()),
        from_integer(values[3], unsigned_char_type()),
        from_integer(values[4], unsigned_char_type()),
        from_integer(values[5], unsigned_char_type()),
        from_integer(values[6], unsigned_char_type())};
      const array_exprt array_expr{array_operands, array_type};

      const exprt max_over_struct =
        compute_max_over_bytes(array_expr, sm_type, test.ns);

      const exprt simplified = simplify_expr(max_over_struct, test.ns);

      REQUIRE(simplified == from_integer(max(values), sm_type));
    }
    SECTION("on struct elements")
    {
      const struct_union_typet::componentst sub_struct_components{
        {"foo", signedbv_typet{32}}, {"bar", unsignedbv_typet{16}}};
      const struct_typet inner_struct_type{sub_struct_components};
      const struct_union_typet::componentst struct_components{
        {"fizz", char_type()}, {"bar", inner_struct_type}};
      const struct_typet struct_type{struct_components};
      const mp_integer foo =
        values[0] + (values[1] << 8) + (values[2] << 16) + (values[3] << 24);
      const mp_integer bar = values[4] + (values[5] << 8);
      const mp_integer fizz = values[6];
      const struct_exprt::operandst inner_operands{
        from_integer(foo, signedbv_typet{32}),
        from_integer(bar, unsignedbv_typet{16})};
      const struct_exprt inner_struct_expr{inner_operands, inner_struct_type};
      const struct_exprt::operandst struct_operands{
        from_integer(fizz, char_type()), inner_struct_expr};
      const struct_exprt struct_expr{struct_operands, struct_type};

      const exprt max_over_struct =
        compute_max_over_bytes(struct_expr, sm_type, test.ns);

      const exprt simplified = simplify_expr(max_over_struct, test.ns);

      REQUIRE(simplified == from_integer(max(values), sm_type));
    }
  }
}

bool compute_or(const std::array<mp_integer, 7> &values)
{
  return values[0].to_long() || values[1].to_long() || values[2].to_long() ||
         values[3].to_long() || values[4].to_long() || values[5].to_long() ||
         values[6].to_long();
}

// It seems that simplify_expr does not get rid of bitor_exprt, so we do it by
// ourselves
exprt simplify_bit_or_exprt(const exprt &expr)
{
  INVARIANT(
    can_cast_type<bool_typet>(expr.type()),
    "Or expression must be of bool type");
  if(can_cast_expr<constant_exprt>(expr))
  {
    return expr;
  }
  if(const auto *or_expr = expr_try_dynamic_cast<bitor_exprt>(expr))
  {
    bool res = false;
    for(const auto &operand : or_expr->operands())
    {
      const exprt reduced = simplify_bit_or_exprt(operand);
      res |= reduced.is_true();
    }
    return from_integer(res, bool_typet{});
  }
  UNREACHABLE;
}

TEST_CASE(
  "compute_or_over_bytes works correctly",
  "[core][goto-symex][compute_max_over_bytes]")
{
  auto test = shadow_memory_util_test_environmentt::make();
  const bool_typet sm_type;

  // Using mp_integer types otherwise on 32-bit machines n << 48 wraps around.
  std::array<mp_integer, 7> values = GENERATE(
    std::array<mp_integer, 7>{{0, 0, 0, 0, 0, 0, 0}},
    std::array<mp_integer, 7>{{2, 0, 0, 0, 0, 0, 0}},
    std::array<mp_integer, 7>{{0, 2, 0, 0, 0, 0, 0}},
    std::array<mp_integer, 7>{{0, 0, 2, 0, 0, 0, 0}},
    std::array<mp_integer, 7>{{0, 0, 0, 2, 0, 0, 0}},
    std::array<mp_integer, 7>{{0, 0, 0, 0, 2, 0, 0}},
    std::array<mp_integer, 7>{{0, 0, 0, 0, 0, 2, 0}},
    std::array<mp_integer, 7>{{0, 0, 0, 0, 0, 0, 2}},
    std::array<mp_integer, 7>{{8, 8, 8, 8, 8, 8, 8}});

  SECTION("test set " + std::to_string(values[0].to_long()))
  {
    SECTION("on bitvector")
    {
      const exprt bitvector = from_integer(
        values[0] + (values[1] << 8) + (values[2] << 16) + (values[3] << 24) +
          (values[4] << 32) + (values[5] << 40) + (values[6] << 48),
        unsignedbv_typet{56});

      const exprt max_over_struct =
        compute_or_over_bytes(bitvector, sm_type, test.ns, test.log, false);

      const exprt simplified =
        simplify_bit_or_exprt(simplify_expr(max_over_struct, test.ns));

      REQUIRE(simplified == from_integer(compute_or(values), sm_type));
    }
    SECTION("on array")
    {
      const array_typet array_type{
        unsigned_char_type(), from_integer(7, unsigned_long_int_type())};
      const array_exprt::operandst array_operands{
        from_integer(values[0], unsigned_char_type()),
        from_integer(values[1], unsigned_char_type()),
        from_integer(values[2], unsigned_char_type()),
        from_integer(values[3], unsigned_char_type()),
        from_integer(values[4], unsigned_char_type()),
        from_integer(values[5], unsigned_char_type()),
        from_integer(values[6], unsigned_char_type())};
      const array_exprt array_expr{array_operands, array_type};

      const exprt max_over_struct =
        compute_or_over_bytes(array_expr, sm_type, test.ns, test.log, false);

      const exprt simplified =
        simplify_bit_or_exprt(simplify_expr(max_over_struct, test.ns));

      REQUIRE(simplified == from_integer(compute_or(values), sm_type));
    }
    SECTION("on struct elements")
    {
      const struct_union_typet::componentst sub_struct_components{
        {"foo", signedbv_typet{32}}, {"bar", unsignedbv_typet{16}}};
      const struct_typet inner_struct_type{sub_struct_components};
      const struct_union_typet::componentst struct_components{
        {"fizz", char_type()}, {"bar", inner_struct_type}};
      const struct_typet struct_type{struct_components};
      const mp_integer foo =
        values[0] + (values[1] << 8) + (values[2] << 16) + (values[3] << 24);
      const mp_integer bar = values[4] + (values[5] << 8);
      const mp_integer fizz = values[6];
      const struct_exprt::operandst inner_operands{
        from_integer(foo, signedbv_typet{32}),
        from_integer(bar, unsignedbv_typet{16})};
      const struct_exprt inner_struct_expr{inner_operands, inner_struct_type};
      const struct_exprt::operandst struct_operands{
        from_integer(fizz, char_type()), inner_struct_expr};
      const struct_exprt struct_expr{struct_operands, struct_type};

      const exprt max_over_struct =
        compute_or_over_bytes(struct_expr, sm_type, test.ns, test.log, false);

      const exprt simplified =
        simplify_bit_or_exprt(simplify_expr(max_over_struct, test.ns));

      REQUIRE(simplified == from_integer(compute_or(values), sm_type));
    }
  }
}

TEST_CASE(
  "build_if_else_expr works correctly",
  "[core][goto-symex][build_if_else_expr]")
{
  const symbol_exprt symbol_a = {"condition_a", bool_typet{}};
  const symbol_exprt symbol_b = {"condition_b", bool_typet{}};
  const symbol_exprt symbol_c = {"condition_c", bool_typet{}};
  const symbol_exprt symbol_d = {"condition_d", bool_typet{}};
  const symbol_exprt symbol_e = {"condition_e", bool_typet{}};
  const symbol_exprt symbol_f = {"condition_f", bool_typet{}};

  const exprt value_a = from_integer(0, char_type());
  const exprt value_b = from_integer(1, char_type());
  const exprt value_c = from_integer(2, char_type());
  const exprt value_d = from_integer(3, char_type());
  const exprt value_e = from_integer(4, char_type());
  const exprt value_f = from_integer(5, char_type());

  std::vector<std::pair<exprt, exprt>> condition_and_value{
    {symbol_a, value_a},
    {symbol_b, value_b},
    {symbol_c, value_c},
    {symbol_d, value_d},
    {symbol_e, value_e},
    {symbol_f, value_f}};

  const exprt joined = build_if_else_expr(condition_and_value);
  const exprt expected = if_exprt(
    symbol_f,
    value_f,
    if_exprt{
      symbol_e,
      value_e,
      if_exprt{
        symbol_d,
        value_d,
        if_exprt{symbol_c, value_c, if_exprt{symbol_b, value_b, value_a}}}});

  REQUIRE(joined == expected);
}
