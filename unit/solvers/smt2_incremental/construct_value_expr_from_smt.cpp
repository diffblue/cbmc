// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/string_constant.h>
#include <util/symbol_table.h>

#include <solvers/smt2_incremental/ast/smt_terms.h>
#include <solvers/smt2_incremental/construct_value_expr_from_smt.h>
#include <solvers/smt2_incremental/object_tracking.h>
#include <solvers/smt2_incremental/smt_to_smt2_string.h>
#include <solvers/smt2_incremental/theories/smt_core_theory.h>
#include <testing-utils/invariant.h>
#include <testing-utils/use_catch.h>

#include <string>

static mp_integer power2(unsigned exponent)
{
  mp_integer result;
  result.setPower2(exponent);
  return result;
}

/// Returns the maximum integer value which can be stored in \p bits as an
/// unsigned integer.
static mp_integer max_int(const std::size_t bits)
{
  return power2(bits) - 1;
}

static type_symbolt make_c_enum_type_symbol(std::size_t underlying_size)
{
  const signedbv_typet underlying_type{underlying_size};
  c_enum_typet enum_type{underlying_type};

  auto &members = enum_type.members();
  members.reserve(20);

  for(unsigned int i = 0; i < 20; ++i)
  {
    c_enum_typet::c_enum_membert member;
    member.set_identifier("V" + std::to_string(i));
    member.set_base_name("V" + std::to_string(i));
    member.set_value(integer2bvrep(i, underlying_size));
    members.push_back(member);
  }
  return type_symbolt{"my_enum", enum_type, ID_C};
}

static symbolt make_c_enum_tag_instance_symbol(const symbolt &enum_type_symbol)
{
  const c_enum_tag_typet enum_tag{enum_type_symbol.name};
  return symbolt{"my_enum_value", enum_tag, ID_C};
}

TEST_CASE("Value expr construction from smt.", "[core][smt2_incremental]")
{
  symbol_tablet symbol_table;
  const namespacet ns{symbol_table};
  const symbolt enum_type_symbol = make_c_enum_type_symbol(42);
  const symbolt enum_tag_value_symbol =
    make_c_enum_tag_instance_symbol(enum_type_symbol);
  symbol_table.insert(enum_type_symbol);
  symbol_table.insert(enum_tag_value_symbol);
  std::optional<smt_termt> input_term;
  std::optional<exprt> expected_result;

  using rowt = std::pair<smt_termt, exprt>;

  // clang-format off
#define UNSIGNED_BIT_VECTOR_TESTS(bits)                                        \
  rowt{smt_bit_vector_constant_termt{0, (bits)},                               \
       from_integer(0, unsignedbv_typet{(bits)})},                             \
  rowt{smt_bit_vector_constant_termt{42, (bits)},                              \
       from_integer(42, unsignedbv_typet{(bits)})},                            \
  rowt{smt_bit_vector_constant_termt{max_int((bits) - 1), (bits)},             \
       from_integer(max_int((bits) - 1), unsignedbv_typet{(bits)})},           \
  rowt{smt_bit_vector_constant_termt{power2((bits) - 1), (bits)},              \
       from_integer(power2((bits) - 1), unsignedbv_typet{(bits)})},            \
  rowt{smt_bit_vector_constant_termt{max_int((bits)), (bits)},                 \
       from_integer(max_int((bits)), unsignedbv_typet{(bits)})}

#define SIGNED_BIT_VECTOR_TESTS(bits)                                          \
  rowt{smt_bit_vector_constant_termt{0, (bits)},                               \
       from_integer(0, signedbv_typet{(bits)})},                               \
  rowt{smt_bit_vector_constant_termt{42, (bits)},                              \
       from_integer(42, signedbv_typet{(bits)})},                              \
  rowt{smt_bit_vector_constant_termt{max_int((bits) - 1), (bits)},             \
       from_integer(max_int((bits) - 1), signedbv_typet{(bits)})},             \
  rowt{smt_bit_vector_constant_termt{power2((bits) - 1), (bits)},              \
       from_integer(-power2((bits) - 1), signedbv_typet{(bits)})},             \
  rowt{smt_bit_vector_constant_termt{max_int((bits)), (bits)},                 \
       from_integer(-1, signedbv_typet{(bits)})}
  // clang-format on

  std::tie(input_term, expected_result) = GENERATE_REF(
    rowt{smt_bool_literal_termt{true}, true_exprt{}},
    rowt{smt_bool_literal_termt{false}, false_exprt{}},
    rowt{smt_bit_vector_constant_termt{0, 8}, from_integer(0, c_bool_typet(8))},
    rowt{smt_bit_vector_constant_termt{1, 8}, from_integer(1, c_bool_typet(8))},
    rowt{
      smt_bit_vector_constant_termt{0, 64},
      from_integer(0, pointer_typet{empty_typet{}, 64 /* bits */})},
    // The reason for the more intricate elaboration of a pointer with a value
    // of 12 is a limitation in the design of from_integer, which only handles
    // pointers with value 0 (null pointers).
    rowt{
      smt_bit_vector_constant_termt{12, 64},
      constant_exprt(
        integer2bvrep(12, 64), pointer_typet{empty_typet{}, 64 /* bits */})},
    rowt{
      smt_bit_vector_constant_termt{2, 42},
      constant_exprt{"2", c_enum_tag_typet{enum_type_symbol.name}}},
    UNSIGNED_BIT_VECTOR_TESTS(8),
    SIGNED_BIT_VECTOR_TESTS(8),
    UNSIGNED_BIT_VECTOR_TESTS(16),
    SIGNED_BIT_VECTOR_TESTS(16),
    UNSIGNED_BIT_VECTOR_TESTS(32),
    SIGNED_BIT_VECTOR_TESTS(32),
    UNSIGNED_BIT_VECTOR_TESTS(64),
    SIGNED_BIT_VECTOR_TESTS(64));
  SECTION(
    "Construction of \"" + id2string(expected_result->type().id()) +
    "\" from \"" + smt_to_smt2_string(*input_term) + "\"")
  {
    REQUIRE(
      construct_value_expr_from_smt(*input_term, expected_result->type(), ns) ==
      *expected_result);
  }
}

TEST_CASE(
  "Invariant violations in value expr construction from smt.",
  "[core][smt2_incremental]")
{
  symbol_tablet symbol_table;
  const namespacet ns{symbol_table};
  const symbolt enum_type_symbol = make_c_enum_type_symbol(5);
  const symbolt enum_tag_value_symbol =
    make_c_enum_tag_instance_symbol(enum_type_symbol);
  symbol_table.insert(enum_type_symbol);
  symbol_table.insert(enum_tag_value_symbol);
  std::optional<smt_termt> input_term;
  std::optional<typet> input_type;
  std::string invariant_reason;

  using rowt = std::tuple<smt_termt, typet, std::string>;
  std::tie(input_term, input_type, invariant_reason) = GENERATE_REF(
    rowt{
      smt_bool_literal_termt{true},
      unsignedbv_typet{16},
      "Bool terms may only be used to construct bool typed expressions."},
    rowt{
      smt_identifier_termt{"foo", smt_bit_vector_sortt{16}},
      unsignedbv_typet{16},
      "Unexpected conversion of identifier to value expression."},
    rowt{
      smt_bit_vector_constant_termt{0, 8},
      unsignedbv_typet{16},
      "Width of smt bit vector term must match the width of bit vector type."},
    rowt{
      smt_bit_vector_constant_termt{0, 8},
      empty_typet{},
      "construct_value_expr_from_smt for bit vector should not be applied "
      "to unsupported type empty"},
    rowt{
      smt_core_theoryt::make_not(smt_bool_literal_termt{true}),
      unsignedbv_typet{16},
      "Unexpected conversion of function application to value expression."},
    rowt{
      smt_forall_termt{
        {smt_identifier_termt{"i", smt_bool_sortt{}}},
        smt_bool_literal_termt{true}},
      bool_typet{},
      "Unexpected conversion of forall quantifier to value expression."},
    rowt{
      smt_exists_termt{
        {smt_identifier_termt{"j", smt_bool_sortt{}}},
        smt_bool_literal_termt{true}},
      bool_typet{},
      "Unexpected conversion of exists quantifier to value expression."},
    rowt{
      smt_bit_vector_constant_termt{0, 16},
      pointer_typet{unsignedbv_typet{32}, 0},
      "Width of smt bit vector term must match the width of pointer type"},
    rowt{
      smt_bit_vector_constant_termt{2, 42},
      c_enum_tag_typet{"foo"},
      "we are assuming that a name exists in the namespace when this function "
      "is called - identifier foo was not found"},
    rowt{
      smt_bit_vector_constant_termt{8796093022208ul, 64},
      enum_tag_value_symbol.type,
      "Width of smt bit vector term must match the width of bit vector "
      "underlying type of the original c_enum type."});
  SECTION(invariant_reason)
  {
    const cbmc_invariants_should_throwt invariants_throw;

    REQUIRE_THROWS_MATCHES(
      construct_value_expr_from_smt(*input_term, *input_type, ns),
      invariant_failedt,
      invariant_failure_containing(invariant_reason));
  }
}

TEST_CASE(
  "Annotated pointer constant from smt with object map.",
  "[core][smt2_incremental]")
{
  // Set up architecture-dependent config (endianness) so that the helper
  // can construct byte_extract expressions when needed.
  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  config.ansi_c.set_arch_spec_x86_64();
  // Use default object_bits (8) with 64-bit pointers.
  // Encoding: [object_id (8 bits) | offset (56 bits)]
  const std::size_t object_bits = config.bv_encoding.object_bits;
  const std::size_t pointer_width = 64;
  const std::size_t offset_bits = pointer_width - object_bits;
  const pointer_typet ptr_type{empty_typet{}, pointer_width};
  symbol_tablet symbol_table;
  const namespacet ns{symbol_table};
  const smt_expression_identifier_mapt empty_identifiers;

  SECTION("Null pointer with object map produces null_pointer_exprt")
  {
    const smt_object_mapt object_map = initial_smt_object_map();
    const smt_bit_vector_constant_termt zero_term{0, pointer_width};
    const exprt result = construct_value_expr_from_smt(
      zero_term, ptr_type, ns, object_map, empty_identifiers);
    REQUIRE(result == null_pointer_exprt{ptr_type});
  }

  SECTION("Known symbol object produces annotated_pointer_constant_exprt")
  {
    smt_object_mapt object_map = initial_smt_object_map();
    const symbol_exprt sym{"my_var", signedbv_typet{32}};
    decision_procedure_objectt obj;
    obj.base_expression = sym;
    obj.unique_id = 2;
    object_map.emplace(sym, obj);

    // Encode pointer: object_id=2 in high bits, offset=0 in low bits.
    const mp_integer encoded_value = mp_integer{2} << offset_bits;
    const smt_bit_vector_constant_termt term{encoded_value, pointer_width};
    const pointer_typet sym_ptr_type{signedbv_typet{32}, pointer_width};
    const exprt result = construct_value_expr_from_smt(
      term, sym_ptr_type, ns, object_map, empty_identifiers);
    REQUIRE(can_cast_expr<annotated_pointer_constant_exprt>(result));
    const auto &annotated = to_annotated_pointer_constant_expr(result);
    // The symbolic pointer is address_of(my_var) possibly wrapped in a
    // typecast to the correct pointer width.
    const exprt expected_symbolic =
      typecast_exprt::conditional_cast(address_of_exprt(sym), sym_ptr_type);
    REQUIRE(annotated.symbolic_pointer() == expected_symbolic);
  }

  SECTION(
    "Non-zero offset into a known array produces base + index symbolic form")
  {
    smt_object_mapt object_map = initial_smt_object_map();
    const signedbv_typet i32{32};
    const array_typet arr_type{i32, from_integer(4, signedbv_typet{64})};
    const symbol_exprt arr_sym{"my_arr", arr_type};
    decision_procedure_objectt obj;
    obj.base_expression = arr_sym;
    obj.unique_id = 3;
    object_map.emplace(arr_sym, obj);

    // Encode pointer: object_id=3 in high bits, offset=8 (i.e. arr+2) in low.
    const mp_integer encoded_value = (mp_integer{3} << offset_bits) + 8;
    const smt_bit_vector_constant_termt term{encoded_value, pointer_width};
    const pointer_typet i32_ptr{i32, pointer_width};
    const exprt result = construct_value_expr_from_smt(
      term, i32_ptr, ns, object_map, empty_identifiers);
    REQUIRE(can_cast_expr<annotated_pointer_constant_exprt>(result));
    const auto &annotated = to_annotated_pointer_constant_expr(result);
    // The symbolic pointer must mention the array and a non-trivial
    // offset; we don't pin the exact byte_extract/plus_exprt shape (that
    // is the shared helper's contract, exercised by the SAT-side
    // pointer_logict::pointer_expr) but we do check that arr_sym appears.
    bool has_arr = false;
    annotated.symbolic_pointer().visit_pre(
      [&](const exprt &node)
      {
        if(node == arr_sym)
          has_arr = true;
      });
    REQUIRE(has_arr);
  }

  SECTION("Integer-address (NULL object + non-zero offset) matches SAT form")
  {
    // For pointer constants like (int *)0xDEADBEEF the encoded value is
    // object_id == 0 with a non-zero offset. The SAT backend renders this
    // as `((T *)NULL) + offset`; we must produce the same shape so traces
    // are identical across backends.
    const smt_object_mapt object_map = initial_smt_object_map();
    const mp_integer offset_value = 0xDEADBEEF;
    const smt_bit_vector_constant_termt term{offset_value, pointer_width};
    const exprt result = construct_value_expr_from_smt(
      term, ptr_type, ns, object_map, empty_identifiers);
    REQUIRE(can_cast_expr<annotated_pointer_constant_exprt>(result));
    const auto &annotated = to_annotated_pointer_constant_expr(result);
    const null_pointer_exprt null{ptr_type};
    const plus_exprt expected{
      null, from_integer(offset_value, pointer_diff_type())};
    REQUIRE(annotated.symbolic_pointer() == expected);
  }

  SECTION("Invalid pointer object produces annotated constant with INVALID")
  {
    const smt_object_mapt object_map = initial_smt_object_map();
    // Invalid object has unique_id=1.
    const mp_integer encoded_value = mp_integer{1} << offset_bits;
    const smt_bit_vector_constant_termt term{encoded_value, pointer_width};
    const exprt result = construct_value_expr_from_smt(
      term, ptr_type, ns, object_map, empty_identifiers);
    REQUIRE(can_cast_expr<annotated_pointer_constant_exprt>(result));
    const auto &annotated = to_annotated_pointer_constant_expr(result);
    REQUIRE(
      annotated.symbolic_pointer() == constant_exprt("INVALID", ptr_type));
  }

  SECTION("Unknown object ID falls back to plain constant_exprt")
  {
    const smt_object_mapt object_map = initial_smt_object_map();
    // Use object_id=99 which does not exist in the map.
    const mp_integer encoded_value = mp_integer{99} << offset_bits;
    const smt_bit_vector_constant_termt term{encoded_value, pointer_width};
    const exprt result = construct_value_expr_from_smt(
      term, ptr_type, ns, object_map, empty_identifiers);
    REQUIRE(result.id() == ID_constant);
    REQUIRE(result.type() == ptr_type);
  }

  SECTION("Original overload without object map still works")
  {
    // Non-zero pointer without object_map returns plain constant_exprt.
    const smt_bit_vector_constant_termt term{12, pointer_width};
    const exprt result = construct_value_expr_from_smt(term, ptr_type, ns);
    REQUIRE(
      result == constant_exprt(integer2bvrep(12, pointer_width), ptr_type));
  }
}

TEST_CASE(
  "Reverse expression_identifiers lookup for substituted expressions.",
  "[core][smt2_incremental]")
{
  // Architecture setup needed so the helper can build byte_extract
  // expressions for non-trivial offsets if the test exercises them.
  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  config.ansi_c.set_arch_spec_x86_64();
  // Simulates the scenario where an expression (e.g., a string constant)
  // was substituted with a symbol_exprt during SMT conversion, and the
  // object_map tracks the substituted symbol_exprt as the base expression.
  // The reverse lookup through expression_identifiers should recover the
  // original expression for symbolic pointer display in traces.
  const std::size_t object_bits = config.bv_encoding.object_bits;
  const std::size_t pointer_width = 64;
  const std::size_t offset_bits = pointer_width - object_bits;
  symbol_tablet symbol_table;
  const namespacet ns{symbol_table};
  const smt_expression_identifier_mapt empty_identifiers;

  SECTION("symbol_exprt original recovers under reverse lookup")
  {
    const signedbv_typet value_type{32};
    const symbol_exprt original_expr{"my_original_sym", value_type};
    const symbol_exprt substituted_sym{"array_0", value_type};

    const smt_identifier_termt smt_id{
      "array_0", smt_bit_vector_sortt{pointer_width}};
    smt_expression_identifier_mapt expression_identifiers;
    expression_identifiers.emplace(original_expr, smt_id);

    smt_object_mapt object_map = initial_smt_object_map();
    decision_procedure_objectt obj;
    obj.base_expression = substituted_sym;
    obj.unique_id = 2;
    object_map.emplace(substituted_sym, obj);

    const mp_integer encoded_value = mp_integer{2} << offset_bits;
    const smt_bit_vector_constant_termt term{encoded_value, pointer_width};
    const pointer_typet ptr_type{value_type, pointer_width};

    SECTION("With expression_identifiers, resolves original expression")
    {
      const exprt result = construct_value_expr_from_smt(
        term, ptr_type, ns, object_map, expression_identifiers);
      REQUIRE(can_cast_expr<annotated_pointer_constant_exprt>(result));
      const auto &annotated = to_annotated_pointer_constant_expr(result);
      const exprt &sym_ptr = annotated.symbolic_pointer();
      // Positive: original_expr appears in the symbolic form.
      bool has_original = false;
      sym_ptr.visit_pre(
        [&](const exprt &node)
        {
          if(node == original_expr)
            has_original = true;
        });
      REQUIRE(has_original);
    }

    SECTION("Without expression_identifiers, uses substituted symbol")
    {
      const exprt result = construct_value_expr_from_smt(
        term, ptr_type, ns, object_map, empty_identifiers);
      REQUIRE(can_cast_expr<annotated_pointer_constant_exprt>(result));
      const auto &annotated = to_annotated_pointer_constant_expr(result);
      const exprt &sym_ptr = annotated.symbolic_pointer();
      // Negative: original_expr does NOT appear.
      bool has_original = false;
      // Positive: the substituted symbol DOES appear.
      bool has_substituted = false;
      sym_ptr.visit_pre(
        [&](const exprt &node)
        {
          if(node == original_expr)
            has_original = true;
          if(node == substituted_sym)
            has_substituted = true;
        });
      REQUIRE_FALSE(has_original);
      REQUIRE(has_substituted);
    }
  }

  SECTION("string_constantt original recovers under reverse lookup")
  {
    // The motivating scenario from the commit message: a string constant
    // ("abc") gets substituted with an array-typed symbol during SMT
    // conversion (e.g., array_0). The trace must surface the original
    // string literal, not the synthesised array name.
    const string_constantt original_str{"abc"};
    const array_typet arr_type = original_str.type();
    const symbol_exprt substituted_sym{"array_0", arr_type};

    const smt_identifier_termt smt_id{
      "array_0", smt_bit_vector_sortt{pointer_width}};
    smt_expression_identifier_mapt expression_identifiers;
    expression_identifiers.emplace(original_str, smt_id);

    smt_object_mapt object_map = initial_smt_object_map();
    decision_procedure_objectt obj;
    obj.base_expression = substituted_sym;
    obj.unique_id = 4;
    object_map.emplace(substituted_sym, obj);

    const mp_integer encoded_value = mp_integer{4} << offset_bits;
    const smt_bit_vector_constant_termt term{encoded_value, pointer_width};
    const pointer_typet ptr_type{arr_type.element_type(), pointer_width};

    const exprt result = construct_value_expr_from_smt(
      term, ptr_type, ns, object_map, expression_identifiers);
    REQUIRE(can_cast_expr<annotated_pointer_constant_exprt>(result));
    const auto &annotated = to_annotated_pointer_constant_expr(result);
    const exprt &sym_ptr = annotated.symbolic_pointer();
    bool has_string = false;
    sym_ptr.visit_pre(
      [&](const exprt &node)
      {
        if(node == original_str)
          has_string = true;
      });
    REQUIRE(has_string);
  }
}
