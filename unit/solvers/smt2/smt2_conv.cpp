// Author: Diffblue Ltd.

/// \file
/// Unit tests for smt2_convt

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <solvers/smt2/smt2_conv.h>
#include <solvers/smt2/smt2_dec.h>
#include <testing-utils/use_catch.h>

#include <utility>

TEST_CASE(
  "smt2_convt::convert_identifier character escaping.",
  "[core][solvers][smt2]")
{
  const std::string no_escaping_characters =
    "abcdefghijklmnopqrstuvwxyz0123456789$";
  CHECK(
    smt2_convt::convert_identifier(no_escaping_characters) ==
    no_escaping_characters);
  CHECK(smt2_convt::convert_identifier("\\") == "|&92;|");
  CHECK(smt2_convt::convert_identifier("|") == "|&124;|");
  CHECK(smt2_convt::convert_identifier("&") == "&");
}

namespace
{
/// Own the converter and restore the architecture configuration after a test.
struct smt2_type_discovery_testt
{
  const configt::ansi_ct saved_ansi_c = config.ansi_c;
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  std::ostringstream output;
  smt2_convt
    converter{ns, "type discovery", "", "ALL", smt2_convt::solvert::Z3, output};

  smt2_type_discovery_testt()
  {
    config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
    config.ansi_c.set_arch_spec_x86_64();
  }

  ~smt2_type_discovery_testt()
  {
    config.ansi_c = saved_ansi_c;
  }

  /// Add types whose recursion is broken by a pointer edge.
  void add_recursive_types()
  {
    // The pointer edge makes this legal without an infinitely sized value:
    // Leaf.parent -> Internal*, Internal.data -> Leaf by value.
    symbol_table.insert(type_symbolt{
      "Leaf",
      struct_typet{
        {{"parent", pointer_typet{struct_tag_typet{"Internal"}, 64}}}},
      ID_C});
    symbol_table.insert(type_symbolt{
      "Internal", struct_typet{{{"data", struct_tag_typet{"Leaf"}}}}, ID_C});
  }
};
} // namespace

TEST_CASE(
  "SMT pointer discovery does not declare recursive pointee datatypes",
  "[core][solvers][smt2]")
{
  smt2_type_discovery_testt test;
  test.add_recursive_types();
  struct_tag_typet pointee{"Leaf"};
  SECTION("Leaf first")
  {
    // R1: pointer-only use + Leaf-first recursion previously tried to declare
    // Internal.data before Leaf's tag alias existed. The output only needs a
    // pointer bitvector, and discovery must terminate without any datatype.
  }
  SECTION("Internal first")
  {
    // R2: reversing the entry order must have the same pointer-only effect.
    pointee = struct_tag_typet{"Internal"};
  }
  const pointer_typet pointer{pointee, 64};
  test.converter.handle(
    equal_exprt{symbol_exprt{"p", pointer}, null_pointer_exprt{pointer}});
  const auto output = test.output.str();
  CHECK(output.find("(declare-fun p () (_ BitVec 64))") != std::string::npos);
  CHECK(output.find("(declare-datatypes") == std::string::npos);
}

TEST_CASE(
  "SMT discovery distinguishes pointer and value visits to a shared tag",
  "[core][solvers][smt2]")
{
  smt2_type_discovery_testt test;
  test.add_recursive_types();
  struct_typet::componentst components{
    {"pointer", pointer_typet{struct_tag_typet{"Internal"}, 64}},
    {"value", struct_tag_typet{"Internal"}}};
  SECTION("Pointer before value")
  {
    // R3: the same traversal sees Internal indirectly before using it as a
    // value. A pointer-only visited tag must not suppress datatype discovery.
  }
  SECTION("Value before pointer")
  {
    // R4: the reverse member order must preserve the same value dependencies.
    std::swap(components[0], components[1]);
  }
  const struct_typet aggregate{components};
  test.converter.handle(equal_exprt{
    symbol_exprt{"aggregate", aggregate}, symbol_exprt{"other", aggregate}});
  const auto output = test.output.str();
  const auto leaf = output.find(".parent (_ BitVec 64)");
  const auto internal = output.find(".data struct.");
  const auto holder = output.find(".value struct.");
  REQUIRE(leaf != std::string::npos);
  REQUIRE(internal != std::string::npos);
  REQUIRE(holder != std::string::npos);
  CHECK(leaf < internal);
  CHECK(internal < holder);
  CHECK(output.find("(declare-fun aggregate () struct.") != std::string::npos);
}

TEST_CASE(
  "SMT member values discover types after an earlier pointer-only use",
  "[core][solvers][smt2]")
{
  smt2_type_discovery_testt test;
  test.add_recursive_types();
  const pointer_typet leaf_pointer{struct_tag_typet{"Leaf"}, 64};
  const pointer_typet internal_pointer{struct_tag_typet{"Internal"}, 64};
  test.converter.handle(equal_exprt{
    symbol_exprt{"p", leaf_pointer}, null_pointer_exprt{leaf_pointer}});
  REQUIRE(test.output.str().find("(declare-datatypes") == std::string::npos);

  // R5: a subsequent expression reads a member of a real Leaf value. Its
  // operand must now declare Leaf and use its selector; the earlier indirect
  // visit must not leave an empty alias/base entry that suppresses this work.
  const member_exprt parent{
    symbol_exprt{"leaf_value", struct_tag_typet{"Leaf"}},
    "parent",
    internal_pointer};
  test.converter.handle(
    equal_exprt{parent, null_pointer_exprt{internal_pointer}});
  const auto output = test.output.str();
  CHECK(output.find("(declare-fun leaf_value () struct.") != std::string::npos);
  CHECK(output.find(".parent leaf_value)") != std::string::npos);
  CHECK(output.find(".data struct.") == std::string::npos);
}

TEST_CASE(
  "SMT pointer discovery retains implicit variable array-size dependencies",
  "[core][solvers][smt2]")
{
  smt2_type_discovery_testt test;
  const unsignedbv_typet index_type{64};
  const symbol_exprt size{"array_length", index_type};
  const array_typet array{unsignedbv_typet{8}, size};
  const pointer_typet pointer{array, 64};
  const symbol_exprt base{"p", pointer};
  const symbol_exprt index{"index", index_type};

  // R6: the size symbol occurs only in the pointed-to array type. The
  // element_address converter adds sizeof(element_type) implicitly after
  // symbol discovery, so removing the entire pointer-type walk loses it.
  const element_address_exprt address{base, index, pointer};
  test.converter.handle(equal_exprt{address, base});
  const auto output = test.output.str();
  const auto size_declaration =
    output.find("(declare-fun array_length () (_ BitVec 64))");
  const auto address_use = output.find("(element-address-p64 p index ");
  REQUIRE(size_declaration != std::string::npos);
  REQUIRE(address_use != std::string::npos);
  CHECK(size_declaration < address_use);
  CHECK(output.find("array_length", address_use) != std::string::npos);
}

TEST_CASE(
  "SMT function pointers retain parameter and return-type size expressions",
  "[core][solvers][smt2]")
{
  smt2_type_discovery_testt test;
  const unsignedbv_typet index_type{64};
  const array_typet parameter_array{
    unsignedbv_typet{8}, symbol_exprt{"parameter_size", index_type}};
  const array_typet return_array{
    unsignedbv_typet{8}, symbol_exprt{"return_size", index_type}};
  test.symbol_table.insert(
    type_symbolt{"Parameter", struct_typet{{{"data", parameter_array}}}, ID_C});
  test.symbol_table.insert(
    type_symbolt{"Return", struct_typet{{{"data", return_array}}}, ID_C});
  const code_typet function{
    {code_typet::parametert{struct_tag_typet{"Parameter"}}},
    struct_tag_typet{"Return"}};
  const pointer_typet pointer{function, 64};

  // R7: code-pointer signatures are indirect type uses, but their nested
  // array sizes remain expression dependencies. Both sides of the signature
  // must be visited without emitting either aggregate's unused datatype.
  test.converter.handle(equal_exprt{
    symbol_exprt{"function_pointer", pointer}, null_pointer_exprt{pointer}});
  const auto output = test.output.str();
  CHECK(
    output.find("(declare-fun parameter_size () (_ BitVec 64))") !=
    std::string::npos);
  CHECK(
    output.find("(declare-fun return_size () (_ BitVec 64))") !=
    std::string::npos);
  CHECK(output.find("(declare-datatypes") == std::string::npos);
}

TEST_CASE(
  "SMT pointer-only discovery does not register complex or state sorts",
  "[core][solvers][smt2]")
{
  smt2_type_discovery_testt test;
  typet pointee = complex_typet{signedbv_typet{32}};
  std::string declaration = "(declare-datatypes";
  SECTION("Complex")
  {
    // R8: complex values require a datatype; complex pointers do not.
  }
  SECTION("State")
  {
    // R9: the same distinction applies to state's uninterpreted sort.
    pointee = typet{ID_state};
    declaration = "(declare-sort state 0)";
  }
  const pointer_typet pointer{pointee, 64};
  test.converter.handle(
    equal_exprt{symbol_exprt{"p", pointer}, null_pointer_exprt{pointer}});
  REQUIRE(test.output.str().find(declaration) == std::string::npos);
  test.converter.handle(equal_exprt{
    symbol_exprt{"value", pointee}, symbol_exprt{"other", pointee}});
  CHECK(test.output.str().find(declaration) != std::string::npos);
}

TEST_CASE(
  "SMT pointer discovery preserves bitvector pointer arithmetic",
  "[core][solvers][smt2]")
{
  smt2_type_discovery_testt test;
  test.add_recursive_types();
  test.converter.use_datatypes = false;
  const pointer_typet pointer{struct_tag_typet{"Leaf"}, 64};
  const symbol_exprt base{"p", pointer};
  const plus_exprt next{base, from_integer(1, signedbv_typet{64})};

  // R10: with datatypes disabled, a recursive pointee still has a concrete
  // size (one 64-bit pointer). Existing pointer arithmetic must keep scaling
  // its offset by eight bytes; this change must not alter pointer encoding.
  test.converter.handle(equal_exprt{next, base});
  const auto output = test.output.str();
  CHECK(output.find("(declare-fun p () (_ BitVec 64))") != std::string::npos);
  CHECK(output.find("(bvmul ") != std::string::npos);
  CHECK(output.find("(_ bv8 ") != std::string::npos);
  CHECK(output.find("(declare-datatypes") == std::string::npos);
}

TEST_CASE(
  "SMT pointer array sizes discover datatypes needed by size expressions",
  "[core][solvers][smt2]")
{
  smt2_type_discovery_testt test;
  const unsignedbv_typet index_type{64};
  const struct_typet bounds_type{{{"length", index_type}}};
  const member_exprt size{
    symbol_exprt{"bounds", bounds_type}, "length", index_type};
  const pointer_typet pointer{array_typet{unsignedbv_typet{8}, size}, 64};
  const symbol_exprt base{"p", pointer};
  const element_address_exprt address{
    base, symbol_exprt{"index", index_type}, pointer};

  // R11: a pointer's array size reads a member of a struct value. Although
  // the pointee is an expressions-only dependency, the size expression's
  // operands need full discovery: declare the struct before its symbol and
  // selector use. Propagating expressions-only into the expression loses it.
  test.converter.handle(equal_exprt{address, base});
  const auto output = test.output.str();
  const auto datatype = output.find(".length (_ BitVec 64)");
  const auto symbol = output.find("(declare-fun bounds () struct.");
  const auto address_use = output.find("(element-address-p64 p index ");
  REQUIRE(datatype != std::string::npos);
  REQUIRE(symbol != std::string::npos);
  REQUIRE(address_use != std::string::npos);
  CHECK(datatype < symbol);
  CHECK(symbol < address_use);
  CHECK(output.find(".length bounds)", address_use) != std::string::npos);
}

TEST_CASE(
  "SMT union tags distinguish pointer and value discovery modes",
  "[core][solvers][smt2]")
{
  smt2_type_discovery_testt test;
  const union_tag_typet tag{"Payload"};
  const pointer_typet pointer{tag, 64};
  test.symbol_table.insert(type_symbolt{
    "Member", struct_typet{{{"payload_value", unsignedbv_typet{64}}}}, ID_C});
  test.symbol_table.insert(type_symbolt{
    "Payload",
    union_typet{{{"data", struct_tag_typet{"Member"}}, {"next", pointer}}},
    ID_C});

  // R12: a self-pointer terminates through a union tag without registering
  // its member datatype. In the following aggregate, the same traversal
  // visits that tag first through a pointer and then by value. The latter
  // must still discover Member; a tag-only visited set suppresses this work.
  test.converter.handle(
    equal_exprt{symbol_exprt{"p", pointer}, null_pointer_exprt{pointer}});
  REQUIRE(test.output.str().find("(declare-datatypes") == std::string::npos);
  const struct_typet aggregate{{{"pointer", pointer}, {"value", tag}}};
  test.converter.handle(equal_exprt{
    symbol_exprt{"aggregate", aggregate}, symbol_exprt{"other", aggregate}});
  const auto output = test.output.str();
  const auto member = output.find(".payload_value (_ BitVec 64)");
  const auto holder = output.find(".value (_ BitVec 64)");
  REQUIRE(member != std::string::npos);
  REQUIRE(holder != std::string::npos);
  CHECK(member < holder);
  CHECK(output.find("(declare-fun aggregate () struct.") != std::string::npos);
}

/// Helper: extract the "(assert ...)" line from SMT2 output of set_to
static std::string get_assert(const exprt &red_expr)
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  std::ostringstream out;
  smt2_convt conv(ns, "test", "", "QF_BV", smt2_convt::solvert::GENERIC, out);
  conv.set_to(red_expr, true);
  std::string result = out.str();
  auto pos = result.find("(assert ");
  REQUIRE(pos != std::string::npos);
  // strip trailing newline
  auto end = result.find_last_not_of('\n');
  return result.substr(pos, end - pos + 1);
}

TEST_CASE("smt2_convt reduction operators", "[core][solvers][smt2]")
{
  unsignedbv_typet u2(2);
  symbol_exprt sym("x", u2);

  SECTION("reduction_and")
  {
    REQUIRE(get_assert(reduction_and_exprt{sym}) == "(assert (= x (_ bv3 2)))");
  }

  SECTION("reduction_nand")
  {
    REQUIRE(
      get_assert(reduction_nand_exprt{sym}) ==
      "(assert (not (= x (_ bv3 2))))");
  }

  SECTION("reduction_or")
  {
    REQUIRE(
      get_assert(reduction_or_exprt{sym}) == "(assert (not (= x (_ bv0 2))))");
  }

  SECTION("reduction_nor")
  {
    REQUIRE(
      get_assert(reduction_nor_exprt{sym}) ==
      "(assert (not (not (= x (_ bv0 2)))))");
  }

  SECTION("reduction_xor")
  {
    REQUIRE(
      get_assert(reduction_xor_exprt{sym}) ==
      "(assert (let ((?rop x)) "
      "(= (bvxor ((_ extract 0 0) ?rop) ((_ extract 1 1) ?rop)) #b1)))");
  }

  SECTION("reduction_xnor")
  {
    REQUIRE(
      get_assert(reduction_xnor_exprt{sym}) ==
      "(assert (not (let ((?rop x)) "
      "(= (bvxor ((_ extract 0 0) ?rop) ((_ extract 1 1) ?rop)) #b1))))");
  }

  SECTION("reduction_xor 1-bit")
  {
    symbol_exprt sym1("y", unsignedbv_typet(1));
    REQUIRE(get_assert(reduction_xor_exprt{sym1}) == "(assert (= y #b1))");
  }

  SECTION("reduction_and 1-bit")
  {
    symbol_exprt sym1("y", unsignedbv_typet(1));
    REQUIRE(
      get_assert(reduction_and_exprt{sym1}) == "(assert (= y (_ bv1 1)))");
  }

  SECTION("reduction_or 1-bit")
  {
    symbol_exprt sym1("y", unsignedbv_typet(1));
    REQUIRE(
      get_assert(reduction_or_exprt{sym1}) == "(assert (not (= y (_ bv0 1))))");
  }
}

TEST_CASE(
  "smt2_convt no unary concat for zero-width operand",
  "[core][solvers][smt2]")
{
  unsignedbv_typet u8{8};
  unsignedbv_typet u0{0};
  symbol_exprt x{"x", u8};
  symbol_exprt z{"z", u0};

  // concat of a zero-width and a non-zero-width operand should emit
  // the non-zero-width operand directly, not (concat x)
  concatenation_exprt concat{{z, x}, u8};
  REQUIRE(get_assert(equal_exprt{concat, x}) == "(assert (= x x))");
}

TEST_CASE("smt2_convt range encoding", "[core][solvers][smt2]")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  null_message_handlert message_handler;
  smt2_dect smt2_dec(
    ns,
    "unit test",
    "",
    "QF_AUFBV",
    smt2_dect::solvert::Z3,
    "",
    message_handler);

  GIVEN("An unsatisfiable formula over range-typed variables")
  {
    integer_range_typet range_type{0, 2}; // {0,...,2}
    symbol_exprt a{"a", range_type};
    smt2_dec << notequal_exprt{a, from_integer(0, range_type)};
    smt2_dec << notequal_exprt{a, from_integer(1, range_type)};
    smt2_dec << notequal_exprt{a, from_integer(2, range_type)};

    THEN("the SMT2 solver says it's UNSAT")
    {
      REQUIRE(smt2_dec() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }
}

TEST_CASE(
  "smt2_convt::flatten2bv FPA-encoded float constant",
  "[core][solvers][smt2]")
{
  // Drive `flatten2bv` on a `floatbv` constant under a solver that
  // enables the SMT-LIB FloatingPoint theory (use_FPA_theory == true).
  // This pins the constant branch of the new flatten2bv handler:
  // the constant's IEEE-754 interchange bit pattern is emitted as a
  // bit-vector literal.  Without the fix, the back-end aborts here
  // with `INVARIANT(!use_FPA_theory, ...)`.
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  std::ostringstream out;
  // CPROVER_SMT2 sets use_FPA_theory = true at construction time.
  smt2_convt conv{
    ns, "test", "", "QF_AUFBV", smt2_convt::solvert::CPROVER_SMT2, out};

  // double 1.0 -> 0x3FF0000000000000 = 4607182418800017408.
  ieee_float_valuet f{ieee_float_spect::double_precision()};
  f.from_double(1.0);
  const constant_exprt fp_const = f.to_expr();

  // Place the constant in a single-member union so that the back-end
  // takes a flat-of-float path:
  //   convert_typecast(union -> bv64)
  //     -> convert_expr(union_exprt)
  //     -> convert_union
  //     -> flatten2bv(float)  <- exercises the new code
  const union_typet u_type{
    {struct_union_typet::componentt{"d", fp_const.type()}}};
  const union_exprt u_expr{"d", fp_const, u_type};

  const unsignedbv_typet u64{64};
  const constant_exprt expected =
    from_integer(mp_integer{"4607182418800017408"}, u64);

  conv.set_to(equal_exprt{typecast_exprt{u_expr, u64}, expected}, true);

  REQUIRE(out.str().find("(_ bv4607182418800017408 64)") != std::string::npos);
}

/// Helper: build an application of a CPROVER string/regex built-in function
/// over the given SMT-LIB-native operands.
static function_application_exprt string_builtin_app(
  const irep_idt &fn,
  std::vector<exprt> args,
  const typet &codomain)
{
  std::vector<typet> domain;
  for(const auto &a : args)
    domain.push_back(a.type());
  return function_application_exprt{
    symbol_exprt{fn, mathematical_function_typet{domain, codomain}},
    std::move(args)};
}

TEST_CASE(
  "smt2_convt string and regex operator lowering",
  "[core][solvers][smt2]")
{
  const typet string_type{ID_string};
  const typet regex_type{ID_regex};
  const symbol_exprt s1{"s1", string_type};
  const symbol_exprt s2{"s2", string_type};

  SECTION("string literal escapes only the double quote")
  {
    // value is: a " b \ c  -- the backslash must stay literal. Wrap in a
    // boolean op so set_to does not attempt a (width-based) equality split.
    const constant_exprt c{"a\"b\\c", string_type};
    const auto contains_c = string_builtin_app(
      ID_cprover_string_contains_func, {s1, c}, bool_typet{});
    REQUIRE(
      get_assert(contains_c) == "(assert (str.contains s1 \"a\"\"b\\c\"))");
  }

  SECTION("concat lowers to str.++")
  {
    const auto concat =
      string_builtin_app(ID_cprover_string_concat_func, {s1, s2}, string_type);
    const auto contains_concat = string_builtin_app(
      ID_cprover_string_contains_func, {concat, s1}, bool_typet{});
    REQUIRE(
      get_assert(contains_concat) ==
      "(assert (str.contains (str.++ s1 s2) s1))");
  }

  SECTION("contains lowers to str.contains")
  {
    const auto contains = string_builtin_app(
      ID_cprover_string_contains_func, {s1, s2}, bool_typet{});
    REQUIRE(get_assert(contains) == "(assert (str.contains s1 s2))");
  }

  SECTION("is_prefix lowers to str.prefixof")
  {
    const auto pref = string_builtin_app(
      ID_cprover_string_is_prefix_func, {s1, s2}, bool_typet{});
    REQUIRE(get_assert(pref) == "(assert (str.prefixof s1 s2))");
  }

  SECTION("in_regex/to_regex lower to str.in_re/str.to_re")
  {
    const auto re =
      string_builtin_app(ID_cprover_string_to_regex_func, {s2}, regex_type);
    const auto in = string_builtin_app(
      ID_cprover_string_in_regex_func, {s1, re}, bool_typet{});
    REQUIRE(get_assert(in) == "(assert (str.in_re s1 (str.to_re s2)))");
  }

  SECTION("regex star lowers to re.*")
  {
    const auto re =
      string_builtin_app(ID_cprover_string_to_regex_func, {s1}, regex_type);
    const auto star =
      string_builtin_app(ID_cprover_regex_star_func, {re}, regex_type);
    const auto in = string_builtin_app(
      ID_cprover_string_in_regex_func, {s2, star}, bool_typet{});
    REQUIRE(get_assert(in) == "(assert (str.in_re s2 (re.* (str.to_re s1))))");
  }

  SECTION("startswith/endswith swap operands to prefixof/suffixof")
  {
    const auto sw = string_builtin_app(
      ID_cprover_string_startswith_func, {s1, s2}, bool_typet{});
    REQUIRE(get_assert(sw) == "(assert (str.prefixof s2 s1))");
    const auto ew = string_builtin_app(
      ID_cprover_string_endswith_func, {s1, s2}, bool_typet{});
    REQUIRE(get_assert(ew) == "(assert (str.suffixof s2 s1))");
  }

  SECTION("is_empty lowers to equality with the empty string")
  {
    const auto empty =
      string_builtin_app(ID_cprover_string_is_empty_func, {s1}, bool_typet{});
    REQUIRE(get_assert(empty) == "(assert (= s1 \"\"))");
  }

  SECTION("index_of defaults the start offset to 0 / passes it through")
  {
    const typet int_type{ID_integer};
    // 2-arg form: offset padded with 0; wrapped so set_to sees a boolean.
    const auto idx2 =
      string_builtin_app(ID_cprover_string_index_of_func, {s1, s2}, int_type);
    const auto at2 =
      string_builtin_app(ID_cprover_string_char_at_func, {s1, idx2}, s1.type());
    const auto c2 = string_builtin_app(
      ID_cprover_string_contains_func, {at2, s1}, bool_typet{});
    REQUIRE(
      get_assert(c2) ==
      "(assert (str.contains (str.at s1 (str.indexof s1 s2 0)) s1))");
    // 3-arg form: explicit offset (here str.len s2) passed through.
    const auto len =
      string_builtin_app(ID_cprover_string_length_func, {s2}, int_type);
    const auto idx3 = string_builtin_app(
      ID_cprover_string_index_of_func, {s1, s2, len}, int_type);
    const auto at3 =
      string_builtin_app(ID_cprover_string_char_at_func, {s1, idx3}, s1.type());
    const auto c3 = string_builtin_app(
      ID_cprover_string_contains_func, {at3, s1}, bool_typet{});
    REQUIRE(
      get_assert(c3) ==
      "(assert (str.contains (str.at s1 (str.indexof s1 s2 (str.len s2))) "
      "s1))");
  }

  SECTION("regex opt/diff lower to re.opt/re.diff")
  {
    const auto re1 =
      string_builtin_app(ID_cprover_string_to_regex_func, {s1}, regex_type);
    const auto re2 =
      string_builtin_app(ID_cprover_string_to_regex_func, {s2}, regex_type);
    const auto opt =
      string_builtin_app(ID_cprover_regex_opt_func, {re1}, regex_type);
    const auto in_opt = string_builtin_app(
      ID_cprover_string_in_regex_func, {s2, opt}, bool_typet{});
    REQUIRE(
      get_assert(in_opt) == "(assert (str.in_re s2 (re.opt (str.to_re s1))))");
    const auto diff =
      string_builtin_app(ID_cprover_regex_diff_func, {re1, re2}, regex_type);
    const auto in_diff = string_builtin_app(
      ID_cprover_string_in_regex_func, {s1, diff}, bool_typet{});
    REQUIRE(
      get_assert(in_diff) ==
      "(assert (str.in_re s1 (re.diff (str.to_re s1) (str.to_re s2))))");
  }

  SECTION("string operators substring/char_at/replace/length/equal")
  {
    const typet int_type{ID_integer};
    const exprt c0 = from_integer(0, int_type);
    const exprt c3 = from_integer(3, int_type);
    const auto substr = string_builtin_app(
      ID_cprover_string_substring_func, {s1, c0, c3}, string_type);
    const auto c_sub = string_builtin_app(
      ID_cprover_string_contains_func, {substr, s1}, bool_typet{});
    REQUIRE(
      get_assert(c_sub) == "(assert (str.contains (str.substr s1 0 3) s1))");

    const auto at =
      string_builtin_app(ID_cprover_string_char_at_func, {s1, c0}, string_type);
    const auto c_at = string_builtin_app(
      ID_cprover_string_contains_func, {at, s1}, bool_typet{});
    REQUIRE(get_assert(c_at) == "(assert (str.contains (str.at s1 0) s1))");

    const auto repl = string_builtin_app(
      ID_cprover_string_replace_func, {s1, s2, s1}, string_type);
    const auto c_repl = string_builtin_app(
      ID_cprover_string_contains_func, {repl, s2}, bool_typet{});
    REQUIRE(
      get_assert(c_repl) ==
      "(assert (str.contains (str.replace s1 s2 s1) s2))");

    const auto len =
      string_builtin_app(ID_cprover_string_length_func, {s2}, int_type);
    const auto at_len = string_builtin_app(
      ID_cprover_string_char_at_func, {s1, len}, string_type);
    const auto c_len = string_builtin_app(
      ID_cprover_string_contains_func, {at_len, s1}, bool_typet{});
    REQUIRE(
      get_assert(c_len) ==
      "(assert (str.contains (str.at s1 (str.len s2)) s1))");

    const auto eq =
      string_builtin_app(ID_cprover_string_equal_func, {s1, s2}, bool_typet{});
    REQUIRE(get_assert(eq) == "(assert (= s1 s2))");
  }

  SECTION("regex range/concat/plus/union/inter/comp operators")
  {
    const auto re1 =
      string_builtin_app(ID_cprover_string_to_regex_func, {s1}, regex_type);
    const auto re2 =
      string_builtin_app(ID_cprover_string_to_regex_func, {s2}, regex_type);
    auto in = [&](const exprt &re)
    {
      return string_builtin_app(
        ID_cprover_string_in_regex_func, {s1, re}, bool_typet{});
    };
    REQUIRE(
      get_assert(in(string_builtin_app(
        ID_cprover_regex_range_func, {s1, s2}, regex_type))) ==
      "(assert (str.in_re s1 (re.range s1 s2)))");
    REQUIRE(
      get_assert(in(string_builtin_app(
        ID_cprover_regex_concat_func, {re1, re2}, regex_type))) ==
      "(assert (str.in_re s1 (re.++ (str.to_re s1) (str.to_re s2))))");
    REQUIRE(
      get_assert(in(
        string_builtin_app(ID_cprover_regex_plus_func, {re1}, regex_type))) ==
      "(assert (str.in_re s1 (re.+ (str.to_re s1))))");
    REQUIRE(
      get_assert(in(string_builtin_app(
        ID_cprover_regex_union_func, {re1, re2}, regex_type))) ==
      "(assert (str.in_re s1 (re.union (str.to_re s1) (str.to_re s2))))");
    REQUIRE(
      get_assert(in(string_builtin_app(
        ID_cprover_regex_inter_func, {re1, re2}, regex_type))) ==
      "(assert (str.in_re s1 (re.inter (str.to_re s1) (str.to_re s2))))");
    REQUIRE(
      get_assert(in(
        string_builtin_app(ID_cprover_regex_comp_func, {re1}, regex_type))) ==
      "(assert (str.in_re s1 (re.comp (str.to_re s1))))");
  }

  SECTION("nullary regex operators all/allchar/none")
  {
    auto in = [&](const irep_idt &id)
    {
      return string_builtin_app(
        ID_cprover_string_in_regex_func,
        {s1, string_builtin_app(id, {}, regex_type)},
        bool_typet{});
    };
    REQUIRE(
      get_assert(in(ID_cprover_regex_all_func)) ==
      "(assert (str.in_re s1 re.all))");
    REQUIRE(
      get_assert(in(ID_cprover_regex_allchar_func)) ==
      "(assert (str.in_re s1 re.allchar))");
    REQUIRE(
      get_assert(in(ID_cprover_regex_none_func)) ==
      "(assert (str.in_re s1 re.none))");
  }

  SECTION("re.loop lowers to the indexed ((_ re.loop lo hi) r) operator")
  {
    const typet int_type{ID_integer};
    const auto re1 =
      string_builtin_app(ID_cprover_string_to_regex_func, {s1}, regex_type);
    const auto loop = string_builtin_app(
      ID_cprover_regex_loop_func,
      {re1, from_integer(2, int_type), from_integer(5, int_type)},
      regex_type);
    const auto in = string_builtin_app(
      ID_cprover_string_in_regex_func, {s1, loop}, bool_typet{});
    REQUIRE(
      get_assert(in) ==
      "(assert (str.in_re s1 ((_ re.loop 2 5) (str.to_re s1))))");
  }

  SECTION("refined-string (array) operand is rejected by the soundness guard")
  {
    // An application carrying the refined-string (char-array) representation
    // must not be lowered natively here -- it requires --refine-strings.
    const array_typet char_array{
      unsignedbv_typet{8}, from_integer(4, size_type())};
    const symbol_exprt arr{"arr", char_array};
    const auto contains = string_builtin_app(
      ID_cprover_string_contains_func, {arr, s2}, bool_typet{});
    REQUIRE_THROWS(get_assert(contains));
  }
}

TEST_CASE(
  "smt2_convt mathematical integer div/mod truncate toward zero",
  "[core][solvers][smt2]")
{
  const typet string_type{ID_string};
  const typet int_type{ID_integer};
  const symbol_exprt s1{"s1", string_type};

  // Wrap the (Int-returning) div/mod inside a boolean str.contains so set_to
  // emits a plain assertion we can pin exactly.
  auto in_str = [&](const exprt &idx)
  {
    const auto at = string_builtin_app(
      ID_cprover_string_char_at_func, {s1, idx}, string_type);
    return string_builtin_app(
      ID_cprover_string_contains_func, {at, s1}, bool_typet{});
  };

  SECTION("integer div truncates toward zero ((-3) div 2 is -1, not -2)")
  {
    const div_exprt d{from_integer(-3, int_type), from_integer(2, int_type)};
    REQUIRE(
      get_assert(in_str(d)) ==
      "(assert (str.contains (str.at s1 (let ((?da (- 3)) (?db 2)) (let ((?dq "
      "(div (ite (< ?da 0) (- ?da) ?da) (ite (< ?db 0) (- ?db) ?db)))) (ite (= "
      "(< ?da 0) (< ?db 0)) ?dq (- ?dq))))) s1))");
  }

  SECTION("integer mod takes the sign of the dividend ((-3) mod 2 is -1)")
  {
    const mod_exprt m{from_integer(-3, int_type), from_integer(2, int_type)};
    REQUIRE(
      get_assert(in_str(m)) ==
      "(assert (str.contains (str.at s1 (let ((?ma (- 3)) (?mb 2)) (let ((?mr "
      "(mod (ite (< ?ma 0) (- ?ma) ?ma) (ite (< ?mb 0) (- ?mb) ?mb)))) (ite (< "
      "?ma 0) (- ?mr) ?mr)))) s1))");
  }

  SECTION("natural div/mod use plain SMT-LIB div/mod")
  {
    const typet nat_type{ID_natural};
    const div_exprt d{from_integer(7, nat_type), from_integer(3, nat_type)};
    REQUIRE(
      get_assert(in_str(d)) ==
      "(assert (str.contains (str.at s1 (div 7 3)) s1))");
    const mod_exprt m{from_integer(7, nat_type), from_integer(3, nat_type)};
    REQUIRE(
      get_assert(in_str(m)) ==
      "(assert (str.contains (str.at s1 (mod 7 3)) s1))");
  }
}

TEST_CASE(
  "smt2_convt declares a regex-typed value with the RegLan sort",
  "[core][solvers][smt2]")
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  std::ostringstream out;
  smt2_convt conv(ns, "test", "", "QF_BV", smt2_convt::solvert::GENERIC, out);
  const symbol_exprt s{"s", typet{ID_string}};
  const symbol_exprt re{"re", typet{ID_regex}};
  const auto in =
    string_builtin_app(ID_cprover_string_in_regex_func, {s, re}, bool_typet{});
  conv.set_to(in, true);
  REQUIRE(out.str().find("RegLan") != std::string::npos);
}

/// Subclass exposing the protected \ref smt2_convt::walk_array_tree method so
/// the array-model parse direction can be exercised directly.
class array_tree_smt2_convt : public smt2_convt
{
public:
  using smt2_convt::smt2_convt;
  using smt2_convt::walk_array_tree;
};

/// Helper: build an irept node carrying just an id.
static irept smt_node(const irep_idt &id)
{
  irept node;
  node.id(id);
  return node;
}

TEST_CASE(
  "smt2_convt::walk_array_tree skips non-constant store indices",
  "[core][solvers][smt2]")
{
  // A solver may return an array model whose store term carries a
  // non-constant index (e.g. for unbounded or non-integer-keyed arrays).
  // walk_array_tree must skip such an entry rather than abort in
  // to_constant_expr, while still collecting the well-formed entries.
  //
  // Put invariants into throwing mode: without the is_constant() guard,
  // to_constant_expr fails via an INVARIANT that aborts the unit binary by
  // default; throwing mode turns that into an exception REQUIRE_NOTHROW can
  // report as a clean test failure.
  const cbmc_invariants_should_throwt invariants_throw;

  // The index is parsed against type.size().type(); a bool-typed size makes
  // a plain symbol index parse to a non-constant (nil) expression, which is
  // the case the guard handles. (parse_rec coerces arithmetic index types to
  // constants, so a non-constant index can only arise from a non-arithmetic
  // index type.)
  const signedbv_typet element_type{32};
  const array_typet array_type{element_type, symbol_exprt{"n", bool_typet{}}};

  // (as const <type> 0): a well-formed default entry, collected at index -1
  // without going through index parsing.
  irept as_const_header;
  as_const_header.get_sub().push_back(smt_node("as"));
  as_const_header.get_sub().push_back(smt_node("const"));
  as_const_header.get_sub().push_back(irept{}); // type info, unused here
  irept as_const_node;
  as_const_node.get_sub().push_back(as_const_header);
  as_const_node.get_sub().push_back(smt_node("0")); // default value 0

  // (store (as const <type> 0) x 7): the index "x" is a plain symbol, so it
  // parses to a non-constant under the bool-typed index type and must be
  // dropped.
  irept store_node;
  store_node.get_sub().push_back(smt_node("store"));
  store_node.get_sub().push_back(as_const_node);
  store_node.get_sub().push_back(smt_node("x")); // non-constant index
  store_node.get_sub().push_back(smt_node("7")); // value, must not survive

  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  std::ostringstream out;
  array_tree_smt2_convt conv{
    ns, "test", "", "QF_BV", smt2_convt::solvert::GENERIC, out};

  std::unordered_map<int64_t, exprt> operands_map;
  REQUIRE_NOTHROW(conv.walk_array_tree(&operands_map, store_node, array_type));

  // The non-constant store was dropped; only the well-formed default remains.
  REQUIRE(operands_map.size() == 1);
  REQUIRE(operands_map.count(-1) == 1);
}
