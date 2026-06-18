// Author: Diffblue Ltd.

/// \file
/// Unit tests for smt2_convt

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/ieee_float.h>
#include <util/mathematical_types.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <solvers/smt2/smt2_conv.h>
#include <solvers/smt2/smt2_dec.h>
#include <testing-utils/invariant.h>
#include <testing-utils/use_catch.h>

// Build a synthetic multi-constructor ADT struct_typet of the kind the Strata
// front end produces: a leading $tag discriminant followed by the union of all
// constructors' fields, plus a #adt_constructors annotation describing each
// constructor's name and field list.
static struct_typet build_adt_type()
{
  const unsignedbv_typet u32{32};
  struct_typet::componentst components;
  components.emplace_back("$tag", u32);
  components.emplace_back("value", u32); // field of constructor from_int
  struct_typet adt{std::move(components)};
  adt.set_tag("myadt");

  irept ctors;
  // constructor 0: nil, no fields
  irept ctor0;
  ctor0.add(ID_name).id("nil");
  ctor0.add(irep_idt("fields"));
  // constructor 1: from_int, field "value"
  irept ctor1;
  ctor1.add(ID_name).id("from_int");
  irept field_value;
  field_value.id("value");
  ctor1.add(irep_idt("fields")).get_sub().push_back(field_value);
  ctors.get_sub().push_back(ctor0);
  ctors.get_sub().push_back(ctor1);
  adt.add(irep_idt("#adt_constructors")) = ctors;
  return adt;
}

static std::string adt_smt2(const exprt &expr)
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  std::ostringstream out;
  // Z3 enables use_datatypes.
  smt2_convt conv(ns, "test", "", "QF_AUFBV", smt2_convt::solvert::Z3, out);
  conv.set_to(expr, true);
  return out.str();
}

// Count the number of "(declare-datatypes" declarations in \p smt2.
static std::size_t count_datatype_decls(const std::string &smt2)
{
  std::size_t count = 0;
  const std::string marker = "(declare-datatypes";
  for(std::size_t pos = smt2.find(marker); pos != std::string::npos;
      pos = smt2.find(marker, pos + 1))
    ++count;
  return count;
}

// An ordinary (single-constructor) struct with a tag and a single array member,
// used to exercise the same-tag datatype reuse in find_symbols_rec.
static struct_typet make_tagged_array_struct(
  const irep_idt &tag,
  const typet &element,
  std::size_t size)
{
  struct_typet::componentst components;
  components.emplace_back(
    "arr", array_typet{element, from_integer(size, size_type())});
  struct_typet st{std::move(components)};
  st.set_tag(tag);
  return st;
}

TEST_CASE(
  "smt2_convt multi-constructor ADT datatype encoding",
  "[core][solvers][smt2]")
{
  const struct_typet adt = build_adt_type();
  const unsignedbv_typet u32{32};
  const symbol_exprt s{"s", adt};

  SECTION("declaration and constant-tag construction")
  {
    const std::string out = adt_smt2(equal_exprt{
      s, struct_exprt{{from_integer(1, u32), from_integer(7, u32)}, adt}});
    CHECK(
      out.find("(declare-datatypes ((struct.0 0)) (((nil) (from_int "
               "(struct.0.value (_ BitVec 32))) )))") != std::string::npos);
    CHECK(out.find("(from_int (_ bv7 32))") != std::string::npos);
  }

  SECTION("non-constant-tag construction uses a well-sorted tag comparison")
  {
    const symbol_exprt t{"t", u32};
    const std::string out =
      adt_smt2(equal_exprt{s, struct_exprt{{t, from_integer(7, u32)}, adt}});
    // the tag is compared against a bit-vector literal, not a bare numeral
    CHECK(out.find("(= t (_ bv0 32))") != std::string::npos);
    CHECK(out.find("(= t 0)") == std::string::npos);
  }

  SECTION("$tag member access yields well-sorted index literals")
  {
    const std::string out =
      adt_smt2(equal_exprt{member_exprt{s, "$tag", u32}, from_integer(1, u32)});
    CHECK(
      out.find("(ite ((_ is nil) s) (_ bv0 32) (_ bv1 32))") !=
      std::string::npos);
  }

  SECTION("field member access uses the per-field selector")
  {
    const std::string out = adt_smt2(
      equal_exprt{member_exprt{s, "value", u32}, from_integer(7, u32)});
    CHECK(out.find("(struct.0.value s)") != std::string::npos);
  }

  SECTION("with on a field rebuilds each constructor")
  {
    exprt where{ID_member_name};
    where.set(ID_component_name, "value");
    const std::string out =
      adt_smt2(equal_exprt{s, with_exprt{s, where, from_integer(9, u32)}});
    CHECK(out.find("(from_int (_ bv9 32))") != std::string::npos);
  }

  SECTION("with on $tag is rejected")
  {
    exprt where{ID_member_name};
    where.set(ID_component_name, "$tag");
    const cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS_MATCHES(
      adt_smt2(equal_exprt{s, with_exprt{s, where, from_integer(0, u32)}}),
      invariant_failedt,
      invariant_failure_containing("with on the constructor tag"));
  }
}

TEST_CASE(
  "smt2_convt ADT constructors must not share field names",
  "[core][solvers][smt2]")
{
  const unsignedbv_typet u32{32};
  struct_typet::componentst components;
  components.emplace_back("$tag", u32);
  components.emplace_back("v", u32);
  struct_typet adt{std::move(components)};
  adt.set_tag("dup");

  irept ctors;
  for(const auto name : {"C0", "C1"})
  {
    irept ctor;
    ctor.add(ID_name).id(name);
    irept field;
    field.id("v"); // both constructors declare a field named "v"
    ctor.add(irep_idt("fields")).get_sub().push_back(field);
    ctors.get_sub().push_back(ctor);
  }
  adt.add(irep_idt("#adt_constructors")) = ctors;

  const symbol_exprt s{"s", adt};
  const cbmc_invariants_should_throwt invariants_throw;
  REQUIRE_THROWS_MATCHES(
    adt_smt2(equal_exprt{member_exprt{s, "v", u32}, from_integer(0, u32)}),
    invariant_failedt,
    invariant_failure_containing("must not share field names"));
}

TEST_CASE(
  "smt2_convt same-tag struct datatype reuse compares component sorts",
  "[core][solvers][smt2]")
{
  const signedbv_typet i32{32};
  const signedbv_typet i64{64};

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  auto emit_two = [&](const struct_typet &a, const struct_typet &b)
  {
    std::ostringstream out;
    smt2_convt conv(ns, "test", "", "QF_AUFBV", smt2_convt::solvert::Z3, out);
    conv.set_to(
      and_exprt{
        equal_exprt{symbol_exprt{"a", a}, symbol_exprt{"a2", a}},
        equal_exprt{symbol_exprt{"b", b}, symbol_exprt{"b2", b}}},
      true);
    return out.str();
  };

  SECTION("differing array sizes share one datatype")
  {
    const std::string out = emit_two(
      make_tagged_array_struct("S", i32, 4),
      make_tagged_array_struct("S", i32, 8));
    CHECK(count_datatype_decls(out) == 1);
  }

  SECTION("differing element types use separate datatypes")
  {
    const std::string out = emit_two(
      make_tagged_array_struct("S", i32, 4),
      make_tagged_array_struct("S", i64, 4));
    CHECK(count_datatype_decls(out) == 2);
  }
}

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
