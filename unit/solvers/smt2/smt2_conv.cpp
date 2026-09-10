// Author: Diffblue Ltd.

/// \file
/// Unit tests for smt2_convt

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <solvers/smt2/smt2_conv.h>
#include <solvers/smt2/smt2_dec.h>
#include <testing-utils/use_catch.h>

namespace
{
/// Expose the existing response reader to supply solver protocol fixtures.
class smt2_result_testt : public smt2_dect
{
public:
  using smt2_dect::read_result;
  using smt2_dect::smt2_dect;
};
} // namespace

TEST_CASE(
  "SMT model queries preserve the identifier set",
  "[core][solvers][smt2]")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  const auto solver = GENERATE(
    smt2_convt::solvert::Z3,
    smt2_convt::solvert::GENERIC,
    smt2_convt::solvert::BITWUZLA,
    smt2_convt::solvert::BOOLECTOR,
    smt2_convt::solvert::CPROVER_SMT2,
    smt2_convt::solvert::CVC5,
    smt2_convt::solvert::MATHSAT,
    smt2_convt::solvert::YICES);
  std::ostringstream output;
  smt2_convt converter{ns, "queries", "", "ALL", solver, output};
  std::string expected;
  SECTION("Empty")
  {
    // Q1: no identifiers means no model request, including no empty Z3 query.
  }
  SECTION("Singleton")
  {
    // Q2: one identifier keeps exactly the previous singleton request.
    const symbol_exprt x{"x", unsignedbv_typet{8}};
    converter.set_to(equal_exprt{x, from_integer(1, x.type())}, true);
    expected = "(get-value (x))\n";
  }
  SECTION("Multiple, including escaped identifier")
  {
    // Q3: Z3 batches every identifier in the existing sorted set once;
    // Q4: other solvers retain singleton commands, and Boolector retains none.
    // Deliberately discover the symbols out of order and include an escaped id.
    for(const auto &name : {"x|y", "z", "a"})
    {
      const symbol_exprt x{name, unsignedbv_typet{8}};
      converter.set_to(equal_exprt{x, from_integer(1, x.type())}, true);
    }
    expected = solver == smt2_convt::solvert::Z3
                 ? "(get-value (a z |x&124;y|))\n"
                 : "(get-value (a))\n(get-value (z))\n"
                   "(get-value (|x&124;y|))\n";
  }
  if(solver == smt2_convt::solvert::BOOLECTOR)
    expected.clear();
  CHECK(converter() == decision_proceduret::resultt::D_ERROR);
  const auto text = output.str();
  const auto check = text.find("(check-sat)\n");
  REQUIRE(check != std::string::npos);
  CHECK(
    text.substr(check) ==
    "(check-sat)\n\n" + expected + "\n(exit)\n; end of SMT2 file\n");
}

TEST_CASE(
  "SMT model responses decode every typed value",
  "[core][solvers][smt2]")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  null_message_handlert messages;
  smt2_result_testt solver{
    ns, "results", "", "ALL", smt2_convt::solvert::Z3, "", messages};
  const unsignedbv_typet byte{8};
  const symbol_exprt x{"x|y", byte};
  const symbol_exprt empty_name{"", byte};
  const symbol_exprt number{"number", integer_typet{}};
  const struct_typet record_type{{{"field", byte}}};
  const symbol_exprt record{"record", record_type};
  const array_typet array_type{byte, from_integer(2, unsignedbv_typet{64})};
  const symbol_exprt array{"array", array_type};
  solver.set_to(equal_exprt{x, from_integer(42, byte)}, true);
  solver.set_to(equal_exprt{empty_name, from_integer(9, byte)}, true);
  solver.set_to(equal_exprt{number, from_integer(-10, number.type())}, true);
  solver.set_to(
    equal_exprt{record, struct_exprt{{from_integer(3, byte)}, record_type}},
    true);
  solver.set_to(
    equal_exprt{array, array_of_exprt{from_integer(7, byte), array_type}},
    true);
  const auto yes = solver.handle(equal_exprt{x, from_integer(42, byte)});
  const auto no =
    solver.handle(equal_exprt{number, from_integer(0, number.type())});

  // Q5/Q6: singleton and multiline batched responses must produce the same
  // actual values. Reordered pairs, quoted/escaped ids, both Boolean values,
  // the legal empty quoted identifier, indexed bitvectors, negative integers,
  // arrays and structs all use the
  // original parsed_values map and typed parse_rec implementation.
  const std::vector<std::string> pairs{
    "(B1 false)",
    "(|| #x09)",
    "(array ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07))",
    "(|x&124;y| (_ bv42 8))",
    "(record (mk-struct.0 #x03))",
    "(B0 true)",
    "(number (- 10))"};
  std::string response = "sat\n";
  SECTION("Singleton responses")
  {
    for(const auto &pair : pairs)
      response += "(" + pair + ")\n";
  }
  SECTION("Batched response")
  {
    response += "(\n";
    for(const auto &pair : pairs)
      response += pair + "\n";
    response += ")\n";
  }
  std::istringstream input{response};
  REQUIRE(
    solver.read_result(input) == decision_proceduret::resultt::D_SATISFIABLE);
  CHECK(solver.get(x) == from_integer(42, byte));
  CHECK(solver.get(empty_name) == from_integer(9, byte));
  CHECK(solver.get(number) == from_integer(-10, number.type()));
  CHECK(
    solver.get(record) == struct_exprt{{from_integer(3, byte)}, record_type});
  CHECK(
    solver.get(array) ==
    array_exprt{{from_integer(7, byte), from_integer(7, byte)}, array_type});
  CHECK(solver.get(yes) == true_exprt{});
  CHECK(solver.get(no) == false_exprt{});
}

TEST_CASE(
  "SMT model response failures do not become SAT",
  "[core][solvers][smt2]")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  null_message_handlert messages;
  smt2_result_testt solver{
    ns, "results", "", "ALL", smt2_convt::solvert::Z3, "", messages};
  const auto response = GENERATE(
    "sat\n(error \"model unavailable\")\n",
    "unknown\n",
    "sat\n()\n",
    "sat\n((x #x01) (broken) (y #x02))\n",
    "sat\n((x #x01) (y #x02 extra))\n",
    "sat\n((x #x01) ((bad name) #x02))\n",
    "sat\n((x #x01) (y #x02)\n",
    "sat\n((x #x01))\n)\n");
  // Q7: SAT errors and UNKNOWN are failures as before. Q8: malformed middle
  // or last pairs, empty lists and syntax errors also fail, even after valid
  // values or SAT were parsed. Never return a partially accepted model.
  std::istringstream input{response};
  CHECK(solver.read_result(input) == decision_proceduret::resultt::D_ERROR);
}

TEST_CASE(
  "SMT model status and Boolean fallback remain compatible",
  "[core][solvers][smt2]")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  null_message_handlert messages;
  smt2_result_testt solver{
    ns, "results", "", "ALL", smt2_convt::solvert::Z3, "", messages};
  SECTION("UNSAT ignores later model errors")
  {
    // Q9: no model exists after UNSAT; retain the existing error exemption.
    std::istringstream input{"unsat\n(error \"model unavailable\")\n"};
    CHECK(
      solver.read_result(input) ==
      decision_proceduret::resultt::D_UNSATISFIABLE);
  }
  SECTION("Historical diagnostics do not invalidate a clean response")
  {
    // Q10: syntax-error detection compares the current parser call's error
    // count, not unrelated diagnostics previously sent to the shared handler.
    messaget log{messages};
    log.error() << "earlier diagnostic" << messaget::eom;
    std::istringstream input{"sat\n"};
    CHECK(
      solver.read_result(input) == decision_proceduret::resultt::D_SATISFIABLE);
  }
  SECTION("Missing typed value")
  {
    // Q11: a required typed identifier cannot silently parse an absent value.
    const symbol_exprt x{"x", unsignedbv_typet{8}};
    solver.set_to(equal_exprt{x, from_integer(1, x.type())}, true);
    std::istringstream input{"sat\n"};
    CHECK(solver.read_result(input) == decision_proceduret::resultt::D_ERROR);
  }
  SECTION("Missing Boolean without fallback")
  {
    // Q12: a missing solver Boolean must not default to false.
    const symbol_exprt x{"x", unsignedbv_typet{8}};
    solver.handle(equal_exprt{x, from_integer(1, x.type())});
    std::istringstream input{"sat\n((x #x01))\n"};
    CHECK(solver.read_result(input) == decision_proceduret::resultt::D_ERROR);
  }
  SECTION("Missing Boolean with set_to fallback")
  {
    // Q13: the established set_to fallback remains valid for a literal whose
    // value is already fixed by an assertion; no model value is invented.
    const symbol_exprt x{"x", unsignedbv_typet{8}};
    const equal_exprt expression{x, from_integer(1, x.type())};
    const auto literal = solver.handle(expression);
    solver.set_to(expression, true);
    std::istringstream input{"sat\n((x #x01))\n"};
    REQUIRE(
      solver.read_result(input) == decision_proceduret::resultt::D_SATISFIABLE);
    CHECK(solver.get(literal) == true_exprt{});
  }
}

TEST_CASE(
  "SMT missing-value handling for other solvers is unchanged",
  "[core][solvers][smt2]")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  null_message_handlert messages;
  const auto backend =
    GENERATE(smt2_convt::solvert::BOOLECTOR, smt2_convt::solvert::GENERIC);
  smt2_result_testt solver{ns, "results", "", "ALL", backend, "", messages};
  const symbol_exprt x{"x", unsignedbv_typet{8}};
  solver.set_to(equal_exprt{x, from_integer(1, x.type())}, true);

  // Q15: smt2_identifiers is not a request receipt for every backend:
  // Boolector never emits get-value. The new missing-requested-value failure
  // is limited to Z3; preserve other backends' existing result handling.
  std::istringstream input{"sat\n"};
  CHECK(
    solver.read_result(input) == decision_proceduret::resultt::D_SATISFIABLE);
}

TEST_CASE(
  "SMT other solver responses retain singleton and extra-model handling",
  "[core][solvers][smt2]")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  null_message_handlert messages;
  const auto backend =
    GENERATE(smt2_convt::solvert::BOOLECTOR, smt2_convt::solvert::GENERIC);
  smt2_result_testt solver{ns, "results", "", "ALL", backend, "", messages};
  const symbol_exprt x{"x", unsignedbv_typet{8}};
  solver.set_to(equal_exprt{x, from_integer(42, x.type())}, true);
  std::string response = "sat\n((x #x2a))\n";
  SECTION("Additional model list")
  {
    // Q16: a non-Z3 solver can emit an extra model list. Preserve the old
    // unknown-list handling and the actual value read from its singleton.
    response += "(model (define-fun x () (_ BitVec 8) #x2a))\n";
  }
  SECTION("Historical syntax-error behavior")
  {
    // Q17: this patch's new syntax-error rejection is scoped to Z3 batching;
    // do not change other solvers' existing EOF/error interpretation here.
    response += "(";
  }
  std::istringstream input{response};
  REQUIRE(
    solver.read_result(input) == decision_proceduret::resultt::D_SATISFIABLE);
  CHECK(solver.get(x) == from_integer(42, x.type()));
}

TEST_CASE("Z3 batched model values retain their assignments", "[smt2][z3]")
{
  // Q18: multiple differently typed, constrained symbols trigger one model
  // request. A real Z3 response must recover each value, including both
  // Boolean outcomes. This exercises generation, transport and decoding.
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  null_message_handlert messages;
  smt2_dect solver{
    ns, "batch", "", "ALL", smt2_convt::solvert::Z3, "", messages};
  const symbol_exprt x{"x|y", unsignedbv_typet{8}};
  const symbol_exprt number{"number", integer_typet{}};
  const equal_exprt condition{x, from_integer(42, x.type())};
  const auto yes = solver.handle(condition);
  const auto no =
    solver.handle(equal_exprt{number, from_integer(0, number.type())});
  solver.set_to(condition, true);
  solver.set_to(equal_exprt{number, from_integer(-10, number.type())}, true);
  REQUIRE(solver() == decision_proceduret::resultt::D_SATISFIABLE);
  CHECK(solver.get(x) == from_integer(42, x.type()));
  CHECK(solver.get(number) == from_integer(-10, number.type()));
  CHECK(solver.get(yes) == true_exprt{});
  CHECK(solver.get(no) == false_exprt{});
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
