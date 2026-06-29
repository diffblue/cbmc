// Author: Diffblue Ltd.

/// \file
/// Unit tests for smt2_convt

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/ieee_float.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <solvers/smt2/smt2_conv.h>
#include <solvers/smt2/smt2_dec.h>
#include <testing-utils/use_catch.h>

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
