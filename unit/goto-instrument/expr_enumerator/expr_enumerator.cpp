/*******************************************************************\

Module: Tests for Expression Enumerator

Author: Qinheping Hu

\*******************************************************************/

#include <util/c_types.h>
#include <util/format_expr.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/symbol_table.h>

#include <goto-instrument/synthesizer/expr_enumerator.h>
#include <testing-utils/use_catch.h>

TEST_CASE("enumeratingsummation expressions", "[core]")
{
  int num_var = 3;

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  symbolt a0_symbol;
  a0_symbol.base_name = "a0";
  a0_symbol.name = "a0";
  a0_symbol.type = size_type();
  a0_symbol.is_lvalue = true;
  symbol_table.add(a0_symbol);

  symbolt a1_symbol;
  a1_symbol.base_name = "a1";
  a1_symbol.name = "a1";
  a1_symbol.type = size_type();
  a1_symbol.is_lvalue = true;
  symbol_table.add(a1_symbol);

  symbolt a2_symbol;
  a2_symbol.base_name = "a2";
  a2_symbol.name = "a2";
  a2_symbol.type = size_type();
  a2_symbol.is_lvalue = true;
  symbol_table.add(a2_symbol);

  // Initialize factory representing grammar
  // Start -> Start + Start | a0 | a1 |a2
  // where a0, a1, and a2 are symbol expressions.
  enumerator_factoryt factory = enumerator_factoryt(ns);
  recursive_enumerator_placeholdert start_ph(factory, "Start", ns);

  enumeratorst start_args;

  // a0 | a1 | a2
  expr_sett leafexprs;
  for(int i = 0; i < num_var; i++)
  {
    leafexprs.insert(symbol_exprt("a" + std::to_string(i), size_type()));
  }
  leaf_enumeratort leaf_g(leafexprs, ns);
  start_args.push_back(&leaf_g);

  // Start + Start
  // Optimization: restrict enumerated expressions to be
  // right linear regular---the lambada expression.
  binary_functional_enumeratort plus_g(
    ID_plus,
    start_ph,
    start_ph,
    [](const partitiont &partition) {
      if(partition.size() <= 1)
        return true;
      return partition.front() == 1;
    },
    ns);
  start_args.push_back(&plus_g);

  factory.attach_productions("Start", start_args);

  // enumerate expressions with size `size_term`.
  unsigned int size_term = 5;
  expr_sett result = start_ph.enumerate(size_term);
  std::list<std::string> result_str;

  for(const auto &e : result)
  {
    std::stringstream ss;
    ss << format(e);
    result_str.push_back(ss.str());
  }

  // there are 10 summation expressions with size 5 and 3 variables.
  REQUIRE(result.size() == 10);
  REQUIRE(
    std::find(result_str.begin(), result_str.end(), "a0 + a0 + a0") !=
    result_str.end());
  REQUIRE(
    std::find(result_str.begin(), result_str.end(), "a0 + a0 + a1") !=
    result_str.end());
  REQUIRE(
    std::find(result_str.begin(), result_str.end(), "a0 + a1 + a1") !=
    result_str.end());
  REQUIRE(
    std::find(result_str.begin(), result_str.end(), "a1 + a1 + a1") !=
    result_str.end());
  REQUIRE(
    std::find(result_str.begin(), result_str.end(), "a0 + a0 + a2") !=
    result_str.end());
  REQUIRE(
    std::find(result_str.begin(), result_str.end(), "a0 + a1 + a2") !=
    result_str.end());
  REQUIRE(
    std::find(result_str.begin(), result_str.end(), "a1 + a1 + a2") !=
    result_str.end());
  REQUIRE(
    std::find(result_str.begin(), result_str.end(), "a0 + a2 + a2") !=
    result_str.end());
  REQUIRE(
    std::find(result_str.begin(), result_str.end(), "a1 + a2 + a2") !=
    result_str.end());
  REQUIRE(
    std::find(result_str.begin(), result_str.end(), "a2 + a2 + a2") !=
    result_str.end());
}

TEST_CASE("predicate expression enumeration", "[core]")
{
  size_t size_term = 9;

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  symbolt a1_symbol;
  a1_symbol.base_name = "a1";
  a1_symbol.name = "a1";
  a1_symbol.type = size_type();
  a1_symbol.is_lvalue = true;
  symbol_table.add(a1_symbol);

  symbolt a0_symbol;
  a0_symbol.base_name = "a0";
  a0_symbol.name = "a0";
  a0_symbol.type = size_type();
  a0_symbol.is_lvalue = true;
  symbol_table.add(a0_symbol);

  // Initialize factory representing grammar
  // StartBool -> StartBool && StartBool | Start == Start
  // Start -> Start + Start | a0 | a1
  // where a0, and a1 are symbol expressions.
  enumerator_factoryt factory = enumerator_factoryt(ns);
  recursive_enumerator_placeholdert start_bool_ph(factory, "StartBool", ns);
  recursive_enumerator_placeholdert start_ph(factory, "Start", ns);

  // Start -> a0 | a1
  expr_sett leafexprs;
  symbol_exprt a_0("a0", size_type());
  symbol_exprt a_1("a1", size_type());
  leafexprs.insert(a_0);
  leafexprs.insert(a_1);

  enumeratorst start_args;
  leaf_enumeratort leaf_g(leafexprs, ns);
  start_args.push_back(&leaf_g);

  // Start -> Start + Start
  binary_functional_enumeratort plus_g(
    ID_plus,
    start_ph,
    start_ph,
    [](const partitiont &partition) {
      if(partition.size() <= 1)
        return true;
      return partition.front() == 1;
    },
    ns);
  start_args.push_back(&plus_g);

  // StartBool -> StartBool && StartBool | Start == Start
  enumeratorst start_bool_args;
  binary_functional_enumeratort and_g(ID_and, start_bool_ph, start_bool_ph, ns);
  start_bool_args.push_back(&and_g);
  binary_functional_enumeratort equal_g(ID_equal, start_ph, start_ph, ns);
  start_bool_args.push_back(&equal_g);

  factory.attach_productions("Start", start_args);
  factory.attach_productions("StartBool", start_bool_args);

  expr_sett result = start_bool_ph.enumerate(size_term);

  // Enumerated 16 expressions.
  REQUIRE(result.size() == 16);

  // a0 + a0 == a1 + a1 + a1
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(
        equal_exprt(
          plus_exprt(a_0, a_0), plus_exprt(a_1, plus_exprt(a_1, a_1))),
        ns)) != result.end());

  // a0 + a0 == a1
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(equal_exprt(plus_exprt(a_0, a_0), a_1), ns)) !=
    result.end());

  // a0 + a0 + a0 == a1 + a1
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(
        equal_exprt(
          plus_exprt(a_0, plus_exprt(a_0, a_0)), plus_exprt(a_1, a_1)),
        ns)) != result.end());

  // a0 + a0 + a0 == 0ul
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(
        equal_exprt(
          plus_exprt(a_0, plus_exprt(a_0, a_0)),
          constant_exprt("0", size_type())),
        ns)) != result.end());

  // a0 + a0 + a1 == 0ul
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(
        equal_exprt(
          plus_exprt(a_0, plus_exprt(a_0, a_1)),
          constant_exprt("0", size_type())),
        ns)) != result.end());

  // a0 + a1 + a1 == 0ul
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(
        equal_exprt(
          plus_exprt(a_0, plus_exprt(a_1, a_1)),
          constant_exprt("0", size_type())),
        ns)) != result.end());

  // a1 + a1 + a1 == 0ul
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(
        equal_exprt(
          plus_exprt(a_1, plus_exprt(a_1, a_1)),
          constant_exprt("0", size_type())),
        ns)) != result.end());

  // a0 + a0 + a0 + a0 == a1
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(
        equal_exprt(
          plus_exprt(a_0, plus_exprt(a_0, plus_exprt(a_0, a_0))), a_1),
        ns)) != result.end());

  // a0 == a1 + a1
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(equal_exprt(a_0, plus_exprt(a_1, a_1)), ns)) !=
    result.end());

  // a0 == a1 + a1 + a1 + a1
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(
        equal_exprt(
          a_0, plus_exprt(a_1, plus_exprt(a_1, plus_exprt(a_1, a_1)))),
        ns)) != result.end());

  // a0 == 0ul
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(equal_exprt(a_0, constant_exprt("0", size_type())), ns)) !=
    result.end());

  // a1 == 0ul
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(equal_exprt(a_0, constant_exprt("0", size_type())), ns)) !=
    result.end());

  // a0 + a0 == a1 && a0 == a1
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(
        and_exprt(
          equal_exprt(plus_exprt(a_0, a_0), a_1), equal_exprt(a_0, a_1)),
        ns)) != result.end());

  // a0 == 0ul && a0 == a1
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(
        and_exprt(
          equal_exprt(a_0, constant_exprt("0", size_type())),
          equal_exprt(a_0, a_1)),
        ns)) != result.end());

  // a0 == a1 && a0 == a1 + a1
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(
        and_exprt(
          equal_exprt(a_0, a_1), equal_exprt(a_0, plus_exprt(a_1, a_1))),
        ns)) != result.end());

  // a0 == a1 && a1 == 0
  REQUIRE(
    std::find(
      result.begin(),
      result.end(),
      simplify_expr(
        and_exprt(
          equal_exprt(a_0, a_1),
          equal_exprt(a_1, constant_exprt("0", size_type()))),
        ns)) != result.end());
}
