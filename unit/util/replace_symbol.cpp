/*******************************************************************\

Module: replace_symbolt unit tests

Author: Michael Tautschnig

\*******************************************************************/

#include <util/mathematical_expr.h>
#include <util/pointer_expr.h>
#include <util/replace_symbol.h>
#include <util/std_expr.h>

#include <testing-utils/use_catch.h>

TEST_CASE("Replace all symbols in expression", "[core][util][replace_symbol]")
{
  symbol_exprt s1("a", typet("some_type"));
  symbol_exprt s2("b", typet("some_type"));

  binary_exprt binary(s1, "binary", s2, typet("some_type"));

  array_typet array_type(typet("sub-type"), s1);
  REQUIRE(array_type.size() == s1);

  exprt other_expr("other", typet("some_type"));

  replace_symbolt r;
  REQUIRE(r.empty());

  r.insert(s1, other_expr);
  REQUIRE(r.replaces_symbol("a"));
  REQUIRE(r.get_expr_map().size() == 1);

  REQUIRE(!r.replace(binary));
  REQUIRE(binary.op0() == other_expr);

  REQUIRE(!r.replace(s1));
  REQUIRE(s1 == other_expr);

  REQUIRE(r.replace(s2));
  REQUIRE(s2 == symbol_exprt("b", typet("some_type")));

  REQUIRE(!r.replace(array_type));
  REQUIRE(array_type.size() == other_expr);

  REQUIRE(r.erase("a") == 1);
  REQUIRE(r.empty());
}

TEST_CASE("Lvalue only", "[core][util][replace_symbol]")
{
  symbol_exprt s1("a", typet("some_type"));
  array_typet array_type(typet("some_type"), s1);
  symbol_exprt array("b", array_type);
  index_exprt index(array, s1);

  binary_exprt binary(
    address_of_exprt(s1),
    "binary",
    address_of_exprt(index),
    typet("some_type"));

  constant_exprt c("some_value", typet("some_type"));

  address_of_aware_replace_symbolt r;
  r.insert(s1, c);

  REQUIRE(!r.replace(binary));
  REQUIRE(binary.op0() == address_of_exprt(s1));
  const index_exprt &index_expr =
    to_index_expr(to_address_of_expr(binary.op1()).object());
  REQUIRE(to_array_type(index_expr.array().type()).size() == c);
  REQUIRE(index_expr.index() == c);

  address_of_exprt address_of(s1);
  r.erase("a");
  r.insert(s1, address_of);

  REQUIRE(r.replace(binary));
  REQUIRE(binary.op0() == address_of_exprt(s1));
}

TEST_CASE("Replace always", "[core][util][replace_symbol]")
{
  symbol_exprt s1("a", typet("some_type"));
  array_typet array_type(typet("some_type"), s1);
  symbol_exprt array("b", array_type);
  index_exprt index(array, s1);

  binary_exprt binary(
    address_of_exprt(s1),
    "binary",
    address_of_exprt(index),
    typet("some_type"));

  constant_exprt c("some_value", typet("some_type"));

  unchecked_replace_symbolt r;
  r.insert(s1, c);

  REQUIRE(!r.replace(binary));
  REQUIRE(binary.op0() == address_of_exprt(c));
  const index_exprt &index_expr =
    to_index_expr(to_address_of_expr(binary.op1()).object());
  REQUIRE(to_array_type(index_expr.array().type()).size() == c);
  REQUIRE(index_expr.index() == c);
}

TEST_CASE("Let expression hides bound variable", "[core][util][replace_symbol]")
{
  const typet t{"some_type"};
  const symbol_exprt x{"x", t};
  const symbol_exprt y{"y", t};
  const constant_exprt replacement{"val", t};

  // let x = y in x + y
  const binary_exprt body{x, "plus", y, t};
  const let_exprt let{x, y, body};

  replace_symbolt r;
  r.insert(x, replacement);
  r.insert(y, replacement);

  exprt result = let;
  // replacements happen, so return value is false
  REQUIRE(!r.replace(result));

  const auto &result_let = to_let_expr(result);
  // the value expression (y) is replaced
  REQUIRE(result_let.value() == replacement);
  // in the body, x is bound and must NOT be replaced
  const auto &result_body = result_let.where();
  REQUIRE(result_body.operands().size() == 2);
  REQUIRE(result_body.operands()[0] == x);
  // y is not bound, so it IS replaced in the body
  REQUIRE(result_body.operands()[1] == replacement);
}

TEST_CASE(
  "Forall expression hides bound variable",
  "[core][util][replace_symbol]")
{
  const typet t{"some_type"};
  const symbol_exprt x{"x", t};
  const symbol_exprt y{"y", t};
  const constant_exprt replacement{"val", t};

  // forall x. x == y
  const equal_exprt body{x, y};
  const forall_exprt forall{x, body};

  replace_symbolt r;
  r.insert(x, replacement);
  r.insert(y, replacement);

  exprt result = forall;
  REQUIRE(!r.replace(result));

  const auto &result_forall = to_quantifier_expr(result);
  // x is bound and must NOT be replaced in the body
  REQUIRE(result_forall.where().operands()[0] == x);
  // y is free and IS replaced
  REQUIRE(result_forall.where().operands()[1] == replacement);
}

TEST_CASE(
  "Let expression returns true when nothing replaced",
  "[core][util][replace_symbol]")
{
  const typet t{"some_type"};
  const symbol_exprt x{"x", t};
  const symbol_exprt y{"y", t};
  const constant_exprt replacement{"val", t};

  // let x = x in x  -- only bound variable, no free occurrences of y
  const let_exprt let{x, x, x};

  replace_symbolt r;
  r.insert(y, replacement);

  exprt result = let;
  // nothing to replace, so return value is true
  REQUIRE(r.replace(result));
}
