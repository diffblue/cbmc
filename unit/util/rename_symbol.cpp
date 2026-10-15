/*******************************************************************\

Module: Unit tests for rename_symbolt

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// rename_symbolt unit tests

#include <util/bitvector_types.h>
#include <util/rename_symbol.h>
#include <util/std_expr.h>

#include <testing-utils/use_catch.h>

TEST_CASE(
  "rename_symbolt is a no-op when its maps are empty",
  "[core][util][rename_symbol]")
{
  const rename_symbolt rename;
  REQUIRE(rename.empty());

  // Contract (see rename_symbol.h): the call returns true ("did nothing") and
  // leaves the expression untouched.
  symbol_exprt e{"foo", signedbv_typet{32}};
  const exprt before = e;
  REQUIRE(rename(e));
  REQUIRE(e == before);
}

TEST_CASE(
  "rename_symbolt renames a symbol present in the expr_map",
  "[core][util][rename_symbol]")
{
  rename_symbolt rename;
  rename.insert_expr("foo", "bar");
  REQUIRE_FALSE(rename.empty());

  // A populated map renames the matching symbol and returns false ("renamed
  // something").
  symbol_exprt e{"foo", signedbv_typet{32}};
  REQUIRE_FALSE(rename(e));
  REQUIRE(e.get_identifier() == "bar");
}
