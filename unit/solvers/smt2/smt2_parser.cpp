/*******************************************************************\

Module: Unit tests for parsing SMT 2 files

Author: Daniel Kroening

\*******************************************************************/

#include <solvers/smt2/smt2_parser.h>
#include <testing-utils/use_catch.h>

#include <sstream>

TEST_CASE("Parse simple SMT2 command", "[core][solvers][smt2_parser]")
{
  std::istringstream in("(set-logic QF_LIA)");
  smt2_parsert parser(in);
  // A well-formed command parses without throwing an smt2 error.
  REQUIRE_NOTHROW(parser.parse());
}

TEST_CASE("Parse SMT2 exit command", "[core][solvers][smt2_parser]")
{
  std::istringstream in("(exit)");
  smt2_parsert parser(in);
  parser.parse();
  REQUIRE(parser.exit);
}

TEST_CASE("Parse SMT2 declare-fun and assert", "[core][solvers][smt2_parser]")
{
  std::istringstream in(
    "(set-logic QF_LIA)\n"
    "(declare-fun x () Int)\n"
    "(assert (= x 42))\n"
    "(exit)\n");
  smt2_parsert parser(in);
  parser.parse();
  REQUIRE(parser.id_map.count("x") == 1);
}
