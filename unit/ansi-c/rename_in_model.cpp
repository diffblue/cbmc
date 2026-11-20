/*******************************************************************\

Module: Unit tests for rename_in_model

Author: Michael Tautschnig

\*******************************************************************/

#include <ansi-c/cprover_library.h>
#include <testing-utils/use_catch.h>

TEST_CASE("rename_in_model", "[core][ansi-c][cprover_library]")
{
  SECTION("Only whole words are renamed")
  {
    REQUIRE(
      rename_in_model(
        "double sqrt(double d) { return fast_sqrt(d) + sqrtl(d); }",
        "sqrt",
        "__builtin_sqrt") ==
      "double __builtin_sqrt(double d) "
      "{ return fast_sqrt(d) + sqrtl(d); }\n");
    REQUIRE(rename_in_model("sqrt", "sqrt", "x") == "x\n");
    REQUIRE(rename_in_model("sqrt1 _sqrt", "sqrt", "x") == "sqrt1 _sqrt\n");
  }

  SECTION("#include lines are kept")
  {
    const std::string model =
      "#include <time.h>\n"
      "  #  include <time.h>\n"
      "#undef time\n"
      "time_t time(time_t *t);\n";
    REQUIRE(
      rename_in_model(model, "time", "__builtin_time") ==
      "#include <time.h>\n"
      "  #  include <time.h>\n"
      "#undef __builtin_time\n"
      "time_t __builtin_time(time_t *t);\n");
  }

  SECTION("String and character literals are kept")
  {
    REQUIRE(
      rename_in_model(
        "free(p, \"double free\", '\\'', \"\\\"free\", 'free');",
        "free",
        "__builtin_free") ==
      "__builtin_free(p, \"double free\", '\\'', \"\\\"free\", 'free');\n");
    REQUIRE(
      rename_in_model("#line 1 \"<builtin-library-free>\"", "free", "x") ==
      "#line 1 \"<builtin-library-free>\"\n");
    // an unterminated literal extends to the end of the line
    REQUIRE(rename_in_model("\"free\nfree", "free", "x") == "\"free\nx\n");
  }
}
