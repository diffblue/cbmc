// Author: Diffblue Ltd.

#include <util/optional.h>

#include <solvers/smt2_incremental/smt_index.h>
#include <testing-utils/use_catch.h>

TEST_CASE("Test smt_indext.pretty is accessible.", "[core][smt2_incremental]")
{
  const smt_indext index = smt_numeral_indext{42};
  REQUIRE_FALSE(index.pretty().empty());
}

TEST_CASE("Test smt_index getters", "[core][smt2_incremental]")
{
  SECTION("Numeral")
  {
    REQUIRE(smt_numeral_indext{42}.value() == 42);
  }
  SECTION("Symbol")
  {
    REQUIRE(smt_symbol_indext{"foo"}.identifier() == "foo");
  }
}

TEST_CASE("Visiting smt_indext", "[core][smt2_incremental]")
{
  class : public smt_index_const_downcast_visitort
  {
  public:
    optionalt<std::size_t> numeral_visited{};
    optionalt<irep_idt> symbol_visited{};

    void visit(const smt_numeral_indext &numeral) override
    {
      numeral_visited = numeral.value();
    }

    void visit(const smt_symbol_indext &symbol) override
    {
      symbol_visited = symbol.identifier();
    }
  } visitor;
  SECTION("numeral")
  {
    smt_numeral_indext{8}.accept(visitor);
    REQUIRE(visitor.numeral_visited);
    CHECK(*visitor.numeral_visited == 8);
    CHECK_FALSE(visitor.symbol_visited);
  }
  SECTION("symbol")
  {
    smt_symbol_indext{"bar"}.accept(visitor);
    CHECK_FALSE(visitor.numeral_visited);
    REQUIRE(visitor.symbol_visited);
    CHECK(*visitor.symbol_visited == "bar");
  }
}

TEST_CASE("smt_index equality", "[core][smt2_incremental]")
{
  const smt_symbol_indext foo_index{"foo"};
  CHECK(foo_index == smt_symbol_indext{"foo"});
  CHECK(foo_index != smt_symbol_indext{"bar"});
  const smt_numeral_indext index_42{42};
  CHECK(index_42 == smt_numeral_indext{42});
  CHECK(index_42 != smt_numeral_indext{12});
  CHECK(index_42 != foo_index);
}
