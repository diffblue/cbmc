// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_sorts.h>

TEST_CASE("Test smt_sortt.pretty is accessible.", "[core][smt2_incremental]")
{
  const smt_sortt bool_sort = smt_bool_sortt{};
  REQUIRE(bool_sort.pretty(0, 0) == "smt_bool_sort");
}

TEST_CASE(
  "Test smt_bit_vec_sortt bit width invariant",
  "[core][smt2_incremental]")
{
  const cbmc_invariants_should_throwt invariants_throw_during_test;
  REQUIRE_THROWS(smt_bit_vector_sortt{0});
}

TEST_CASE(
  "Test smt_bit_vec_sortt bit_width getter.",
  "[core][smt2_incremental]")
{
  REQUIRE(smt_bit_vector_sortt{32}.bit_width() == 32);
}

TEST_CASE("Visiting smt_bool_sortt.", "[core][smt2_incremental]")
{
  class : public smt_sort_const_downcast_visitort
  {
  public:
    bool bool_visited = false;
    bool bit_vec_visited = false;
    bool array_visited = false;

    void visit(const smt_bool_sortt &) override
    {
      bool_visited = true;
    }

    void visit(const smt_bit_vector_sortt &) override
    {
      bit_vec_visited = true;
    }

    void visit(const smt_array_sortt &) override
    {
      array_visited = true;
    }
  } visitor;
  smt_bool_sortt{}.accept(visitor);
  REQUIRE(visitor.bool_visited);
  REQUIRE_FALSE(visitor.bit_vec_visited);
  REQUIRE_FALSE(visitor.array_visited);
}

TEST_CASE("Visiting smt_bit_vec_sortt.", "[core][smt2_incremental]")
{
  class : public smt_sort_const_downcast_visitort
  {
  public:
    bool bool_visited = false;
    bool bit_vec_visited = false;
    bool array_visited = false;

    void visit(const smt_bool_sortt &) override
    {
      bool_visited = true;
    }

    void visit(const smt_bit_vector_sortt &bit_vec) override
    {
      bit_vec_visited = true;
      REQUIRE(bit_vec.bit_width() == 8);
    }

    void visit(const smt_array_sortt &) override
    {
      array_visited = true;
    }
  } visitor;
  smt_bit_vector_sortt{8}.accept(visitor);
  REQUIRE_FALSE(visitor.bool_visited);
  REQUIRE(visitor.bit_vec_visited);
  REQUIRE_FALSE(visitor.array_visited);
}

TEST_CASE("Visiting smt_array_sort.", "[core][smt2_incremental]")
{
  class : public smt_sort_const_downcast_visitort
  {
  public:
    bool bool_visited = false;
    bool bit_vec_visited = false;
    bool array_visited = false;

    void visit(const smt_bool_sortt &) override
    {
      bool_visited = true;
    }

    void visit(const smt_bit_vector_sortt &bit_vec) override
    {
      bit_vec_visited = true;
    }

    void visit(const smt_array_sortt &) override
    {
      array_visited = true;
    }
  } visitor, visitor_second;

  smt_array_sortt{smt_bool_sortt{}, smt_bool_sortt{}}.accept(visitor);
  REQUIRE_FALSE(visitor.bool_visited);
  REQUIRE_FALSE(visitor.bit_vec_visited);
  REQUIRE(visitor.array_visited);

  smt_array_sortt{smt_bit_vector_sortt{64}, smt_bit_vector_sortt{32}}.accept(
    visitor_second);
  REQUIRE_FALSE(visitor_second.bool_visited);
  REQUIRE_FALSE(visitor_second.bit_vec_visited);
  REQUIRE(visitor_second.array_visited);
}

TEST_CASE("smt_sortt equality", "[core][smt2_incremental]")
{
  const smt_bool_sortt bool_sort1;
  CHECK(bool_sort1 == bool_sort1);
  const smt_bool_sortt bool_sort2;
  CHECK(bool_sort1 == bool_sort2);
  const smt_bit_vector_sortt bit_vector8{8};
  CHECK(bit_vector8 == bit_vector8);
  CHECK(bit_vector8 != bool_sort1);
  const smt_bit_vector_sortt bit_vector16{16};
  CHECK(bit_vector8 != bit_vector16);
  const smt_array_sortt array_sort{smt_bool_sortt{}, smt_bool_sortt{}};
  CHECK(array_sort != bool_sort1);
  CHECK(array_sort != bit_vector8);
  const smt_array_sortt array_sort2{smt_bool_sortt{}, smt_bool_sortt{}};
  CHECK(array_sort == array_sort2);
  const smt_array_sortt array_sort_bv{bit_vector16, bit_vector16};
  CHECK(array_sort_bv != array_sort);
  const smt_array_sortt array_sort_bv2{bit_vector16, bit_vector16};
  CHECK(array_sort_bv2 == array_sort_bv);
}

TEST_CASE(
  "Test smt_array_sort get_index_sort getter.",
  "[core][smt2_incremental]")
{
  const smt_array_sortt array_sort{smt_bool_sortt{}, smt_bool_sortt{}};
  REQUIRE(smt_bool_sortt{} == array_sort.index_sort());

  const smt_array_sortt array_sort2{smt_bit_vector_sortt{16}, smt_bool_sortt{}};
  REQUIRE(smt_bit_vector_sortt{16} == array_sort2.index_sort());
}

TEST_CASE(
  "Test smt_array_sort get_element_sort getter.",
  "[core][smt2_incremental]")
{
  const smt_array_sortt array_sort{smt_bool_sortt{}, smt_bool_sortt{}};
  REQUIRE(smt_bool_sortt{} == array_sort.element_sort());

  const smt_array_sortt array_sort2{
    smt_bit_vector_sortt{16}, smt_bit_vector_sortt{64}};
  REQUIRE(smt_bit_vector_sortt{64} == array_sort2.element_sort());
}
